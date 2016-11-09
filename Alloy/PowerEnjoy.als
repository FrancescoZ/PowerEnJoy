module PowEnj 
//SIGNATURES
sig Position{}
sig Email{}
sig Code{}

sig Plug{}

abstract sig Bool{}
sig False extends Bool{}
sig True extends Bool{}

abstract sig State{}
sig FreeState extends State{}
sig ReservedState extends State{}
sig RentedState extends State{}

sig DriverLicense{
	code:one Code,
	expiration:Int
}
{ 
	expiration>0
}


sig User
{
	payInfo: some PaymentMethod,
	position: one Position,
	license: one DriverLicense,
	email:one Email
}

sig Reservation{
	user:one User,
	time:Int,
	endTime:Int,
	car:one Car
}
{
	time>0
	endTime>time
}

sig Rent
{
	startTime: one  Int,
	endTime:one Int,
	endRent:one Bool,
	applyDiscount:one Int,
	applyOvertax:one Int, 
	totalCost:Int,
	passengers:one  Int,
	reservation:one Reservation,
	payment:one PaymentMethod
}{
	passengers>=0
	startTime>0
	endTime>startTime
}


abstract sig Station{
	parkedCar:set Car,
	positoin:one Position
}

sig  Parking extends Station{
	distanceFromCharge:Int
}

sig SafeArea extends Station
{
	carsToCharge: set Car,
	plugAvailable: set Plug,
}


sig PaymentMethod
{
	transactionCode: one Code
}

sig Car
{
	position:one Position,
	battery: Int,
	plate: one Code,
	state:one State,
	readyToEnd:one Bool
}{
	battery>=0 and battery<=100
}

//FACT

fact{
	//No useless paymentMethod
	User.payInfo=PaymentMethod
	//No useless Plug
	SafeArea.plugAvailable=Plug
	//No useless Email
	User.email=Email
	//No useless Position
	Car.position+User.position=Position
	//No useless Code
	Car.plate+PaymentMethod.transactionCode+DriverLicense.code=Code
	//No useless State
	Car.state=State
	//No useless Bool
	Rent.endRent=Bool
	//No useless License
	User.license=DriverLicense

	//No car with the same plate
	all c1, c2: Car | c1!=c2 implies c1.plate!=c2.plate
	//No users with same email
	all u1,u2:User| u1!=u2 implies u1.email!=u2.email
	//No users with same license
	all u1,u2:User| u1!=u2 implies u1.license!=u2.license

	//No reservation for the same car in a time<1
	all r1,r2:Reservation | (r1!=r2 and r1.car=r2.car) implies (r1.time>r2.time+1 or r2.time>r1.time+1)

	//If a car is reserved is in reserved state
	all r:Reservation,c:Car,rent:Rent|  (r.car=c and  !(rent.endRent=False and rent.reservation.car=c)) implies c.state=ReservedState
	
	//if a car is in use is in rentedState
	all c:Car,r:Rent| r.reservation.car=c and r.endRent=False implies c.state=RentedState
	
	//if a car is not rented or reserved is in free state and a reservation keep going for max 1 hour
	all c:Car,rent:Rent,res:Reservation| 
		//if the car is not reserved
		((res.car!=c 
			or
				//or the reservation is expired
				(res.car=c and res.endTime>res.time+1)) 
		and 
			//and there is no rent on the car
			(rent.reservation.car!=c 
				or
					//or the rent is finished
					(rent.endRent=True and rent.reservation.car=c))) implies c.state=FreeState
	
	//A rent can be done only after a reservation
	all rent:Rent,res:Reservation| rent.reservation=res implies rent.startTime>res.time and rent.startTime<=res.time+1

	//Two different rent can't have the same reservation
	all r1,r2:Rent| r1!=r2 implies r1.reservation!=r2.reservation

	//There is just one rent not finish for each car
	all r1,r2:Rent|r1.endRent=False and r2.reservation.car=r1.reservation.car implies !(r2.endRent=False)
	
	//A rent can end only in a station
	all rent:Rent,c:Car,s:Station|rent.reservation.car=c and c.readyToEnd=True implies c.position=s.position
	
	//A rent has been concluded only in a station
	all rent:Rent,s:Station|rent.endRent=True implies rent.reservation.car.position=s.position	

	//Discount for battery state applyed only if the rent in ended and the battery state is >50
	all rent:Rent| rent.reservation.car.battery>50 and rent.endRent=True implies rent.applyDiscount=20
	
	//Discount for passengers is applyed only if the rent is finished and more than 2 passengers were found
	all rent:Rent| rent.passengers>2 and rent.endRent=True implies rent.applyDiscount=20
	
	//All the cars parked are free
	all car:Car,s:Station| car.position=s.position and car.state=FreeState implies car in Station.parkedCar
	//Safe area discount
	//Safe area overtax
	//Non ti puoi essere in carica o parcheggiato in una safe area se hai un rent
}

//ASSUMPTION

//A car can be reused after a rent
assert CarReused{
	all r1,r2:Rent| r1.endRent=True and r2.endRent=False and r1.reservation.car= r2.reservation.car implies r2.startTime>r1.endTime
}

assert RentOnlyAvaibleCar{
	some rent:Rent|rent.reservation.car.state=FreeState or rent.reservation.car.state=ReservedState  implies rent.endRent=False
}

//There are as many driver license as users
assert DriverForEachDocument{
	#DriverLicense = #User
	#User=#Email
}

assert UserPaymentMethod{
	#User.payInfo<=#PaymentMethod
}

check UserPaymentMethod

check CarReused for 5

check RentOnlyAvaibleCar for 5

check DriverForEachDocument for 5

