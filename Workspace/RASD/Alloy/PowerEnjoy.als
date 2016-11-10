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
	applyOvertax>=0
	applyDiscount>=0
}


abstract sig Station{
	parkedCar:set Car,
	positoin:one Position
}

sig  Parking extends Station{
	distanceFromCharge:Int
}{
	distanceFromCharge>0
}


sig SafeArea extends Station
{
	pluggedCar: set Car,
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

	//No PaymentMethod with the same code
	all p1,p2:PaymentMethod| p1!=p2 implies p1.code!=p2.code
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
	all car:Car,s:Station| car.position=s.position and car.state=FreeState implies car in s.parkedCar
	
	//If a car is plugged is also parked
	all s:SafeArea,car:Car|car in s.pluggedCar implies car in s.parkedCar   

	//the user get a discount parking and plugging the car
	all car:Car,s:SafeArea,r1,r2:Rent| car in s.parkedCar and car in s.pluggedCar implies r1.applyDiscount=30
	
	//Safe area overtax
	all car:Car,p:Parking, r1,r2:Rent | car in p.parkedCar and p.distanceFromCharge>3 implies r1.applyDiscount=0 and r1.applyOvertax=30
	
	all car:Car| car.state=FreeState implies car in Station.parkedCar
	
	no s:SafeArea| #s.pluggedCar>#s.parkedCar

	//Overtaxes are 0 or 30
	all rent:Rent| rent.applyOvertax=0 or rent.applyOvertax=30

	//the bill is calculate only if the rent is finish
	all rent:Rent| rent.applyOvertax>0 or rent.applyDiscount>0 implies rent.endRent=True
}

//ASSUMPTION

//A car can be reused after a rent
assert CarReused{
	all r1,r2:Rent| r1.endRent=True and r2.endRent=False and r1.reservation.car= r2.reservation.car implies r2.startTime>r1.endTime
}

//There are as many driver license as users
assert DriverForEachDocument{
	#DriverLicense = #User
	#User=#Email
}

assert UserPaymentMethod{
	#User.payInfo<=#PaymentMethod
}

//The rent with taxes can't have a discount
assert RentOverTaxes{
	all rent:Rent| rent.applyOvertax>0 implies rent.applyDiscount<rent.applyOvertax
}

//the plugged car can't be in use
assert PluggedCar{
	all rent:Rent| rent.reservation.car in SafeArea.pluggedCar implies !rent.endRent=False
}

check PluggedCar

check RentOverTaxes

check UserPaymentMethod

check CarReused for 5

check DriverForEachDocument for 5


pred SimpleWorld
{
	#User <3
	#Car < 4
	#Station< 4
	#Reservation < 4
	#Rent <3
}

pred RealWorld
{
	#User > 2
	#Car > 3
	#SafeArea> 1
	#Parking > 2
	#Reservation > 2
	#Rent > 1
}

run SimpleWorld for 6

run RealWorld for 6
