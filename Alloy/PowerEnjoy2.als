module PowEnj

sig Position{}
sig Word{}
sig Email{}
sig Code{}
sig Date{}
sig Time{}
abstract sig State{}
sig FreeState extends State{}
sig ReservedState extends State{}
sig RentedState extends State{}
sig Number{}

sig User{
	paymentInfo: one PaymentMethod,
	name:one Word,
	surname:one Word,
	driverLicense:one DriverLicense,
	email:one Email,
	birthday:one Date
}

sig PaymentMethod{
	code:one Number,
	expiration:one Date
}{
	no p1, p2: PaymentMethod | (p1!=p2 and p1.code=p2.code)
}


sig DriverLicense{
	code:one Code,
	expirtation:one Date,
	user:one User
}{
	no d:DriverLicense| d not in d<:user.driverLicense
}

sig Reservation{
	user:one User,
	car:one Car,
	startTime: Time
}{
	no c1, c2: Reservation | (c1!=c2 and c1->Car=c2->Car and c1->startTime=c2->startTime)
}

sig Car{
	plate:one Code,
	position:Position,
	state:one State,
	battery:Number
}
{
	no c1, c2: Car | (c1!=c2 and c1->plate=c2->plate)
}

sig Rent{
	car:one Car,
	user:one User,
	startTime:Int,
	endTime:Int,
	overtaxes:Number,
	discount:Number,
	bill:Number,
	passenger:Number
}
{
	startTime>0 and startTime<endTime
}

pred show{}
run show 
