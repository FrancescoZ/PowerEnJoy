sig Coordinate{
	long : Int ,
	lat : Int
}

sig User{
	position: Coordinate,
	payment: Int ,
	name: String,
	password:String,
}

sig Car{
	position:Coordinate,
	state:String,
	battery:Int  
}

sig Area{
	position:Coordinate,
	ncar:Int ,
	nplace:Int
}
