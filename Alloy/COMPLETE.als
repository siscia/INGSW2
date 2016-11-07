enum CarStatues {Available, Booked, Unlocked, Riding}

sig User {
	car: lone Car
}

sig Car {
	status: one CarStatues
}

sig Ride {
	user: one User,
	car: one Car
}

fact CarCanBeBookedOnlyByUser{
	all c: Car, b: Booked | some u: User | b in c.status <=> c in u.car
}

fact AvailableCarDontHaveUser {
	no c: Car, a: Available, u: User | a in c.status and c in u.car
}

fact CarCanBeBookedOnlyByASingleUser {
	no c: Car, b: Booked, u, u': User | b in c.status and u != u' and c in u.car and c in u'.car
}

fact OnlyOneRideForOneCar {
	no c: Car, r, r': Ride | r != r' and r.car = c and r'.car = c 
}

fact RideOnlyWithRidingCar {
	no c: Car, r: Ride | r.car = c and c.status != Riding
}

fact NoRidingCarWithoutRide {
	all c: Car |some r: Ride | c.status = Riding <=> c in r.car
}

fact RidingWithTheSameCarUsedByTheUser {
	no r: Ride, c: Car, u: User | r.car = c and r.user = u and u.car != c
}

fact CarCanBeRidenOnlyByAnUser {
	no r: Ride, c: Car, u, u': User | u != u' and Riding = c.status and u = r.user and c = r.car and c = u'.car 
}

pred UserCanBookAvailableCar[c, c': Car, b: Booked, a: Available, u, u': User] {
	(c != c')
	(u != u')

	a in c.status
	c not in u.car

	b in c'.status
	c' in u'.car
}

pred show{}

run show for 4
