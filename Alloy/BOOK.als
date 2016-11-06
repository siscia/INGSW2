enum statues {Available, Booked}

sig User {
	car: lone Car
}

sig Car {
	status: one statues
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

pred UserCanBookAvailableCar[c, c': Car, b: Booked, a: Available, u, u': User] {
	(c != c')
	(u != u')

	a in c.status
	c not in u.car

	b in c'.status
	c' in u'.car
}

run UserCanBookAvailableCar for 4
