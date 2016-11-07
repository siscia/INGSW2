enum status {booked, unlock}

sig User {
	car: one Car,
	nearby: set car
}

sig Car {
	status: one status
}

pred unlockCar[c, c': Car, u, u': User] {
	c in unlockableCar[u]
	c'.status = unlock
	c' in u'.car
	c' in u'.nearby
}

fun unlockableCar[u: User]: Car {
	{c: Car | c in u.nearby and c in u.car and booked in c.status}
}

pred show{}

//run unlockableCar for 3
run unlockCar for 4
run show for 4
