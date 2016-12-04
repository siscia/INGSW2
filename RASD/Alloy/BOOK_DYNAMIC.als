enum CarStatus {Available, Booked, Unlocked, Riding, NotAvailable}

sig User {
	car: lone Car,
	nearby: set Car,
}

sig Car {
	status: one CarStatus
}

fact IfAnUserIsAssociateWIthACarNoOneElseIs {
	no u, u': User | some c: Car | u != u' and c = u.car and c = u'.car
}

fact ABookedCarIsAssociatedWithAnUser {
	all c: Car | some u: User | c.status = Booked <=> c in u.car
}

fact AnUnlockedCarIsAssociatedWithAnUser {
	all c: Car | some u: User | c.status = Unlocked <=> c in u.car
}

fact AnUnlockedCarHasIsUserNearby {
	no c: Car, u: User | c.status = Unlocked and c in u.car and c not in u.nearby
}

fact AnAvailableCarIsAssociatedWithNoUser {
	no c: Car, u: User | c.status = Available and c in u.car
}

fact AnNotAvailableCarIsAssociatedWithNoUser {
	no c: Car, u: User | c.status = NotAvailable and c in u.car
}

fun BookableCar[]: Car {
	{c : Car | c.status = Available}
}

fun UnlockableCar[u: User]: Car {
	{c: Car | c.status = Booked and c in u.car and c in u.nearby}
}

pred PossibleToBookACar[c, c': Car, u, u': User] {
	c != c'
	u != u'
	c in BookableCar
	no u.car

	c'.status = Booked
	u'.car = c'
	u.nearby = u'.nearby
	c not in u.nearby <=> c' not in u'.nearby
}

pred PossibleToUnlockACar[c, c': Car, u, u': User] {
	c != c'
	u != u'
	c in UnlockableCar[u]
	c in u.car

	c'.status = Unlocked
	u'.car = c'
	u.nearby = u'.nearby
	c not in u.nearby <=> c' not in u'.nearby
}

assert UnlockedCarHaveTheirUserNearby {
	no u: User | some c: Car | c.status = Unlocked and c not in u.nearby and u.car = c
}

pred PossibleToRideACar[c, c': Car, u, u': User]{
	c != c'
	u != u'
	c.status = Unlocked
	c in u.car
	
	c'.status = Riding
	u'.car = c'
	c' in u'.nearby
	u.nearby = u'.nearby
	c not in u.nearby <=> c' not in u'.nearby
}

pred PossibleToReleaseACar[c, c': Car, u, u': User]{
	c != c'
	u != u'
	c.status = Riding
	c in u.car
	c in u.nearby
	
	c'.status = Available
	no u'.car
	c' in u'.nearby
	u.nearby = u'.nearby
	c not in u.nearby <=> c' not in u'.nearby
}

pred PossibleToBookUnlockRideACar[c, c', c'', c''': Car, u, u', u'', u''': User] {
	PossibleToBookACar[c, c', u, u']
	PossibleToUnlockACar[c', c'', u', u'']
	PossibleToRideACar[c'', c''', u'', u''']
}

pred PossibleWholeCycle[c, c', c'', c''', c'''': Car, u, u', u'', u''', u'''': User] {
	PossibleToBookACar[c, c', u, u']
	PossibleToUnlockACar[c', c'', u', u'']
	PossibleToRideACar[c'', c''', u'', u''']
	PossibleToReleaseACar[c''', c'''', u''', u'''']
}

pred show{}

run show for 5
run PossibleToBookACar for 5
run PossibleToUnlockACar for 5
run PossibleToRideACar for 5
check UnlockedCarHaveTheirUserNearby for 10
run PossibleToBookUnlockRideACar for 4
run PossibleToReleaseACar for 5
run PossibleWholeCycle for 5
	
