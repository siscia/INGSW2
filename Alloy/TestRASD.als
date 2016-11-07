enum carBookStatus {booked, inUse, free}
enum engineStatus {on, off}
enum doorStatus {opened, closed}
enum lockStatus {lock, unlock}

sig Car{
	carStatus:  one carBookStatus,
	engine: one engineStatus,
	door: one doorStatus,
	padlock: one lockStatus,
}
{
	// no car with the engine on and the door open
	no op: opened, o: on | op in door and o in engine
	// no free car unlocked
	no ul: unlock, fr: free | ul in padlock and fr in carStatus
	// no free car with door open
	no op: opened, fr: free | op in door and fr in carStatus
	// no car in use locked
	no l: lock, use: inUse | l in padlock and use in carStatus
	// no engines on if the car is not in use
	no o: on, use: inUse | o in engine and use not in carStatus
	// no two user with the same car
	no u, u': User | this in u.car and this in u'.car and u != u'
	// open car implies car unlock
	all od: opened, un: unlock | od in door => un in padlock
	// locked car implies car locked
	all cl: closed, l: lock | l in padlock => cl in door
}

sig User{
	position: one Position,
	car: lone Car
}
{
	no c: Car, fr: free | c = car and fr in c.carStatus
	no c: Car, p: Position | position = p and c not in p.nearby
}

fact onlyFreeCarDontHaveUser {
	all fr: free, u: User, c: Car | fr in c.carStatus <=> c not in u.car
}

sig Position {
	nearby: set Car,
	bookable: set Car
}
{
	// bookable car must be nearby
	no c: Car | c in bookable and c not in nearby
}

/*
fact NearbyIsTransitive{
	no c, c': Car, p, p' : Position | c != c' and p != p' and 
		c in p.nearby and c' in p.nearby and c in p'.nearby and c' not in p'.nearby
}
*/

fact allFreeCarAreBookable{
	all c: Car, p: Position | c.carStatus = free and c in p.nearby <=> c in p.bookable
}

fact bookedCarAreNotBookable{
	all c: Car, p: Position | c.carStatus = booked and c in p.nearby <=> c not in p.bookable
}

fact inUseCarAreNotBookable{
	all c: Car, p: Position | c.carStatus = inUse and c in p.nearby <=> c not in p.bookable
}

/*
pred BookableCar[p: Position, c: Car]{
	c in p.bookable
}

pred BookACar[p: Position, c, c': Car, u, u': User]{
	BookableCar[p, c] and
	u.position = u'.position and
	u.car = none and
	u'.car = c' and
	not BookableCar[p, c']
}
*/
pred show(){
	#Car = 3 and #User = 0 and #Position = 10
}

run show for 10 Car, 10 User, 10 Position
