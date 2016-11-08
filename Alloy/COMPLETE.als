enum CarStatues {Available, Booked, Unlocked, Riding, NotAvailable}
enum ParkingStatus {Safe, Unsafe}
enum TotNumPeople {lessThan3, moreThan3}
enum BatteryLevel {moreThan50, lessThan50, lessThan20}
enum PlugStatus {plugged, unplugged}
enum Bonuses {less10, less20, less30, plus30}
enum Distance {less3KM, more3KM}
enum Fine {Fined, NotFined}
enum FineSituation {NoFinePending, FinePending}

sig Staff {
	carToMove: set Car
}

sig License {}

sig User {
	car: lone Car,
	license: one License,
	nearby: set Car,
	fineSituation: one FineSituation
}

fact NoActionWithAFinePending {
	no u: User | u.fineSituation = FinePending and not no u.car
}

fact licenseIsPersonal {
	no u, u': User, l: License | u != u' and l in u.license and l in u'.license 
}

fact OnlyCarRidingDontHaveAParkingStatus {
	all c: Car | c.status = Riding <=> no c.parkingStatus
}

fact CarUnsafelyParkedAreOnListToBeMoved {
	all c: Car, s: Staff | c.parkingStatus = Unsafe <=> c in s.carToMove
}

fact CarUnsafelyParkedAreNotAvailable {
	all c: Car | c.parkingStatus = Unsafe <=> c.status = NotAvailable
}

sig Car {
	status: one CarStatues,
	parkingStatus: lone ParkingStatus
}

sig Ride {
	user: one User,
	car: one Car,
	scannedLicense: one License,
	totNumPeople: one TotNumPeople,
	batteryLevel: one BatteryLevel,
	plugStatus: one PlugStatus,
	distance: one Distance,
	bonuses: set Bonuses,
	fine: one Fine
}

assert NoFineWithoutResponsableUser {
	no r: Ride | r.fine = Fined and no r.user	
}

fact ABookedCarIsAssociatedWithAnUser {
	all c: Car | some u: User | c.status = Booked <=> c in u.car
}

fact AnUnlockedCarIsAssociatedWithAnUser {
	all c: Car | some u: User | c.status = Unlocked <=> c in u.car
}

fact AnAvailableCarIsAssociatedWithNoUser {
	no c: Car, u: User | c.status = Available and c in u.car
}

fact RideOnlyIfTheScannedLicenseIsTheSameOfTheUser {
	no r: Ride, u: User, l: License |  r.user = u and u.license = l and r.scannedLicense != l
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
	all c: Car | some r: Ride | c.status = Riding <=> c in r.car
}

fact RidingWithTheSameCarUsedByTheUser {
	no r: Ride, c: Car, u: User | r.car = c and r.user = u and u.car != c
}

fact CarCanBeRidenOnlyByAnUser {
	no r: Ride, c: Car, u, u': User | u != u' and Riding = c.status and u = r.user and c = r.car and c = u'.car 
}

fact UnlockedCarHasIsUserNearby {
	all c: Car | some u: User | Unlocked = c.status <=> (c in u.nearby and u.car = c)
}

fact RidingCarHasIsUserNearby {
	all c: Car | some u: User | Riding = c.status <=> (c in u.nearby and u.car = c)
}

pred UserCanBookAvailableCar[c, c': Car, b: Booked, a: Available, u, u': User] {
	(c != c')
	(u != u')

	a in c.status
	c not in u.car

	b in c'.status
	c' in u'.car
}

fact discountNumPeople {
	all r: Ride | moreThan3 = r.totNumPeople <=> less10 in r.bonuses
}

fact discountBatterLevel {
	all r: Ride | moreThan50 = r.batteryLevel <=> less20 in r.bonuses 
}

fact discountPluggedCar {
	all r: Ride | plugged = r.plugStatus <=> less30 in r.bonuses
}

fact overchargeUnloadFarAway {
	all r: Ride | lessThan20 = r.batteryLevel and more3KM = r.distance <=> plus30 in r.bonuses
}

pred show{
	#Ride > 3
	some u: User | u.fineSituation = FinePending
}

assert UserWithFinePendingCantBookUnlockRideCars {
	no u: User, c: Car | u.fineSituation = FinePending and u.car = c and 
		(c.status = Booked or c.status = Unlocked or c.status = Riding)
}

check UserWithFinePendingCantBookUnlockRideCars for 10
check NoFineWithoutResponsableUser for 5
run show for 5
