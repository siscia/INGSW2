enum CarStatus {Booked, Riding, NotAvailable}
enum ParkingStatus {Safe, Unsafe}

sig Staff {
	carToMove: set Car
}

sig Car{
	status: one CarStatus,
	parkingStatus: lone ParkingStatus
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

pred show{}

run show for 4
