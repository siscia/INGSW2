
enum TotNumPeople {lessThan3, moreThan3}
enum BatteryLevel {moreThan50, lessThan50, lessThan20}
enum PlugStatus {plugged, unplugged}
enum Bonuses {less10, less20, less30, plus30}
enum Distance {less3KM, more3KM}

sig Ride {
	totNumPeople: one TotNumPeople,
	batteryLevel: one BatteryLevel,
	plugStatus: one PlugStatus,
	distance: one Distance,
	bonuses: set Bonuses
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

pred show {}

run show for 4
