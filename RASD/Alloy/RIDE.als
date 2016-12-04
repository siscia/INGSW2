enum status {unlock, running}

sig License {}

sig User {
	license: one License
}

fact licenseIsPersonal {
	no u, u': User, l: License | u != u' and l in u.license and l in u'.license 
}

sig Car {
	user: one User,
	scannedLicense: lone License,
	status: one status
}

fact unlockCarDontHaveScannedLicenseYet {
	no c: Car, l: License, u: unlock| l in c.scannedLicense and u in c.status
}

fact onlyOneUserPerCar {
	no c, c': Car, u: User | c != c' and c.user = u and c'.user = u
}

fact carStartOnlyWithTheCorrectLicenseScanned {
	no c: Car, u: User, l: License, r: running | 
		r in c.status and u in c.user and l in c.scannedLicense and l not in u.license
}

fact carWithoutScannedLicenseDontStart {
	no c: Car, r: running | r in c.status and c.scannedLicense = none
}

pred runningCarAllHaveAScannedLicenseEqualsToTheOneOfTheUser[]{
	all c: Car | c.status = running
}

pred show{}
run runningCarAllHaveAScannedLicenseEqualsToTheOneOfTheUser for 4
