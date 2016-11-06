sig License{}
sig Credential{}

sig User {
	drivingLicense: one License,
	credential: lone Credential
}

fact oneLicenseForUser {
	no l: License, u, u': User | u != u' and l in u.drivingLicense and l in u'.drivingLicense
}

fact credentialsArePersonally {
	no c: Credential, u, u': User | u != u' and c in u.credential and c in u'.credential
}

sig System {
	users: set User
}

fact userInASystemHaveCredential {
	all u: User | some s: System | one c: Credential | u in s.users <=> c in u.credential
}

//the user is able to register
pred Registration[u, u': User, s, s': System] {
	#System = 2
	#User = 2
	(s != s')
	(u != u')

	// the user is not registered
	(u' not in s.users)

	// the user is now in the system
	(u' in s'.users)
	(s'.users = s.users + u')
}

pred show[]{
	#System = 2
	#User > 2
}

run show for 4
