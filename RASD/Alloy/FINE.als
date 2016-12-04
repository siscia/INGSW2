enum Fine {Fined, NotFined}

sig User {}

sig Ride {
	fine: one Fine,
	user: one User
}

pred show{}

assert NoFineWithoutResponsableUser {
	no r: Ride | r.fine = Fined and no r.user	
}

check NoFineWithoutResponsableUser for 100
