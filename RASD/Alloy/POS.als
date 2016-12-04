open util/integer as integer

sig Casher{}

sig POSTerminal {
	casher: one Casher
}

sig Product {
	price: Int 
}

sig Bill {
	products: set Product,
	total:  Int
}{
	sum products.price = total
}

pred addElement(casher: Casher, POS: POSTerminal, p: Product, b, b': Bill){
	POS.casher = casher

	b'.products = b.product + p
	b'total = b.total + p.price
}
