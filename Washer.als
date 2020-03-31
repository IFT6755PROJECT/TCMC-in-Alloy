open ctlfc[State]

//State of Wash


sig State {
	features: set Name,
	//root: features,
	relations: set Relation,
	forms: set Formula
	}

pred initial[s:State]{
	s.features = Washer
}
//sig Name{}
abstract sig Type {}

one sig Optional, Mandatory, OrFeature,Alternative extends Type {}

sig Relation {
	parent: Name,
	child: set Name,
	type: Type
	}

abstract sig Formula {
	satisfy: Configuration -> one Bool,
	wt: State -> one Bool
	}

sig NameF extends Formula {
	n: Name
	}

sig Form extends Formula {
	f: Formula,
	g: Formula,
	op: Op
}

abstract sig Op {}

one sig AndF, OrF, ImpliesF, NotF extends Op {}



//**********************//


abstract sig Name{}

one sig Wash, Heat, Delay, Dry extends Name {}

one sig fm1 extends State {}

one sig r1, r2, r3 extends Relation {}

one sig f1,f4 extends Form {}


fact elements {
	//fm1.root = Wash
	fm1.features = Wash+Heat+Delay+Dry
	fm1.relations = r1+r2+r3
	fm1.forms = f1+f4
	}


fact relations {
	r1.type = Optional
	r1.parent = Wash
	r1.child = Delay

	r2.type = Optional
	r2.parent = Wash
	r2.child = Dry

	r3.type = Optional
	r3.parent = Wash
	r3.child = Heat

	}

one sig f2,f3 extends NameF {}

fact formulas {
	f1.op = ImpliesF
	f1.f = f2
	f1.g = f3
	f2.n = Delay
	f3.n = Heat
	f4.op = ImpliesF
	f4.f = f3
	f4.g = f2
}



