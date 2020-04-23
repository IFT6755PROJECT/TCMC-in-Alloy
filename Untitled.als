open ctl[State]

abstract  sig wash {}
one sig dry, heat, delay extends wash{}

abstract sig status{}
one sig locking, waiting, washing, drying, unlocking, end extends status{}

sig State {
  transition: some State,
  Wash:  wash,
  Status: status
}

fact modelDefinition {
  // constraints on states (State)
  all s:State | stateConstraints[s]
  // init state constraints
  // the function initialState is defined in the CTL module
  all s:State | s in initialState iff init[s]
  // only defined transitions are valid 
  // the function nextState is defined in the CTL module
  all s,s':State| s->s' in nextState iff 
    startPrewash[s,s']  or  endPrewash[s,s'] or
	startDrying[s,s'] or endDrying[s,s'] or endLoop[s, s']
}
  // ensure that two states with the same features are equivalent
  all s,s':State| stateEquality[s,s']
}

pred init [s:State]{ 
  // TODO 
	s.Status = locking
	//s.request = TRUE
	//no s.transation
}

pred stateConstraints [s: State] { 
  // You shouldn't need to add anything here for the two-bit counter
	not (s.Wash = delay and s.Wash = dry)

}

pred startPrewash[s, s':State]{
s.Status = locking implies (s'.Status=waiting and s'.Wash = delay) 
	or  (s'.Status=waiting and s'.Wash = heat) 
}

pred endPrewash[s, s':State]{
	(s'.Status=washing and s'.Wash = heat) iff  startPrewash[s,s']
}

pred startDrying[s, s':State]{
	(s'.Status = drying and s'.Wash = dry) iff endPrewash[s,s']
}
pred endDrying[s, s':State]{
	s'Status = unlocking iff startDrying[s,s']
}

pred endLoop[s, s':State]{
	s'Status = end iff (endDrying[s, s'] or endLoop[s, s'])
}

//pred validTransition[s,s' : State ]{
  // TODO
	//one s' in s.transition iff
	//s.request = TRUE implies s'.Status = busy
	//else  (s'.Status = busy or s'.Status = ready)

//}

pred stateEquality[s,s' : State]{
  // TODO
	s = s' iff s.Status=s'.Status

}

fact modelWellMappedToCTLModule{
  initialStateAxiom
  totalityAxiom
}
pred initialStateAxiom {
	some s: State | s in initialState
}
pred totalityAxiom {
  all s,s' : State |
    s->s' in nextState iff s' in s.transition
}

run showExamples { } for 5 

//assert letsModelCheckThisFormula{
//	ctl_mc[ ag[{s:State | completeThis[s]}] ]
//}
//pred completeThis [s:State]{
  // TODO
	// s.Status = TRUE
//	implies ctl_mc[af[{s : State | s.Status = busy}]]

 //s.R = _0 or s.L = _0

//}
//check letsModelCheckThisFormula for 10// should find no counterexample
//check letsModelCheckThisFormula for 4 // should find a counterexample




