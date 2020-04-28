open ctl[State]

// 2. Locking -> waiting -> washing -> unlocking
abstract sig Feature {}
one sig Wash, Delay extends Feature { }
abstract sig Status {}
one sig Locking, Washing, Waiting, Unlocking extends Status{ }

sig State {
  transition: some State,
  F: set Feature,
  S: one Status
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
    validTransition[s,s']
  // ensure that two states with the same features are equivalent
  all s,s':State| stateEquality[s,s']
}

pred init [s:State]{ 
  // TODO 
  s.S= Locking and no s.F

}

pred stateConstraints [s: State] { 
  // You shouldn't need to add anything here 
s.S=Locking => no s.F
s.S=Washing=> s.F = Wash
s.S=Unlocking => no s.F
s.S=Waiting => s.F = Delay
//no a: Status | a in ^(s.S.a)
}

pred validTransition[s,s' : State ]{
  // TODO
s.S=Locking => s'.S=Waiting 
s.S=Waiting => s'.S=Washing 
s.S=Washing => s'.S=Unlocking 
s.S=Unlocking => s'.S=Locking

}

pred stateEquality[s,s' : State]{
  // TODO
s=s' iff (s'.S = s.S  && s'.F = s.F)
}

fact modelWellMappedToCTLModule{
  initialStateAxiom
  totalityAxiom
}
pred initialStateAxiom {
	some s: State | s in initialState
}
pred totalityAxiom {
  all s: State |all s':State |
    s->s' in nextState iff s' in s.transition
}

run showExamples { } for exactly 4 State
//for exactly 2 State, exactly 4 Symbol, exactly 2 Component, exactly 1 Delegation, exactly 1 Diagrams

assert letsModelCheckThisFormula{
	ctl_mc[ ex[{s:State | completeThis[s]}] ]
}
pred completeThis [s:State]{
  // TODO
//liveness
s.F = Wash

}
check letsModelCheckThisFormula 

