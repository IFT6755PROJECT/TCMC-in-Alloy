open ctl[State]
//creat transition set
abstract sig Transition {
	Source: one State,
	Target: one State
}{ Source != Target
}

lone abstract sig A,B,C,D,E,F,G,H,I, J extends Transition {}
{
//#A=1
//#B<=1
//#C <=1
//#D<=1
//#E <=1
//#F <=1
//#G <=1
//#H <=1
//#I <=1
//#J =1
//#K <=1
}
fact transitionModel {
all t: Transition| t=A iff t.Source.S=Locking and t.Target.S=Waiting and t.Target.F=Delay
all t: Transition| t=B iff t.Source.S=Waiting and t.Source.F=Delay and t.Target.S=Washing and t.Target.F=Wash
all t: Transition| t=C iff t.Source.S=Washing and t.Source.F=Wash and t.Target.S= Unlocking

all t: Transition| t=D iff t.Source.S=Locking and  t.Target.S= Washing and t.Target.F=Wash
all t: Transition| t=E iff t.Source.S=Washing and t.Source.F=Wash and t.Target.S=Drying
all t: Transition| t=F iff t.Source.S=Drying and t.Target.S=Unlocking

all t: Transition| t=G iff t.Source.S=Locking and  t.Target.S= Waiting and t.Target.F=Heat
all t: Transition| t=H iff t.Source.S=Waiting and t.Source.F=Heat and  t.Target.S= Washing and t.Target.F=Heat
all t: Transition| t=I iff t.Source.S=Washing and t.Source.F=Heat and t.Target.S=Drying 

all t: Transition| t=J iff t.Source.S=Unlocking and t.Target.S=Locking
}

// The whole SPL
abstract sig Feature {}
one sig Wash, Delay, Dry, Heat extends Feature { }
abstract sig Status {}
one sig Locking, Washing, Drying, Unlocking, Waiting extends Status{ }

sig State {
  transition: some State,
  F: set Feature,
  S: one Status,
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
 // ensure that two Transition with the same features are equivalent
  all t,t' : Transition| TransitionEquality[t,t']
}

pred init [s:State]{ 
  // TODO 
  s.S= Locking and no s.F

}

pred stateConstraints [s: State] { 
  // You shouldn't need to add anything here 
s.S=Locking => no s.F
s.S=Washing=> s.F = Wash or s.F=Heat
s.S=Unlocking => no s.F
s.S=Drying => s.F = Dry
s.S=Waiting => s.F=Delay or s.F=Heat

}

pred validTransition[s,s' : State ]{
  // TODO
s.S=Locking =>  (s'.S=Waiting and s'.F=Heat)  or (s'.S=Waiting and s'.F=Delay) or (s'.S=Washing and s'.F = Wash)
s.S=Waiting  and s.F=Heat =>  s'.S=Washing and s'.F = Heat 
s.S=Waiting  and s.F=Delay=>  s'.S=Washing and s'.F = Wash 
s.S=Washing => s'.S=Drying or s'.S=Unlocking 
s.S=Drying => s'.S=Unlocking 
s.S=Unlocking => s'.S=Locking
Transition.Source = s => Transition.Target = s'

}

pred stateEquality[s,s' : State]{
  // TODO
s=s' iff (s'.S = s.S  && s'.F = s.F)
}

pred TransitionEquality[t,t' : Transition]{
  // TODO
t=t' iff (t'.Source = t.Source  && t'.Target = t.Target)
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

run showExamples { } for exactly 4 State, exactly 4 Transition

assert letsModelCheckThisFormula{
	ctl_mc[ ex[{s:State | completeThis[s]}] ]
}
pred completeThis [s:State]{
  // TODO
//liveness
s.F = Wash

}
check letsModelCheckThisFormula 


