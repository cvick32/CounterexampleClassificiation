open util/ordering[Time]
sig Time { }

one sig Gen {
  value: Int one -> Time
}

pred init (t: Time) {
	Gen.value.t = 5
}

pred change[t,t': Time] {
	Gen.value.t' != Gen.value.t
}

fact Traces {
	first.init
	all t: Time - last | let t' = t.next |
		change[t,t']
}

assert AlwaysEqualFive {
	all t: Time | 
		Gen.value.t = 5
} check AlwaysEqualFive for 8

//TODO: what happens when all <, >, and != are available?

// classification using only > and <
// these two classes cover the set of violating behavior

pred characterize_LessThan {
	some t: Time | Gen.value.t < 5
}  fact { !characterize_LessThan }

pred characterize_GreaterThan {
	some t: Time | Gen.value.t > 5	
}  fact { !characterize_GreaterThan }


// classifcation using !=
// this class covers the set of violating behavior
/**
pred characterize_NotEqual {
	some t: Time | Gen.value.t != 5
} fact { !characterize_NotEqual }
**/

// classification using isEven
/*
pred isEven[i: Int] {
	rem[i, 2] = 0
}

pred characterize_even {
	some t: Time | isEven[Gen.value.t]
} fact { !characterize_even }


if we allow this, it covers the counterexamples, we could disallow the negation operator
pred characterize_odd {
	some t: Time | !isEven[Gen.value.t]   
} fact { !characterize_odd }
*/

