package multiparty

import (
	"testing"
)

var BoolValue = func() []Sort{
	ans := make([]Sort, 1, 1)
	ans[0]=Sort("bool")
	return ans
}()
var NatValue = func() []Sort{
	ans := make([]Sort, 1, 1)
	ans[0] = Sort("nat")
	return ans
}()


func TestUnfolding(test *testing.T){
	//example from page 5
	example_1 := RecursiveType{bind: NameType("X"),
		body: ParallelType{a: ValueType{value:nil, prefix:Prefix{P1: "A", P2: "B", channel:"s"},next:EndType{}}, b:ValueType{value:nil, prefix:Prefix{P1: "B", P2:"A", channel:"t"}, next:NameType("X")}}}

	unfold_1 := RecursiveType{bind: NameType("X"),
		body: ParallelType{a: ValueType{value:nil, prefix:Prefix{P1: "A", P2: "B", channel:"s"},next:EndType{}}, b:ValueType{value:nil, prefix:Prefix{P1: "B", P2:"A", channel:"t"}, next: RecursiveType{bind: NameType("X"), body: ParallelType{a: ValueType{value:nil, prefix:Prefix{P1: "A", P2: "B", channel:"s"},next:EndType{}}, b:ValueType{value:nil, prefix:Prefix{P1: "B", P2:"A", channel:"t"}, next:NameType("X")}}}}}}

	if !unfold(example_1,make(map[NameType]GlobalType)).equals(unfold_1){
	 	test.FailNow()
	 }
}

func TestLinearityAndCoherence(test *testing.T){
	//test linearity for same example of unfolding
	example_1 := RecursiveType{bind: NameType("X"),
		body: ParallelType{a: ValueType{value:BoolValue, prefix:Prefix{P1: "A", P2: "B", channel:"s"},next:EndType{}}, b:ValueType{value:BoolValue, prefix:Prefix{P1: "B", P2:"A", channel:"t"}, next:NameType("X")}}}

	if linear(example_1){
		test.Errorf("ERROR: Example1 should not be linear\n")
	}
	//Examples in section 3.2 of Honda et al. (2008)
	simple_streaming := RecursiveType{bind:"t", body:ValueType{value:BoolValue, prefix:Prefix{P1: "DP", P2:"K", channel:"d"}, next: ValueType{
		value:BoolValue, 
		prefix:Prefix{P1: "KP", P2: "K", channel:"k"},
		next: ValueType{
			value:BoolValue,
			prefix:Prefix{P1: "K", P2: "C", channel:"c"},
			next: ValueType{
				value: BoolValue,
				prefix: Prefix{P1:"DP", P2:"K", channel:"d"},
				next: ValueType{
					value: BoolValue, 
					prefix: Prefix{P1:"KP", P2:"K", channel:"k"},
					next:ValueType{
						value: BoolValue,
						prefix: Prefix{P1:"K", P2:"C", channel:"c"},
						next: NameType("t")}}}}}}}

	if !linear(simple_streaming){
		test.Errorf("ERROR: Simple_Streaming should be linear\n")
	}

	if !coherent(simple_streaming){
		test.Errorf("ERROR: Simple_Streaming should be coherent\n")
	}
		
	two_buyer_protocol := ValueType{value: BoolValue, prefix:Prefix{P1: "B1", P2:"S", channel:"s"},
		next:ValueType{value:NatValue, prefix: Prefix{P1:"S", P2:"B1", channel:"b1"},
			next:ValueType{value:NatValue, prefix: Prefix{P1:"S", P2:"B2", channel:"b2"},
				next: ValueType{value: NatValue, prefix: Prefix{P1:"B1", P2:"B2", channel:"b'2"},
					next: BranchingType{prefix:Prefix{P1:"B2", P2:"S", channel:"s"},
						branches:map[string]GlobalType{
							"ok": ValueType{value:BoolValue, prefix:Prefix{P1:"B2", P2:"S", channel:"s"},
								next:ValueType{value:BoolValue, prefix:Prefix{P1:"S", P2:"B2", channel:"b2"},
									next:EndType{}}},
							"quit": EndType{}}}}}}}

	if !linear(two_buyer_protocol){
		test.Errorf("ERROR: Two Buyer Protocol should be linear.\n")
	}

	if !coherent(two_buyer_protocol){
		test.Errorf("ERROR: Two Buyer Protocol should be coherent.\n")
	}

	//Example of section 4.2, Honda et al. (2008)
	linear_incoherent := BranchingType{
		prefix:Prefix{P1:"A",P2:"B", channel:"k"},
		branches:map[string]GlobalType{
			"ok": ValueType{value:BoolValue, prefix:Prefix{P1:"C", P2:"D", channel:"k'"},
				next:EndType{}},
			"quit": ValueType{value: NatValue, prefix:Prefix{P1:"C", P2:"D", channel:"k'"},
				next:EndType{}}}}

	if !linear(linear_incoherent){
		test.Errorf("ERROR: Incoherent but linear example is not linear.\n")
	}

	if coherent(linear_incoherent){
		test.Errorf("ERROR: Incoherent but linear example is coherent! should not be.")
	}
}
