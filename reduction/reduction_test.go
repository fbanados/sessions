package reduction
import (
	"testing"
)

func TestEval(test *testing.T){
	exp := App{f:Lambda{x:Id("x"), e:Id("x")},
		v:App{f:Lambda{x:Id("x"), e:Id("x")}, v:Unit{}}}

	if exp.eval() != (Unit{}) {
		test.Errorf("%+v should reduce to Unit but stays at %+v\n.",exp,exp.eval())
	}
}
