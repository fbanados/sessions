package reduction

import (
	"fmt"
)
// Reduction is an attempt to map a set of rules in an evaluation-context oriented semantics into an "eval" method. This will be useful to map the reduction rules in global escape to a real eval method defined recursively on the structure of terms.

// Our language is defined as follows


type Unit struct{}

type Id string
type Lambda struct {
	x Id
	e Exp
}

type App struct{
	f, v Exp
}

type Exp interface{
	eval() Exp
	step() (Exp, bool)
	isValue() bool
	subst(x Id, v Exp) Exp
	unplug() (EC, Exp)
}

func (i Id) eval() Exp{
	return i
}

func (i Id) step() (Exp, bool){
	return nil, false
}

func (i Id) isValue() bool{
	return false
}

func (i Id) subst(x Id, v Exp) Exp{
	if i == x {
		return v
	}
	return i
}

func (i Id) unplug() (EC, Exp){
	return Empty{}, i
}

func (a App) eval() Exp{
	// This is the only interesting rule that does eval.
	var closure Exp
	closure = a
	for{
		ec, exp := closure.unplug()
		step, ok := exp.step()
		if !ok {
			break
		} else {
			fmt.Printf("eval.\n")
		}
		closure = ec.plug(step)
	}
	
	return closure
}

func (a App) isValue() bool{
	return false
}

func (a App) subst (x Id, v Exp) Exp {
	return App{f: a.f.subst(x,v),
		v: a.v.subst(x,v)}
}

func (a App) unplug() (EC, Exp) {
	if a.f.isValue() {
		if a.v.isValue() {
			return Empty{}, a
		}
		rec, val := a.v.unplug()
		return vE{v:a.f, E:rec}, val
	}
	rec, val := a.f.unplug()
	return Ee{e:a.v, E:rec}, val
}

func (a App) step() (Exp, bool){
	// reduction rule (\x.e) v -> [v/x] e
	if a.f.isValue() && a.v.isValue(){
		switch a.f.(type){
		case Lambda:
			f := a.f.(Lambda)
			return f.e.subst(f.x,a.v), true
		}
	}
	return nil, false
}

func (l Lambda) eval() Exp{
	return l
}

func (l Lambda) isValue() bool{
	return true
}

func (l Lambda) subst(x Id, v Exp) Exp{
	if l.x==x {
		return l
	}

	return Lambda{x:l.x, e:l.e.subst(x,v)}
}

func (l Lambda) unplug() (EC, Exp){
	return Empty{}, l
}

func (l Lambda) step() (Exp, bool){
	return nil, false
}

func (u Unit) eval() Exp{
	return u
}

func (u Unit) isValue() bool{
	return true
}

func (u Unit) subst(x Id, v Exp) Exp{
	return u
}

func (u Unit) unplug() (EC, Exp){
	return Empty{}, u
}

func (u Unit) step() (Exp, bool){
	return nil, false
}


// Evaluation rules for contexts
// e -> e'
// ------
// E[e] -> E[e']

// and only one reduction rule:
// (\x.e) v -> [v/x]e


// Evaluation Contexts

// E = [] | E e | v E

// we need a plugs function that will convert an expresion into a set of plugs

// for example (\x . x x) (\x. x)

// should be converted into (with H hole)

// plug (\x . x x) H, 

type EC interface{
	plug(e Exp) Exp
}

type Empty struct{}

func (emp Empty) plug(e Exp) Exp{
	return e
}

type Ee struct{
	E EC
	e Exp
}

func (ee Ee) plug (e Exp) Exp{
	return App{f:ee.E.plug(e), v:ee.e}
}

type vE struct{
	v Exp
	E EC
}

func (ve vE) plug (e Exp) Exp{
	return App{f:ve.v, v:ve.E.plug(e)}
}
