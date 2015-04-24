package escapes

import (
	"github.com/deckarep/golang-set"
	"errors"
	"fmt"
	"time"
	"math/rand"
)

// Escapes is an implementation of the Global Escape for Multiparty
// Sessions framework defined in Capecchi et al. (2014).
// Unfortunately, the paper is sometimes vague in its definitions and
// makes incomplete references to the POPL 2008 paper "Multiparty
// Asynchronous Session Types" by Honda, Yoshida and Carbon (which
// hereafter we will denominate as Honda08, Honda et al. 2008 and
// similar notations).  Whenever there is a (required) definition that
// is not clear from the original Capecchi paper (most likely because
// they claim to follow a definition by Honda08, which is never
// extended to account for global escapes), we provide a definition
// which is original.  We denote functions that implement new
// functionality with CONTRIBUTION.  To reduce the amount of
// annotations, we sometimes annotate an interface definition with
// whether a method in the interface is a contribution.

// Listing of Comment Identifiers (Useful for Grep-ing)
// CONTRIBUTION SECTION



// References to figures or pages that do not include a clear
// reference must be considered as referring to Capecchi et al. (2014)

// Notes

// Restrictions wrt Capecchi et al.

// 1. We decided to allow only single expressions sent atomically
// through a channel.  Why? Because the definition establishes sets
// (not lists!) and as such is hard to formally verify that binding
// works (that binding is order-preserving, for which it would suffice
// to have OrderedSets, but that is never explicit), and also imposes
// restrictions on sending multiple equal expressions atomically. A
// single value sent makes everything simpler.  We consider that this
// is a behavior expected by programmers that does not reduce
// expressivity in the language but simplifies implementation
// considerably.

// SECTION Implementation Language Syntax.

type MultilevelQueue chan Message

type Program interface{
	eval(exceptions []Throw, queues map[Channel]MultilevelQueue) Program
	//step(exceptions []Throw, queues map[Channel]MultilevelQueue) (Program, bool)
	unplugC() (CEC, Program)
	unplugE() (EEC, Program)
	stepC() (Program, bool)
	stepE(exceptions []Throw, queues map[Channel]MultilevelQueue) (Program, bool)
	subst(x Id, e Exp) Program
	typecheck(names SortingNames, vars SortingVariables, gts GlobalTypeEnv) (Typing, error)

}
type Channel struct{
	name string // represents a channel identifier.
	level int
}
type Participant int // represents an identifier for a participant.
type SessionIdentifier string // represents a in Request/Accept
type Label string
// conditions.  Bear in mind that a SessionIdentifier should be
// matched to begin evaluation of a session.

type Request struct{
	// \bar{a}[2..n](\~s).P
	name SessionIdentifier //a
	others []Participant//[2..n]
	channels mapset.Set // a set of channels
	P Program
}

type Accept struct{
	// a[p](\~s).P
	name SessionIdentifier//a
	participant Participant
	channels mapset.Set
	P Program
}

type Output struct{
	// r!<e> binds a set of expression
	channel Channel
	expression Exp //Only one, to simplify stuff.
}

type Input struct{
	//r?(x).P
	channel Channel
	x Id
	P Program
}

type Select struct{
	// r <| l.P
	channel Channel
	label Label
	P Program
}

type Branch struct{
	// r |> {l_i: P_i} i \in I
	channel Channel
	branches map[Label] Program
}

type TryCatch struct{
	channels mapset.Set // a set of channels
	Try, Catch Program
}

type Throw struct{
	// throw(\~s)
	channels mapset.Set
}

type Conditional struct{
	// if e then P else P
	cond Exp
	t, f Program
}

type Parallel struct{
	P, Q Program
}


type Sequencing struct{
	P, Q Program
}

type Inaction struct{}

type Hiding struct{
	//(\eta n P)
	channel Channel //name of the hidden channel
	P Program
}

type ProcessId string

//declarations are used in Recursion calls.
type Declaration struct{
	identifiers []Id
	channels mapset.Set // set of channels
	P Program
}
	

type Recursion struct{
	declarations map[ProcessId] Declaration
	P Program
}

type ProcessCall struct{
	name ProcessId
	expressions []Exp //to be bound to identifiers in a declaration
	channels mapset.Set
}

	// We avoid declaring named queues directly, our interpreter will
	// have a global map of channels to Multilevel Queues, as required
	// by implementation details.  (Future improvement: There's a note
	// in page 10 suggesting to use pairs (level, msg) instead of
	// multilevel queues.  While this is a notable implementation
	// improvement that might reduce overhead, we do not implement it
	// here to avoid making the code even more confusing.

	// The following is commented out for the reasons in the previous comment.
	
// type NamedQueue struct{
// 	name Channel
// 	queue chan Message
// }

	

// SECTION Expressions Syntax.

// CONTRIBUTION The paper does not consider the expressions language
// as an interesting part of their work.  The expressions section
// denotes local node computation, so it will most likely be the
// interesting part to extend in future work.  Without much analysis,
// it seems that there would be not much problem in adding almost all
// the GO language here (likely exception: channels.  Using channels
// for communication outside the Session protocol would allow to break
// all the invariants).

// We define a standard call-by-value interpreter for expressions.

type Exp interface{
	eval() (Value, error)
	subst(x Id, v Exp) Exp
	isValue() bool
}

type Value interface{
	isValue() bool
	isMessage() bool
}

type Id string //Identifiers, to be used in Expressions.

func (i Id) isValue() bool{
	return false
}

type And struct{
	e1, e2 Exp
}

func (a And) isValue() bool{
	return false
}

type Not struct{
	e Exp
}

func (n Not) isValue() bool{
	return false
}


// Values: As defined in Fig. 3.  Only SessionIdentifiers (a) or
// booleans for now.


type Bool bool // You can't define extra methods on bool directly. Boo
							 // golang. Boo.

func (b Bool) isValue() bool{
	return true
}

func (s SessionIdentifier) isValue() bool{
	return true
}

// Messages are things that could be on a queue (on a channel). For
// now, they can only be either labels or values (we already
// established that sending sets of expressions was not implemented
// here)

type Message interface{
	isMessage() bool
}

// Since golang is evil and does not permit general definition of
// methods on interface types, I need to define the method for all
// elements of the Value interface again. Boo golang. Boo.

func (v Bool) isMessage() bool{
	return true
}

func (s SessionIdentifier) isMessage() bool{
	return true
}

func (l Label) isMessage() bool{
	return true
}

// SECTION Expression's eval. We try to encapsulate the full definition of the
// eval function for Expressions here.

func (s SessionIdentifier) eval() (Value, error){
	return s, nil
}

func (s SessionIdentifier) subst(x Id, v Exp) Exp{
	return s
}

func (b Bool) eval() (Value, error){
	return b, nil
}

func (b Bool) subst(x Id, v Exp) Exp{
	return b
}

func (x Id) eval() (Value, error){
	// substitution failed. there is an unbound identifier.  we could
	// simplify this to have an environment, but we also need to carry
	// the environment throughout evaluation of Programs so we simplify
	// here for the prototype.
	return nil, errors.New(fmt.Sprintf("Identifier %v is undefined", x))
}

func (x Id) subst(other Id, v Exp) Exp{
	if x == other {
		return v
	}
	return x
}

func (a And) eval() (Value, error){
	e1, err := a.e1.eval()
	if err != nil {
		return nil, err
	}

	e2, err := a.e2.eval()
	if err != nil {
		return nil, err
	}

	b1, ok1 := e1.(Bool)
	b2, ok2 := e2.(Bool)
	if ok1 && ok2 && bool(b1) && bool(b2) {
		return Bool(true), nil
	}
	return Bool(false), nil
}

func (a And) subst(x Id, v Exp) Exp{
	return And{e1:a.e1.subst(x,v), e2:a.e2.subst(x,v)}
}

func (n Not) eval() (Value, error) {
	e, err := n.e.eval()
	if err != nil {
		return nil, err
	}

	v, ok := e.(Bool)

	if !ok{
		return nil, errors.New("Trying to not a non boolean expression.")
	}

	return Bool(!bool(v)), nil
}

func (n Not) subst(x Id, v Exp) Exp{
	return Not{e:n.e.subst(x,v)}
}

// SECTION Substitution defined for programs.

// Several rules make use of substitution to encompass for receiving messages.
// Even though it is never defined.  (This is standard practice).
// We define it in the standard way.

func (r Request) subst(x Id, v Exp) Program{
	return Request{name:r.name, others:r.others, channels:r.channels, P:r.P.subst(x,v)}
}

func (a Accept) subst (x Id, v Exp) Program{
	return Accept{name:a.name, participant: a.participant, channels:a.channels, P:a.P.subst(x,v)}
}

func (o Output) subst (x Id, v Exp) Program{
	return Output{channel:o.channel, expression:o.expression.subst(x,v)}
}

func (i Input) subst (x Id, v Exp) Program{
	return Input{channel:i.channel, x:i.x, P:i.P.subst(x,v)}
}

func (s Select) subst (x Id, v Exp) Program{
	return Select{channel:s.channel, label:s.label, P:s.P.subst(x,v)}
}

func (b Branch) subst(x Id, v Exp) Program{
	branches := make(map[Label]Program)
	for l, p := range b.branches{
		branches[l] = p.subst(x,v)
	}
	return Branch{channel:b.channel, branches:branches}
}

func (tc TryCatch) subst(x Id, v Exp) Program{
	return TryCatch{channels:tc.channels,
		Try:tc.Try.subst(x,v),
		Catch:tc.Try.subst(x,v)}
}

func (t Throw) subst(x Id, v Exp) Program{
	return t
}

func (c Conditional) subst (x Id, v Exp) Program{
	return Conditional{cond:c.cond.subst(x,v),
		t:c.t.subst(x,v),
		f:c.f.subst(x,v)}
}

func (p Parallel) subst (x Id, v Exp) Program{
	return Parallel{P: p.P.subst(x,v), Q: p.Q.subst(x,v)}
}

func (s Sequencing) subst (x Id, v Exp) Program{
	return Sequencing{P: s.P.subst(x,v), Q: s.Q.subst(x,v)}
}

func (i Inaction) subst (x Id, v Exp) Program{
	return i
}

func (h Hiding) subst (x Id, v Exp) Program{
	return Hiding{channel:h.channel, P:h.P.subst(x,v)}
}

func (d Declaration) subst(x Id, v Exp) Declaration{
	return Declaration{
		identifiers: d.identifiers,
		channels: d.channels,
		P: d.P.subst(x,v),
	}
}

func (r Recursion) subst (x Id, v Exp) Program{
	declarations := make(map[ProcessId] Declaration)

	for pid, decl := range r.declarations {
		declarations[pid] = decl.subst(x,v)
	}

	return Recursion{
		declarations: declarations,
		P : r.P.subst(x,v),
	}
}

func (pc ProcessCall) subst ( x Id, v Exp) Program{
	expressions := make([]Exp, len(pc.expressions), len(pc.expressions))

	for i, e := range pc.expressions{
		expressions[i] = e.subst(x,v)
	}

	return ProcessCall{
		name:pc.name,
		expressions:expressions,
		channels:pc.channels,
	}
}

// SECTION Runtime semantics for Global Escape.

// The following section maps the rules in Fig. 5 and Fig. 6 that were
// used to define a reduction semantics (in a standard "Evaluation
// Context" structure) into an evaluation strategy for the system.  We
// try to keep track of each of the rules used.  A key innovation with
// respect to the formal semantics is as follows: Instead of using
// Queues as a first-class process running in parallel (which
// introduces all sorts of congruence issues and unnecessary stuff),
// we simply keep a global map of channels to Multilevel Queues.
// Though as explained in the paper, and in previous comments, these
// Multilevel Queues could be implemented more efficiently, we have
// opted for increased clarity on the first implementation.

// The runtime semantics is expressed through the eval method in the Program interface.

// However, it is hard to make a direct map from the rules in a
// reduction semantics towards an actual implementation (they are
// useful for other reasons of semantic reasoning).  We follow an
// approach to ease understanding of the transformation, combining an
// explicit notion of evaluation contexts (in both grammars defined in
// page 10) with a notion of "unplug" and "plug" (plug is the standard
// function to combine evaluation contexts and terms that fill the
// hole. "unplug" gets that pair back from a term.) A simple notion of
// both definitions is presented on the reduction.go package, which
// provides a mapping from a reduction semantics for the lambda
// calculus towards an evaluation machine.  Future work is required to
// ensure efficiency and clarity on this code.  We regard our
// implementation as a working prototype.

// SECTION Evaluation Context Definition

// two grammars: C and E (generating CEC ("C" Evaluation Contexts) and
// EEC, respectively)

type CEC interface{
	plug(p Program) Program
}

type CHole struct{}
type CRec struct{
	D map[ProcessId] Declaration
	C CEC
}

type CSeq struct{
	C CEC
	P Program
}

func (h CHole) plug(p Program) Program{
	return p
}

func (d CRec) plug(p Program) Program{
	return Recursion{declarations: d.D, P:d.C.plug(p)}
}

func (s CSeq) plug (p Program) Program{
	return Sequencing{P:s.C.plug(p), Q:s.P}
}

type EEC interface{
	plug(p Program) Program
}

type EHole struct{}

type ERec struct{
	D map[ProcessId] Declaration
	E EEC
}

type ESeq struct{
	E EEC
	P Program
}

type EParallel struct{
	E EEC
	P Program
}

type EHiding struct{
	channel Channel
	E EEC
}

type ETryCatch struct{
	channels mapset.Set
	Try EEC
	Catch Program
}

func (h EHole) plug(p Program) Program {
	return p
}

func (d ERec) plug(p Program) Program {
	return Recursion{declarations:d.D, P:d.E.plug(p)}
}

func (d ESeq) plug(p Program) Program {
	return Sequencing{P:d.E.plug(p), Q:d.P}
}

func (ep EParallel) plug(p Program) Program {
	return Parallel{P:ep.E.plug(p), Q:ep.P}
}

func (h EHiding) plug(p Program) Program {
	return Hiding{channel:h.channel, P:h.E.plug(p)}
}

func (tc ETryCatch) plug(p Program) Program {
	return TryCatch{channels: tc.channels, Try:tc.Try.plug(p), Catch:tc.Catch}
}

func (r Request) unplugC() (CEC, Program) {
	return CHole{}, r
}

func (a Accept) unplugC() (CEC, Program) {
	return CHole{}, a
}

func (o Output) unplugC() (CEC, Program) {
	return CHole{}, o
}

func (i Input) unplugC() (CEC, Program) {
	return CHole{}, i
}

func (s Select) unplugC() (CEC, Program) {
	return CHole{}, s
}

func (b Branch) unplugC() (CEC, Program) {
	return CHole{}, b
}

func (tc TryCatch) unplugC() (CEC, Program) {
	return CHole{}, tc
}

func (t Throw) unplugC() (CEC, Program) {
	return CHole{}, t
}

func (c Conditional) unplugC() (CEC, Program) {
	return CHole{}, c
}

func (p Parallel) unplugC() (CEC, Program) {
	return CHole{}, p
}

func (s Sequencing) unplugC() (CEC, Program) {
	// Only Sequencing and Recursion are interesting
	ec, p := s.P.unplugC()
	return CSeq{C:ec, P:s.Q}, p
}

func (i Inaction) unplugC() (CEC, Program) {
	return CHole{}, i
}

func (h Hiding) unplugC() (CEC, Program) {
	return CHole{}, h
}

func (r Recursion) unplugC() (CEC, Program) {
	// Only Sequencing and Recursion are interesting
	ec, p := r.P.unplugC()
	return CRec{D:r.declarations, C:ec}, p
}

func (pc ProcessCall) unplugC() (CEC, Program) {
	return CHole{}, pc
}


func (r Request) unplugE() (EEC, Program) {
	return EHole{}, r
}

func (a Accept) unplugE() (EEC, Program) {
	return EHole{}, a
}

func (o Output) unplugE() (EEC, Program) {
	return EHole{}, o
}

func (i Input) unplugE() (EEC, Program) {
	return EHole{}, i
}

func (s Select) unplugE() (EEC, Program) {
	return EHole{}, s
}

func (b Branch) unplugE() (EEC, Program) {
	return EHole{}, b
}

func (tc TryCatch) unplugE() (EEC, Program) {
	ec, p := tc.Try.unplugE()
	return ETryCatch{channels: tc.channels, Try:ec, Catch:tc.Catch}, p
}

func (t Throw) unplugE() (EEC, Program) {
	return EHole{}, t
}

func (c Conditional) unplugE() (EEC, Program) {
	return EHole{}, c
}

func (p Parallel) unplugE() (EEC, Program) {
	ec, pr := p.P.unplugE()
	return EParallel{E:ec, P:p.Q}, pr
}

func (s Sequencing) unplugE() (EEC, Program) {
	ec, p := s.P.unplugE()
	return ESeq{E:ec, P:s.Q}, p
}

func (i Inaction) unplugE() (EEC, Program) {
	return EHole{}, i
}

func (h Hiding) unplugE() (EEC, Program) {
	ec, p := h.P.unplugE()
	return EHiding{channel: h.channel, E:ec}, p
}

func (r Recursion) unplugE() (EEC, Program) {
	ec, p := r.P.unplugE()
	return ERec{D:r.declarations, E:ec}, p
}

func (pc ProcessCall) unplugE() (EEC, Program) {
	return EHole{}, pc
}

// SECTION step definitions.
// step is a one-step transition in the reduction semantics
// (well... IF the semantics was defined nicely)

func (r Request) stepC() (Program, bool){
	return nil, false
}

func (a Accept) stepC() (Program, bool){
	return nil, false
}

func (o Output) stepC() (Program, bool){
	return nil, false
}

func (i Input) stepC() (Program, bool){
	return nil, false
}

func (s Select) stepC() (Program, bool){
	return nil, false
}

func (b Branch) stepC() (Program, bool){
	return nil, false
}

func (t TryCatch) stepC() (Program, bool){
	return nil, false
}

func (t Throw) stepC() (Program, bool){
	return nil, false
}

func (c Conditional) stepC() (Program, bool){
	return nil, false
}

func (p Parallel) stepC() (Program, bool){
	// this is the only interesting stepping. Tries to match a session

	// We try to match structurally for the body of rule [Link]

	req, isRequest := p.P.(Request)

	if isRequest && len(req.others)>0{
		// Then find out how many accepting participants i require and chech that they are defined as a parallel IN ORDER :)
		programs := make([]Program,0,len(req.others))
		accept := p.Q
		for i :=0; i<(len(req.others)-1); i++{
			par , isParallel := accept.(Parallel)
			if !isParallel{
				return nil, false
			}
			programs = append(programs, par.P)
			accept = par.Q
		}

		accepts := make([]Accept, len(programs), len(programs))

		for i, candidate := range programs {
			if accept, isAccept := candidate.(Accept); isAccept {
				accepts[i] = accept
			} else {
				return nil, false
			}
		}

		channels := accepts[0].channels

		
		var program Program

		program = Inaction{}

		for _, accept := range accepts {
			if !channels.Equal(accept.channels) {
				return nil, false
			}
			program = Parallel{Q: program, P: accept.P}
		}

		// At this point, it is structurally as required. We can return the binding.
		
		for _, channel := range channels.ToSlice(){
			program = Hiding{channel: channel.(Channel), P: program}
		}

		return program, true
	}
	return nil, false
}

func (s Sequencing) stepC() (Program, bool){
	return nil, false
}

func (i Inaction) stepC() (Program, bool){
	return nil, false
}

func (h Hiding) stepC() (Program, bool){
	return nil, false
}

func (r Recursion) stepC() (Program, bool){
	return nil, false
}

func (p ProcessCall) stepC() (Program, bool){
	return nil, false
}


func (r Request) stepE(exceptions []Throw, queues map[Channel]MultilevelQueue) (Program, bool){
	return nil, false
}

func (a Accept) stepE(exceptions []Throw, queues map[Channel]MultilevelQueue) (Program, bool){
	return nil, false
}

func (o Output) stepE(exceptions []Throw, queues map[Channel]MultilevelQueue) (Program, bool){
	value, error := o.expression.eval()
	if error == nil {
		queue, exists := queues[o.channel]
		if !exists{
			//rule [Send2]
			queues[o.channel] = make(chan Message,256)
			queue = queues[o.channel]
		}
		// rule [Send1]

		queue <- value
		return Inaction{}, true
	}
	return nil, false
}

func (i Input) stepE(exceptions []Throw, queues map[Channel]MultilevelQueue) (Program, bool){
	// [Recv] Rule
	select {
	case value := <- queues[i.channel]:
		return i.P.subst(i.x,value.(Exp)), true
	case <-time.After(time.Second):
	}
	return nil, false		
}

func (s Select) stepE(exceptions []Throw, queues map[Channel]MultilevelQueue) (Program, bool){
	if _ , exists := queues[s.channel]; !exists{
		queues[s.channel]=make(chan Message, 256)
	}
	queues[s.channel]<-s.label
	
	return s.P, true
}

func (b Branch) stepE(exceptions []Throw, queues map[Channel]MultilevelQueue) (Program, bool){

	pick := rand.Intn(len(b.branches))
	i := 0
	for l, P := range b.branches{
		if i == pick {
			queues[b.channel] <- l
			return P, true
		}
		i++
	}
	return nil, false
}

func (t TryCatch) stepE(exceptions []Throw, queues map[Channel]MultilevelQueue) (Program, bool){
	return nil, false
}

func (t Throw) stepE(exceptions []Throw, queues map[Channel]MultilevelQueue) (Program, bool){
	return nil, false
}

func (c Conditional) stepE(exceptions []Throw, queues map[Channel]MultilevelQueue) (Program, bool){
	return nil, false
}

func (p Parallel) stepE(exceptions []Throw, queues map[Channel]MultilevelQueue) (Program, bool){
	return nil, false
}

func (s Sequencing) stepE(exceptions []Throw, queues map[Channel]MultilevelQueue) (Program, bool){
	return nil, false
}

func (i Inaction) stepE(exceptions []Throw, queues map[Channel]MultilevelQueue) (Program, bool){
	return nil, false
}

func (h Hiding) stepE(exceptions []Throw, queues map[Channel]MultilevelQueue) (Program, bool){
	return nil, false
}

func (r Recursion) stepE(exceptions []Throw, queues map[Channel]MultilevelQueue) (Program, bool){
	if PR, ok := r.P.(Parallel); ok{
		P := PR.P
		Q := PR.Q
		if pc, ok := P.(ProcessCall); ok{
			values := make([]Exp, len(pc.expressions), len(pc.expressions))
			for i, exp := range pc.expressions{
				v, err := exp.eval()
				if err != nil{
					return nil, false
				}
				values[i] = v.(Exp)
			}
			if D, ok := r.declarations[pc.name]; ok{
				P = D.P
				if D.channels.Equal(pc.channels){
					if len(D.identifiers) == len(values){
						for i := range values {
							P = P.subst(D.identifiers[i], values[i])
						}
						return Recursion{
							declarations: r.declarations,
							P: Parallel{P:P, Q:Q},
						}, true
					}
				}
			}
		}
	}
	return nil, false
}

func (p ProcessCall) stepE(exceptions []Throw, queues map[Channel]MultilevelQueue) (Program, bool){
	return nil, false
}

func (r Request) eval (exceptions []Throw, queues map[Channel]MultilevelQueue) Program{
	// request and accepts don't do anything on their own.
	// only when in parallel and under a CEC they reduce through link
	return r
}

func (a Accept)  eval (exceptions []Throw, queues map[Channel]MultilevelQueue) Program{
		return a
}

func (o Output)  eval (exceptions []Throw, queues map[Channel]MultilevelQueue) Program {
	if step, ok := o.stepE(exceptions, queues); ok {
		return step
	} 
	return o
}

func (i Input) eval (exceptions []Throw, queues map[Channel]MultilevelQueue) Program {
	if step, ok := i.stepE(exceptions, queues); ok {
		return step
	}
	return i
}

func (s Select) eval (exceptions []Throw, queues map[Channel]MultilevelQueue) Program {
	if step, ok := s.stepE(exceptions, queues); ok {
		return step
	}
	return s
}

func (b Branch) eval (exceptions []Throw, queues map[Channel]MultilevelQueue) Program {
	if step, ok := b.stepE(exceptions, queues); ok {
		return step
	}
	return b
}

func THRexceptionsPrecondition(exceptions []Throw, channels mapset.Set) bool{
	for _, thr := range exceptions{

		for _, throwncandidate := range thr.channels.ToSlice(){
			if thrown, ok := throwncandidate.(Channel); ok{
				for _, precond := range channels.ToSlice(){
					if precondition, ok := precond.(Channel); ok{
						if precondition.name == thrown.name && thrown.level > precondition.level{
							// precondition doesn't hold.
							return false
						}
					} else {
						//there was a non channel on the set.
						return false
					}
				}
			} else {
				// There was a non channel on the set. boo golang. boo.
				return false
			}
		}
	}
	return true
}

func HasThrown( exceptions []Throw, channels mapset.Set) bool{
	for _, throw := range exceptions{
		if throw.channels.IsSuperset(channels){
			return true
		}
	}
	return false
}

func (tc TryCatch) eval (exceptions []Throw, queues map[Channel]MultilevelQueue) Program {
	// This is the most complex and interesting eval rule.

	_, thrc := tc.Try.unplugE()
	if throw, ok := thrc.(Throw); ok{
		//In this lovely case, rule Thr applies.
		if THRexceptionsPrecondition(exceptions, tc.channels) {
			return TryCatch{channels:tc.channels, Try:Inaction{}, Catch:tc.Catch}.eval(append(exceptions, throw), queues)
		}
	}

	//Rule RThr
	if HasThrown(exceptions, tc.channels){
		//First empty channels. This may lead to future bugs, but is the expected semantics.
		for _, ch := range tc.channels.ToSlice(){
			delete(queues, ch.(Channel))
		}

		return tc.Catch.eval(exceptions,queues)
	}

	// Rule Eval
	if eec, exp := tc.unplugE(); (eec != EHole{}){
		if step, ok := exp.stepE(exceptions, queues); ok {
			return eec.plug(step).eval(exceptions,queues)
		}
	}

	// Ok. Last case is rule (ZThr), which applies when correct
	// computation has finished. While it expects also an inaction at
	// the beginning, it is not the same inaction that we introduced for
	// rule Thr: Control won't reach this stage because of HasThrown()
	// (which will be true)

	// I disagree with the paper's restriction of reduction under a
	// hiding evaluation context. I will implement what I believe to be
	// correct, because the semantics in this paper is clearly wrong in
	// several situations.

	
	if _, ok := tc.Try.(Inaction); ok{
		//We simplify the (ZThr) rule because there is a lot of nonsense there.
		return Inaction{}
	}
	
	return tc
}

func (t Throw) eval (exceptions []Throw, queues map[Channel]MultilevelQueue) Program {
		return t
}

func (c Conditional) eval (exceptions []Throw, queues map[Channel]MultilevelQueue) Program {
	// This is the easiest rule to implement.

	cond, err := c.cond.eval()

	// We will follow a simple scheme / C -like definition. All values
	// != false are equivalent to true.

	// We also will consider errors as false.

	isTrue, castPasses := cond.(Bool)
	if err != nil || (castPasses && !bool(isTrue)) {
		return c.f.eval(exceptions, queues)
	}
	return c.t.eval(exceptions, queues)
}

func (p Parallel) eval (exceptions []Throw, queues map[Channel]MultilevelQueue) Program {
	// This is the (second) most complex rule to be evaluated.

	// This makes a simplifying assumption instead of using detailed CEC.
	if link, canLink := p.stepC(); canLink{
		return link.eval(exceptions, queues)
	}

	// see if one of the branches is redundant (congruency)

	if _, ok := p.P.(Inaction); ok {
		return p.Q.eval(exceptions, queues)
	}

	if _, ok := p.Q.(Inaction); ok {
		return p.P.eval(exceptions, queues)
	}

	//Otherwise, we are in an evaluation context.

	// This is complicated: We need to independently step on one of the sides.
	// We flip a coin to choose which side to step on.

	candidates := append(make([]Program,0,2),p.P,p.Q)

	first := rand.Intn(2)
	second := 1 - first

	if eec, exp1 := candidates[first].unplugE(); (eec != EHole{}){
		if step, ok := exp1.stepE(exceptions, queues); ok {
			return Parallel{P:eec.plug(step), Q:candidates[second]}.eval(exceptions, queues)
		}
	}
	if step, ok := candidates[first].stepE(exceptions, queues); ok{
		return Parallel{P:step, Q:candidates[second]}.eval(exceptions, queues)
	}

	if eec, exp2 := candidates[second].unplugE(); (eec != EHole{}){
		if step, ok := exp2.stepE(exceptions, queues); ok {
			return Parallel{P:candidates[first], Q:eec.plug(step).eval(exceptions, queues)}.eval(exceptions, queues)
		}
	}

	if step, ok := candidates[second].stepE(exceptions, queues); ok{
		return Parallel{P:candidates[first], Q:step}.eval(exceptions, queues)
	}
	
	return p
}

func (s Sequencing) eval (exceptions []Throw, queues map[Channel]MultilevelQueue) Program {
	// for side effects :)
	s.P.eval(exceptions, queues)
	return s.Q.eval(exceptions, queues)
}

func (i Inaction) eval (exceptions []Throw, queues map[Channel]MultilevelQueue) Program {
		return i
}

func (h Hiding) eval (exceptions []Throw, queues map[Channel]MultilevelQueue) Program{

	// congruency restrictions
	if end, ok := h.P.(Inaction); ok{
		return end
	}

	// evaluation context
	
	eec, exp := h.unplugE()

	if step, ok := exp.stepE(exceptions, queues); ok {
		return eec.plug(step).eval(exceptions, queues)
	}

	return h
}

func (r Recursion) eval (exceptions []Throw, queues map[Channel]MultilevelQueue) Program {
	// Try first to unplugC

	if cec, expc := r.unplugC(); (cec != CHole{}){
		// on a CEC. then evaluate recursively.
		if stepc, ok := expc.stepC(); ok {
			return cec.plug(stepc).eval(exceptions, queues)
		}
	}

	if eec, expe := r.unplugE(); (eec != EHole{}){
		// Rule (Eval) for recursion evaluation contexts.
		// on an EEC.
		if stepe, ok := expe.stepE(exceptions, queues); ok {
			return eec.plug(stepe).eval(exceptions, queues)
		}
	}

	if step, ok := r.stepE(exceptions, queues); ok {
		return step.eval(exceptions, queues)
	}
	return r
}

func (pc ProcessCall) eval (exceptions []Throw, queues map[Channel]MultilevelQueue) Program {
	// This is the simple implementation. There should be a later
	// version that does definition lookup on an environment. But
	// substitution works for the prototype.	
		return pc
}


// SECTION Types. We modify the basis of the type system by (Honda08)

// GLOBAL TYPES

type GlobalType interface{
	isWellFormed() bool
	Prefixes() mapset.Set
	participants() mapset.Set
	channels() mapset.Set
	project(p Participant) (LocalType, error)
	equals(t GlobalType) bool
}

type Sort string

type Prefix struct{
	P1, P2 Participant
	channel Channel
}

func (p Prefix) participants() mapset.Set{
	set := mapset.NewSet()
	set.Add(p.P1)
	set.Add(p.P2)
	return set
}

type SortGT struct{
	prefix Prefix
	sorts mapset.Set
}

func Singleton(element interface{}) mapset.Set{
	set := mapset.NewSet()
	set.Add(element)
	return set
}

func (t SortGT) isWellFormed() bool{
	return true
}

func (t SortGT) Prefixes() mapset.Set{
	return Singleton(t.prefix)
}

func (t SortGT) participants() mapset.Set{
	return t.prefix.participants()
}

func (t SortGT) project(p Participant) (LocalType, error){
	// TODO
	//ans , err:= t.next.project(p)
	// if err != nil {
	// 	return nil, err
	// } else if t.prefix.P1 == p {
	// 	ans = LocalSendType{channel:t.prefix.channel, value:t.value, next: ans}
	// } else if t.prefix.P2 == p {
	// 	ans = LocalReceiveType{channel:t.prefix.channel, value:t.value, next:ans}
	// }
	// return ans, err
	return nil, nil
}

func (t SortGT) equals(g GlobalType) bool {
	switch g.(type){
	case SortGT:
		gt := g.(SortGT)
		return gt.prefix == t.prefix && gt.sorts.Equal(t.sorts)
	}	
	return false
}

func (t SortGT) channels() mapset.Set{
	return Singleton(t.prefix.channel)
}


type BranchingGT struct{
	prefix Prefix
	branches map[Label] GlobalType
}

func (t BranchingGT) channels() mapset.Set {
	set := Singleton(t.prefix.channel)
	for _, gt := range t.branches{
		set = set.Union(gt.channels())
	}
	return set
}

func (t BranchingGT) Prefixes() mapset.Set{
	set := Singleton(t.prefix)
	for _ , branch := range t.branches{
		set  = set.Union(branch.Prefixes())
	}
	return set
}

func (t BranchingGT) isWellFormed() bool{
	for _, value := range t.branches{
		if !value.isWellFormed(){
			return false
		}
	}
	return true
}

func (t BranchingGT) participants() mapset.Set{
	set := t.prefix.participants()
	for _, val := range t.branches {
		set = set.Union(val.participants())
	}
	return set
}

func (t BranchingGT) project(p Participant) (LocalType, error){
	// TODO
	branches := make(map[Label]LocalType)

	for key, value := range t.branches{
		candidate, err := value.project(p)
		if err != nil {
			return nil, err
		}
		branches[key] = candidate
	}

	unique := func(branches map[Label]LocalType) bool{
		var prevValue LocalType

		// preset with first value in the range

		for _ , prevValue = range branches {
			break
		}

		for _ , value := range branches{
			if !prevValue.equals(value) {
				return false
			}
		}
		return true
	}

	if t.prefix.P1 == p {
		return SelectLT{ channel:t.prefix.channel,branches: branches}, nil
	} else if t.prefix.P2 == p {
		return BranchingLT{ channel:t.prefix.channel, branches : branches}, nil
	} else if unique(branches) {
		for _, branch := range branches{
			return branch, nil
		}
	}
	return nil, errors.New("projection undefined")
}

func (t BranchingGT) equals(g GlobalType) bool{
	switch g.(type){
	case BranchingGT:
		gt := g.(BranchingGT)
		for x := range t.branches {
			if !t.branches[x].equals(gt.branches[x]){
				return false
			}
		}
		return t.prefix == gt.prefix
	}
	return false
}

type ParallelGT struct{
	a, b GlobalType
}

func (t ParallelGT) channels() mapset.Set{
	return t.a.channels().Union(t.b.channels())
}

func (t ParallelGT) Prefixes() mapset.Set{
	return t.a.Prefixes().Union(t.b.Prefixes())
}

func (t ParallelGT) isWellFormed() bool{
	return t.a.isWellFormed() && t.b.isWellFormed()
}

func (t ParallelGT) participants() mapset.Set{
	return t.a.participants().Union(t.b.participants())
}

func (t ParallelGT) project(p Participant) (LocalType, error) {
	//TODO
	if t.a.participants().Contains(p) {
		if t.b.participants().Contains(p) {
			return nil, errors.New("projection undefined")
		}
		return t.a.project(p)
	}
	if t.b.participants().Contains(p) {
		return t.b.project(p)
	}
	ans := EmptyLT{}
	return ans, nil
}

func (t ParallelGT) equals(g GlobalType) bool{
	switch g.(type){
	case ParallelGT:
		gt := g.(ParallelGT)
		return t.a.equals(gt.a) && t.b.equals(gt.b)
	}
	return false
}

type NameGT string

func (t NameGT) isWellFormed() bool{
	return true
}

func (t NameGT) Prefixes() mapset.Set{
	return mapset.NewSet()
}

func (t NameGT) participants() mapset.Set{
	return mapset.NewSet()
}

func (t NameGT) project(p Participant) (LocalType, error){
	//TODO
	return NameLT(t), nil
}

func (t NameGT) channels() mapset.Set{
	return mapset.NewSet()
}

func (t NameGT)  equals(g GlobalType) bool{
	switch g.(type){
	case NameGT:
		return t == g.(NameGT)
	}
	return false
}

type SequencingGT struct{
	a, b GlobalType
}

func (t SequencingGT) channels() mapset.Set{
	return t.a.channels().Union(t.b.channels())
}

func (t SequencingGT) isWellFormed() bool{
	return t.a.isWellFormed() && t.b.isWellFormed()
}

func (t SequencingGT) Prefixes() mapset.Set{
	return t.a.Prefixes().Union(t.b.Prefixes())
}

func (t SequencingGT) participants() mapset.Set{
	return t.a.participants().Union(t.b.participants())
}

func (t SequencingGT) project(p Participant) (LocalType, error){
	//TODO
	return nil, nil
}

func (t SequencingGT) equals(g GlobalType) bool{
	switch g.(type){
	case SequencingGT:
		gs := g.(SequencingGT)
		return t.a.equals(gs.a) && t.b.equals(gs.b)
	}
	return false
}

type RecursiveGT struct{
	bind NameGT
	body GlobalType
}

func (t RecursiveGT) channels() mapset.Set{
	return t.body.channels()
}

func (t RecursiveGT) isWellFormed() bool{
	return t.body.isWellFormed()
}

func (t RecursiveGT) Prefixes() mapset.Set{
	return t.body.Prefixes()
}

func (t RecursiveGT) participants() mapset.Set{
	return t.body.participants()
}

func (t RecursiveGT) project(p Participant) (LocalType, error){
	// TODO
	body, err := t.body.project(p)
	if err != nil {
		return nil, err
	}
	return RecursiveLT{bind:NameLT(t.bind),body:body}, nil
}

func (t RecursiveGT)  equals(g GlobalType) bool{
	switch g.(type){
	case RecursiveGT:
		gt := g.(RecursiveGT)
		return t.bind.equals(gt.bind) && t.body.equals(gt.body)
	}
	return false
}

type EmptyGT struct{}

func (t EmptyGT) isWellFormed() bool{
	return true
}

func (t EmptyGT) channels() mapset.Set{
	return mapset.NewSet()
}

func (t EmptyGT) Prefixes() mapset.Set{
	return mapset.NewSet()
}

func (t EmptyGT) participants() mapset.Set{
	return mapset.NewSet()
}

func (t EmptyGT) project(p Participant) (LocalType, error){
	// TODO
	return EmptyLT(t), nil
}

func (t EmptyGT)  equals(g GlobalType) bool{
	switch g.(type){
	case EmptyGT:
		return true
	}
	return false
}

type TryCatchGT struct{
	s mapset.Set
	Try, Catch GlobalType
}

func (t TryCatchGT) isWellFormed() bool{
	return t.Try.isWellFormed() && t.Catch.isWellFormed()
}

func (t TryCatchGT) channels() mapset.Set{
	return t.Try.channels().Union(t.Catch.channels()).Union(t.s)
}

func (t TryCatchGT) Prefixes() mapset.Set{
	return t.Try.Prefixes().Union(t.Catch.Prefixes())
}

func (t TryCatchGT) participants() mapset.Set{
	return t.Try.participants().Union(t.Catch.participants())
}

func (t TryCatchGT) project(p Participant) (LocalType, error){
	// TODO
	return nil, nil
}

func linear(original_gt GlobalType) bool{
	gt := unfold(original_gt, make(map[NameGT] GlobalType))
	return linearInternal(gt, make([]Prefix, 0, 0))
}

//Definition 4.2, from Honda08
func coherent(original_gt GlobalType) bool{
	if !linear(original_gt) {
		return false
	}
	gt := unfold(original_gt, make(map[NameGT] GlobalType))
	for _, p := range gt.participants().ToSlice() {
		_ , err := gt.project(p.(Participant))
		if err != nil{
			return false
		}
	}
	return true
}

func (n1 Prefix) II(n2 Prefix) bool{
	if n1.P2 != n2.P2 {
		fmt.Printf("DEP: II doesn't hold. expects equal P2 among %+v and %+v\n", n1, n2)
		return false
	}
	if n1.channel != n2.channel && n1.P1 != n2.P1{
		//second if condition given on the tech report.
		return true
	}
	fmt.Printf("DEP: II doesn't hold. expects different channels among %+v and %+v\n", n1, n2)

	return false
}

func (n1 Prefix) IO(n2 Prefix) bool{
	if n1.P2 != n2.P1 {
		fmt.Printf("DEP: IO doesn't hold. expects shared participant among %+v and %+v.\n", n1, n2)
		return false
	}
	if n1.channel == n2.channel {
		fmt.Printf("DEP: IO doesn't hold. expects different channels on n1P1 and n2P2 for %+v and %+v\n",n1, n2)
		return false
	}
	return true
}

func (n1 Prefix) OO(n2 Prefix) bool{
	if n1.P1 != n2.P1 {
		fmt.Printf("DEP: OO doesn't hold. expects same P1 among %+v and %+v.\n", n1, n2)
		return false
	}
	if n1.channel != n2.channel && n1.P2 != n2.P2{
		//extra if confition derived from tech report.
		//OO holds subject to p1 \neq p2 => k1 \neq k2,
		// for pfx(n1) = p -> p1: k1 and pfx(n2) = p -> p2 : k2
		// (Tech report at http://www.doc.ic.ac.uk/~pmalo/research/papers/buffer-communication-analysis.pdf)
		fmt.Printf("DEP: OO doesn't hold. expects shared channel among %v and %v.\n", n1, n2)
		return false
	}
	return true
}

func filter_shared_channel(lessthan [] Prefix, filter Prefix) [] Prefix{
	ans :=make([]Prefix, 0, 0)
	for _, prefix := range lessthan {
		if prefix.channel == filter.channel {//&& prefix != filter{
			ans=append(ans,prefix)
		}
	}
	return ans
}

 
func linearInternal(gt GlobalType, lessthan []Prefix) bool{
	// TODO
	/*
overall implementation idea:
since we already have unwrapped, we only need to locally check and there's a finite amount of nodes to explore (we already removed the cycles via unfold)

- 
*/
	switch gt.(type){
	case SortGT:
		t := gt.(SortGT)
		filtered_lessthan :=filter_shared_channel(lessthan, t.prefix)
		if !(InputDependency(filtered_lessthan, t.prefix) && OutputDependency(filtered_lessthan, t.prefix)){
			fmt.Printf("ERROR: Failed to collect dependencies for SortGT %+v\n", t)
			return false
		}
		//linearInternal(t.next,append(lessthan,t.prefix))
	case BranchingGT:
		t := gt.(BranchingGT)
		filtered_lessthan := filter_shared_channel(lessthan, t.prefix)
		if !(InputDependency(filtered_lessthan, t.prefix) && OutputDependency(filtered_lessthan, t.prefix)){
			fmt.Printf("ERROR: Failed to collect dependencies for BranchingGT %+v\n", t)
			return false
		}
		new_lessthan:=append(lessthan, t.prefix)
		for _, value := range t.branches {
			if ! linearInternal(value, new_lessthan) {
				return false
			}
		}
	case ParallelGT:
		t := gt.(ParallelGT)
		for _, prefixes := range t.b.Prefixes().ToSlice() {
			//fmt.Printf("DEBUG: Checking Parallel linearity with %+v and %+v\n",lessthan, prefixes)
			if ! linearInternal(t.a, append(lessthan,prefixes.(Prefix))){
				return false
			}
		}
		for _, prefixes := range t.a.Prefixes().ToSlice() {
			if ! linearInternal(t.b, append(lessthan,prefixes.(Prefix))) {
				return false
			}
		}
	case RecursiveGT:
		t := gt.(RecursiveGT)
		//fmt.Printf("DEBUG: Entering body of type %+v\n", t)
		return linearInternal(t.body, lessthan)
	case NameGT:
	case EmptyGT:
	}
	return true
}

// TODO
func InputDependency(firsts []Prefix, last Prefix) bool{
	if len(firsts)<1 {
		return true
	}
	for i := 0; i<len(firsts)-1; i++ {
		if !(firsts[i].II(last) || firsts[i].IO(last)) {
			fmt.Printf("ERROR: Broke input dependency with %v and %v\n", firsts[i], last)
			return false
		}
	}
	if !firsts[len(firsts)-1].II(last){
		fmt.Printf("Error: Broke input dependency last-II invariant between %v and %v.\n", firsts[len(firsts)-1], last)
		return false
	}
	return true
}

// TODO
func OutputDependency(firsts []Prefix, last Prefix) bool{
	if len(firsts)<1 {
		return true
	}
	for _, first := range firsts{
		if !(first.IO(last) || first.OO(last)){
			fmt.Printf("Error: Broke output dependency invariant between %v and %v.\n", first, last)
			return false
		}
	}
	return true
}

// TODO
func unfold(gt GlobalType, env map[NameGT] GlobalType) GlobalType{
	switch gt.(type){
	case SortGT:
		return gt
	case BranchingGT:
		t := gt.(BranchingGT)
		branches := make(map[Label]GlobalType)
		for key, value := range t.branches{
			branches[key] = unfold(value, env)
		}
		return BranchingGT{prefix: t.prefix, branches:branches}
	case ParallelGT:
		t := gt.(ParallelGT)
		return ParallelGT{a: unfold(t.a,env), b: unfold(t.b, env)}
 	case RecursiveGT:
		t := gt.(RecursiveGT)
		if val, ok := env[t.bind]; ok {
			if val != t {
				//name hiding!
				old_val := val
				env[t.bind] = t
				ans := RecursiveGT{bind:t.bind, body:unfold(t.body, env)}
				env[t.bind] = old_val
				return ans
			} else {
				//I already unfolded once. then return (avoid infinite loop)
				return t
			}
		}
		env[t.bind] = t
		return RecursiveGT{bind:t.bind, body:unfold(t.body, env)}
	case NameGT:
		t := gt.(NameGT)
		if val, ok := env[t]; ok {
			return val
		}
		return t
	case EmptyGT:
		return gt
	}
	return nil
}

// LOCAL TYPES

// UNFOLD
type LocalType interface{
	equals(t LocalType) bool
}

type ProjectionType struct{
	// Original, Type @ participant
	T LocalType
	participant Participant
}

func (t ProjectionType) equals(l LocalType) bool{
	switch l.(type){
	case ProjectionType:
		lt := l.(ProjectionType)
		return t.participant == lt.participant && t.T.equals(lt.T)
	}
	return false
}

// any use of findProjection should be replaced by using a map[Participant]LocalType. This is more efficient and readable.

type SendLT struct{
	channel Channel
	value Sort
	next LocalType
}

func (t SendLT) equals(l LocalType) bool{
	switch l.(type){
	case SendLT:
		lt := l.(SendLT)
		return t.channel == lt.channel && t.value == lt.value && t.next.equals(lt.next)
	}
	return false
}

type ReceiveLT struct{
	channel Channel
	value Sort
	next LocalType
}

func (t ReceiveLT) equals(l LocalType) bool{
	switch l.(type){
	case ReceiveLT:
		lt := l.(ReceiveLT)
		return t.channel == lt.channel && t.value == lt.value && t.next.equals(lt.next)
	}
	return false
}

type SelectLT struct{
	// k \oplus
	channel Channel
	branches map[Label] LocalType
}

func (t SelectLT) equals(l LocalType) bool{
	switch l.(type){
	case SelectLT:
		lt := l.(SelectLT)
		for k := range t.branches{
			if !t.branches[k].equals(lt.branches[k]){
				return false
			}
		}
		return t.channel == lt.channel
	}
	return false
}

type BranchingLT struct{
	// k &
	channel Channel
	branches map[Label] LocalType
}


func (t BranchingLT) equals(l LocalType) bool{
	switch l.(type){
	case BranchingLT:
		lt := l.(BranchingLT)
		for k := range t.branches{
			if !t.branches[k].equals(lt.branches[k]){
				return false
			}
		}
		return t.channel == lt.channel
	}
	return false
}

type NameLT string

func (t NameLT) equals(l LocalType) bool{
	switch l.(type){
	case NameLT:
		return t == l.(NameLT)
	}
	return false
}

type RecursiveLT struct{
	bind NameLT
	body LocalType
}

func (t RecursiveLT) equals(l LocalType) bool{
	switch l.(type){
	case RecursiveLT:
		lt := l.(RecursiveLT)
		return t.bind.equals(lt.bind) && t.body.equals(lt.body)
	}
	return false
}

type EmptyLT struct{}

func (t EmptyLT) equals(l LocalType) bool{
	switch l.(type){
	case EmptyLT:
		return true
	}
	return false
}

// end of local types and definition of projection.


type SortingNames map[string]mapset.Set
type ProcessVariable struct{
	sorts []Sort
	types map[Participant]LocalType
}

type SortingVariables map[string]ProcessVariable

type GlobalTypeEnv map[SessionIdentifier]GlobalType

type Typing interface{
	find(key mapset.Set) (map[Participant]LocalType, bool)
	domain() []mapset.Set
	add(key mapset.Set, value map[Participant]LocalType) Typing
	remove(key mapset.Set) Typing
}
	
type EmptyTyping struct{}

func (et EmptyTyping) add(key mapset.Set, values map[Participant]LocalType) Typing {
	return TypingPair{key : key, values: values, next: et}
}
func (et EmptyTyping) find(key mapset.Set) (map[Participant]LocalType, bool){
	return nil, false
}

func (et EmptyTyping) domain() []mapset.Set{
	return make([]mapset.Set,0,0)
}

func (et EmptyTyping) remove(key mapset.Set) Typing{
	return et
}

type TypingPair struct{
	key mapset.Set //should be a set of channels.
	values map[Participant]LocalType
	next Typing
}

func (tp TypingPair) remove(key mapset.Set) Typing{
	if tp.key.Equal(key){
		return tp.next
	}
	return TypingPair{key:tp.key, values:tp.values, next:tp.next.remove(key)}
}

func (tp TypingPair) add(key mapset.Set, values map[Participant]LocalType) Typing {
	return TypingPair{key: key, values: values, next:tp}
}

func (tp TypingPair) domain() []mapset.Set{
	return append(tp.next.domain(), tp.key)
}

func (tp TypingPair) find (key mapset.Set) (map[Participant]LocalType, bool){
	if tp.key.Equal(key){
		return tp.values, true
	}
	return tp.next.find(key)
}

func compatible(a, b Typing) bool {
	for _, channelsa := range a.domain(){
		for _, channelsb := range b.domain(){
			if !(channelsa.Intersect(channelsb).Equal(mapset.NewSet())){
				if !(channelsa.Equal(channelsb)){
					//then check that Typing1(s) o Typing2(s) is defined
					participantsa := mapset.NewSet()
					participantsb := mapset.NewSet()
					rangea , _ := a.find(channelsa)
					rangeb , _ := b.find(channelsb)
					for participant, _ := range rangea{
						participantsa.Add(participant)
					}
					for participant, _ := range rangeb{
						participantsb.Add(participant)
					}
					if !participantsa.Intersect(participantsb).Equal(mapset.NewSet()) {
						return false
					}
				}
			}
		}
	}
	return true
}

func composition(a, b Typing) Typing{
	// assumes compatibility. Verify before calling
	//composition as defined in 4.5 (Honda08)
	//if !compatible(a,b){
	//	return nil, errors.New("composition undefined by lack of compatibility")
	//}
	var ans Typing
	ans = EmptyTyping{}
	for _, dom := range a.domain(){
		values := make(map[Participant]LocalType)
		if domInA , ok := a.find(dom); ok{
			for p, lt := range domInA{
				values[p]=lt
			}
		}
		if domInB, ok := b.find(dom); ok{
			for p, lt := range domInB{
				values[p]=lt
			}
		} 
		ans = ans.add(dom, values)
	}
	for _, dom := range b.domain(){
		values := make(map[Participant]LocalType)
		if domInA , ok := a.find(dom); ok{
			//Then was in domain of a.
			continue
		}
		domInB, _ := b.find(dom)
		ans = ans.add(dom, domInB)
	}
	return ans
}


// SECTION Typecheck method definition.

func (rs Request) typecheck(names SortingNames, vars SortingVariables, gts GlobalTypeEnv) (Typing, error){
	//rule [Mcast] in fig 7
	//first, the easy part: to check that 2..n is actually all the participants in the set but one.
	type_participants := gts[rs.name].participants()
	if len(rs.others) != type_participants.Cardinality()-1 {
		return nil, errors.New("Malformed Request : [2..n] is not participants(G)-1")
	}
	for _, p := range rs.others{
		if !type_participants.Contains(p){
			return nil, errors.New(fmt.Sprintf("Malformed Request: participant %v does not participate in global type %+v",p,gts[rs.name]))
		}
	}
	//now find actual leader projection
	var participant Participant
	for _, participant = range rs.others{
		type_participants.Remove(participant)
	}

	participant = type_participants.ToSlice()[0].(Participant)
	
	
	typing, err := rs.P.typecheck(names, vars, gts)
	if err != nil {
		return nil, err
	}
	if projections, ok := typing.find(rs.channels); ok{
		if (rs.channels.Cardinality() != gts[rs.name].channels().Cardinality()) {
			return nil, errors.New("MCast Inconsistency on size of channels in s and G. Should be equal.")
		}
		if actual, err := gts[rs.name].project(participant); err == nil{
			if projection, ok := projections[participant]; err==nil{
				if !projection.equals(actual){
					return nil, errors.New(fmt.Sprintf("Projection is different from what was in the Typing of projections!, in particular, %+v != %+v", projection, actual))
				}
			} else {
				return nil, err
			}
		} else{
			return nil, err
		}
		//Note the end of the rule: it removes an element from Delta!
		return typing.remove(rs.channels), nil
	}
	return nil, errors.New("The typing did not contain the set of channels defined in MCast")
}

func (rs Accept) typecheck(envNames SortingNames, envVars SortingVariables, gts GlobalTypeEnv) (Typing, error){
	//rule [Macc] in fig 7
	// quite similar to [Mcast]
	//now find actual leader projection

	participant := rs.participant
	
	typing, err := rs.P.typecheck(envNames, envVars, gts)
	if err != nil {
		return nil, err
	}
	if projections, ok := typing.find(rs.channels); ok{
		if (rs.channels.Cardinality() != gts[rs.name].channels().Cardinality()) {
			return nil, errors.New("MCast Inconsistency on size of channels in s and G. Should be equal.")
		}
		if actual, err := gts[rs.name].project(participant); err == nil{
			if projection, ok := projections[participant]; ok{
				if !projection.equals(actual){
					return nil, errors.New(fmt.Sprintf("Projection is different from what was in the Typing of projections!, in particular, %+v != %+v", projection, actual))
				}
			} else {
				return nil, err
			}
		} else{
			return nil, err
		}
		//Note the end of the rule: it removes an element from Delta!
		return typing.remove(rs.channels), nil
	}
	return nil, errors.New("The typing did not contain the set of channels defined in MCast")
}

func (sv Output) typecheck(envNames SortingNames, envVars SortingVariables, gts GlobalTypeEnv) (Typing, error){
	// Rule [Send]
	sort := "bool"//sv.expression.typecheck()
	projections := make(map[Participant]LocalType)

	return EmptyTyping{}.add(Singleton(sv.s), append(make([]ProjectionType,0,1),
		ProjectionType{participant:channelsType[0].participant, T:SendLT{channel: sv.k,  value:expSorts, next:channelsType[0].T}})) , nil
}

func (rv Input) typecheck(envNames SortingNames, envVars SortingVariables, gts GlobalTypeEnv) (Typing, error){
	// Rule [Rcv]
	P, err := rv.P.typecheck(envNames, envVars, gts)
	if err != nil {
		return nil, err
	}

	for x , v:= range rv.names{
		envNames[v] = SingletonValue(rv.types[x])
	}

	channelsType, found := P.find(rv.s)
	if !found {
		return nil, errors.New("Didn't found a typing for the channels in the system.")
	}

	if len(channelsType) != 1 {
		return nil, errors.New("Channels Type in Send is not a singleton.")
	}

	for _, v := range rv.names{
		delete(envNames,v)
	}
	
	return P.add(rv.s, append(make([]ProjectionType,0,1),
		ProjectionType{participant:channelsType[0].participant, T:ReceiveLT{channel: rv.k,  value:rv.types, next:channelsType[0].T}})) , nil
}

func (sl Select) typecheck(envNames SortingNames, envVars SortingVariables, gts GlobalTypeEnv) (Typing, error){
	// Rule [SelectLabel]
	// This implementation needs a notion of subtyping that 
	P, err := sl.P.typecheck(envNames, envVars, gts)
	if err != nil {
		return nil, err
	}
	// This is how I should fix all the rest of the rules to do linear
	// addition to the content. I will have to fix this to make the
	// multiparty implementation work, but since it is not the goal of
	// this project, I will simply leave this as future work.

	// Get the last definition.

	var lastTyping TypingPair

	switch P.(type){
	case EmptyTyping:
		return nil, errors.New("Missing a typing in P for selection")
	case TypingPair:
		lastTyping = P.(TypingPair)
	}

	if len(lastTyping.values) != 1 {
		return nil, errors.New("Too many typings for selection's next Process")
	}

	if !lastTyping.values[0].equals(sl.T.branches[sl.label]) {
		return nil, errors.New("Type of the branch not equal to the type required for the continuing process on selection")
	}
	return TypingPair{key: lastTyping.key, values: append(make([]ProjectionType,0,1),ProjectionType{T:sl.T,participant:lastTyping.values[0].participant}), next: lastTyping.next}, nil
}

func (bl Branch) typecheck(envNames SortingNames, envVars SortingVariables, gts GlobalTypeEnv) (Typing, error){

	typings := make(map[string]LocalType)

	participant := make([]Participant,0,1)

	channels := make([][]Channel, 0 , 1)

	rest := make([]Typing, 0, 1)
	for label, program := range bl.branches{
		typing, err := program.typecheck(envNames, envVars, gts)
		if err != nil {
			return nil, err
		}
		pair := typing.(TypingPair)

		if len(pair.values)!= 1 {
			return nil, errors.New("More than one projectiontype for a branch")
		}
		if len(participant) < 1 {
			participant = append(participant, pair.values[0].participant)
			channels = append(channels, pair.key)
			rest = append(rest, pair.next)
		} else if participant[0] != pair.values[0].participant {
			return nil, errors.New("Different Participants in branch projections. weird.")
		}
		
		typings[label] = pair.values[0].T
	}

	return TypingPair{key: channels[0], values:append(make([]ProjectionType,0,1),
		ProjectionType{T:BranchingLT{channel:bl.channel,
			branches:typings}, participant:participant[0]}),  next:rest[0]}, nil

}

func (c Conditional) typecheck(envNames SortingNames, envVars SortingVariables, gts GlobalTypeEnv) (Typing, error){
	//Rule [If]
	if c.E.typecheck()!="bool"{
		return nil, errors.New(fmt.Sprintf("Conditional without boolean condition had instead %s", c.E))
	}
	typingThen, err := c.Then.typecheck(envNames, envVars, gts)
	if err != nil {
		return typingThen, err
	}

	typingElse, err := c.Else.typecheck(envNames, envVars, gts)
	if err != nil {
		return typingElse, err
	}

	// rest of method just checks equality of typings

	domainThen := typingThen.domain()
	domainElse := typingElse.domain()
	if len(domainThen) != len(domainElse) {
		return nil, errors.New("Domains of Branch Typings in Conditional are of different size")
	}
	// This has a huge overhead, but can be optimized after having a working version.

	for _, dom := range domainThen{
		domThen, ok := typingThen.find(dom)
		domElse, ok := typingElse.find(dom)
		if !ok {
			return nil, errors.New("Domain mismatch in conditional.")
		}

		if len(domElse) != len (domThen) {
			return nil, errors.New("Domain mismatch in conditional. different codomains..")
		}
		for x := range domThen {
			if !domThen[x].equals(domElse[x]){
				return nil, errors.New("Domain mismatch in conditional. different codomains.")
			}
		}
	}

	for _, dom := range domainElse{
		domElse, ok := typingElse.find(dom)
		domThen, ok := typingThen.find(dom)
		if !ok {
			return nil, errors.New("Domain mismatch in conditional.")
		}

		if len(domElse) != len (domThen) {
			return nil, errors.New("Domain mismatch in conditional. different codomains..")
		}
		for x := range domThen {
			if !domThen[x].equals(domElse[x]){
				return nil, errors.New("Domain mismatch in conditional. different codomains.")
			}
		}
	}	
	
	return typingThen, err
}
	

func (p Parallel) typecheck(envNames SortingNames, envVars SortingVariables, gts GlobalTypeEnv) (Typing, error) {
	// Rule [Conc]
	typingP, err := p.P.typecheck(envNames,envVars,gts)
	if err != nil{
		return typingP, err
	}
	typingQ, err := p.Q.typecheck(envNames,envVars,gts)
	if err != nil{
		return typingQ, err
	}
	if !compatible(typingP, typingQ){
		return nil, errors.New("Typings of parallel branches are not compatible")
	}
	return composition(typingP, typingQ), nil
}

func (i Inaction) typecheck(envNames SortingNames, envVars SortingVariables, gts GlobalTypeEnv) (Typing, error){
	// Rule [Inact]
	return EmptyTyping{},nil
}

func (h Hiding) typecheck(envNames SortingNames, envVars SortingVariables, gts GlobalTypeEnv) (Typing, error){
	// Rule [NRes]
	//This is a key difference from the paper.
	val, ok := gts[h.n]
	gts[h.n] = h.G
	ans, err := h.P.typecheck(envNames, envVars, gts)
	if ok {
		gts[h.n] = val
	} else {
		delete(gts,h.n)
	}
	return ans,err
}

func (vd Recursion) typecheck(envNames SortingNames, envVars SortingVariables, gts GlobalTypeEnv) (Typing, error){
	// Rule [Def]
	original_sorting_variable, sorting_variable_was_set := envVars[vd.identifier]

	//first extend envVars with the type for X
	envVars[vd.identifier] = vd.pv

	//Type Q (second premise of [Def])
	Q , err := vd.Q.typecheck(envNames, envVars, gts)

	for x :=range vd.argvars {
		envNames [vd.argvars[x]] = vd.argtypes[x]
	}

	P, err := vd.P.typecheck(envNames, envVars, gts)

	if err != nil {
		return nil, err
	}

	// Now we have checked all the predicates in the premises, we can go
	// and check validity of the typing in the definition of P with the
	// sorts defined in the definition of X.

	for k , s := range vd.s {
		//For each sortset verify that there is an actual typing in the
		//consequence. There is no restriction about it in the spec, but
		//it must exist.

		_, found := P.find(s)

		if !found {
			return nil, errors.New(fmt.Sprintf("Definition's P does not generate a typing for sortset %v (%+v)", k, s))
		}
	}

	//Cleanup for iterative maps.
	for _, x := range vd.argvars {
		delete(envNames,x)
	}

	if err != nil{
		return nil, err
	}
		
	if sorting_variable_was_set{
		envVars[vd.identifier] = original_sorting_variable
	} else {
		delete(envVars, vd.identifier)
	}

	//Now if everything went well, return exactly the typing for Q.

	return Q, nil
}

func (cp ProcessCall) typecheck(envNames SortingNames, envVars SortingVariables, gts GlobalTypeEnv) (Typing, error) {
	//Rule [Var]
	// premise
	var sorts SortSet
	sorts = make([]Sort,len(cp.expressions), len(cp.expressions))
	for x, exp := range cp.expressions{
		sorts[x] = exp.typecheck()
	}
	var envVal ProcessVariable
	var ok bool
	if envVal, ok = envVars[cp.identifier]; !ok{
		return nil, errors.New("Calling a process identifier that is not in scope.")
	}
	sort.Sort(sorts)
	if !equals(sorts, envVal.sorts){
		return nil, errors.New("Sort of expressions different from process variable's sorts in environment.")
	}
	if len(cp.channelSets) != len(envVal.types){
		return nil, errors.New("Not enough types in process variable to generate the typing. (or too many!)")
	}
	var ans Typing
	ans = EmptyTyping{}

	for x := range cp.channelSets{
		ans = ans.add(cp.channelSets[x], append(make([]ProjectionType,0,1),envVal.types[x]))
	}

	return ans, nil
}

func (tc TryCatch) typecheck(envNames SortingNames, envVars SortingVariables, gts GlobalTypeEnv) (Typing, error) {
	return nil, nil
}

func (t Throw) typecheck(envNames SortingNames, envVars SortingVariables, gts GlobalTypeEnv) (Typing, error) {
	return nil, nil
}

func (s Sequencing) typecheck(envNames SortingNames, envVars SortingVariables, gts GlobalTypeEnv) (Typing, error) {
	return nil, nil
}
