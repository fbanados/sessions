package multiparty

import (
	"fmt"
	"errors"
	"sort"
	"strings"
//	"reflect"
)

// This package follows the descriptions of Multiparty Session Types as
// discussed in Honda et al. 2008 (POPL). 

// GLOBAL TYPES

type GlobalType interface{
	isWellFormed() bool
	Prefixes() [][]Prefix
	participants() []Participant
	channels() ChannelSet
	project(p Participant) (LocalType, error)
	equals(t GlobalType) bool
}

type Participant string


func contains( p Participant, slice []Participant) bool{
	for _, element := range slice{
		if element == p {
			return true
		}
	}
	return false
}

func disjoint (a , b []Participant) bool{
	// Though this operator could be optimized, we are only dealing with the specification here.
	for _, x := range a {
		if contains(x, b) {
			return false
		}
	}
	for _, x := range b {
		if contains(x, a) {
			return false
		}
	}
	return true
}

func count(participants ParticipantSet) int{
	ans := 0
	sort.Sort(participants)
	if len(participants)<2 {
		return len(participants)
	}
	last := participants[0]
	ans = 1
	for _, x := range participants{
		if x != last{
			last= x
			ans++
		}
	}
	return ans
}

type Channel string
type Sort string

//implementing Sort's "sort" interface (to use go slices as sets)

type SortSet []Sort

func (ss SortSet) Len() int {
	return len(ss)
}

func (ss SortSet) Less(i, j int) bool{
	return ss[i] < ss[j]
}

func (ss SortSet) Swap(i, j int) {
	temp := ss[i]
	ss[i] = ss[j]
	ss[j] = temp
}

type ParticipantSet []Participant

func (ps ParticipantSet) Len() int{
	return len(ps)
}

func (ps ParticipantSet) Less(i, j int) bool{
	return ps[i] < ps[j]
}

func (ps ParticipantSet) Swap(i, j int) {
	temp:= ps[i]
	ps[i] = ps[j]
	ps[j] = temp
}

type ChannelSet []Channel

func (cs ChannelSet) Len() int {
	return len(cs)
}

func (cs ChannelSet) Less(i, j int) bool{
	return cs[i] < cs[j]
}

func (cs ChannelSet) Swap(i, j int) {
	temp := cs[i]
	cs[i] = cs[j]
	cs[j] = temp
}

func (cs ChannelSet) equals(b ChannelSet) bool{
	if cs.Len() != b.Len() {
		return false
	}
	for k := range cs {
		if cs[k] != b[k] {
			return false
		}
	}
	return true
}

func (slice ChannelSet) contains( p Channel) bool{
	for _, element := range slice{
		if element == p {
			return true
		}
	}
	return false
}

func (a ChannelSet) uniquify() ChannelSet{
	// Makes contents of the channelset actually unique.
	if a.Len()<1 {
		return a
	}
	var ans ChannelSet
	ans = append(make([]Channel,0,a.Len()),a[0])
	sort.Sort(ans)
	var last Channel
	last = a[0]
	for _, ch := range a {
		if ch != last{
			ans = append(ans, ch)
			last = ch
		}
	}
	return ans
	
}


func (a ChannelSet) disjoint (b ChannelSet) bool{
	// Though this operator could be optimized, we are only dealing with the specification here.
	for _, x := range a {
		if b.contains(x) {
			return false
		}
	}
	for _, x := range b {
		if a.contains(x) {
			return false
		}
	}
	return true
}




type Prefix struct{
	P1, P2 Participant
	channel Channel
}

func (p Prefix) participants() []Participant{
	ans :=make([]Participant,2,2)
	ans[0] = p.P1
	ans[1] = p.P2
	return ans
}

type ValueType struct{
	prefix Prefix
	value []Sort
	next GlobalType
}

func SingletonValue(s Sort) []Sort{
	ans := make([]Sort, 1, 1)
	ans[0]=s
	return ans
}

func equals(a, b SortSet) bool{
	if a.Len() != b.Len() {
		return false}
	sort.Sort(a)
	sort.Sort(b)
	for k := range a {
		if a[k] != b[k] {
			return false
		}
	}
	return true
}

func (t ValueType) isWellFormed() bool{
	return t.next.isWellFormed()
}

func (t ValueType) Prefixes() [][]Prefix{
	current :=append(make([]Prefix,0,1), t.prefix)
	ans := append(make([][]Prefix,0,1),current)
	for _, prefix := range t.next.Prefixes(){
		ans = append(ans, append(current, prefix...))
	}
	return ans
}

func (t ValueType) participants() []Participant{
	return append(t.prefix.participants(), t.next.participants()...)
}

func (t ValueType) project(p Participant) (LocalType, error){
	ans , err:= t.next.project(p)
	if err != nil {
		return nil, err
	} else if t.prefix.P1 == p {
		ans = LocalSendType{channel:t.prefix.channel, value:t.value, next: ans}
	} else if t.prefix.P2 == p {
		ans = LocalReceiveType{channel:t.prefix.channel, value:t.value, next:ans}
	}
	return ans, err
}

func (t ValueType) equals(g GlobalType) bool {
	switch g.(type){
	case ValueType:
		gt := g.(ValueType)
		return gt.prefix == t.prefix && equals(gt.value,t.value) && t.next.equals(gt.next)
	}	
	return false
}

func (t ValueType) channels() ChannelSet{
	return append(t.next.channels(),t.prefix.channel)
}


type BranchingType struct{
	prefix Prefix
	branches map[string] GlobalType
}

func (t BranchingType) channels() ChannelSet{
	ans := make([]Channel,0,0)
	for _, v := range t.branches{
		ans = append(ans,v.channels()...)
	}
	return append(ans,t.prefix.channel)
}

func (t BranchingType) Prefixes() [][]Prefix{
	base :=append(make([]Prefix,0,1),t.prefix)
	ans := make([][]Prefix,0,1)
	for _ , branch := range t.branches{
		branches := branch.Prefixes()
		for _, branch := range branches {
			ans = append(ans,append(base,branch...))
		}
	}
	return ans
}

func (t BranchingType) isWellFormed() bool{
	for _, value := range t.branches{
		if !value.isWellFormed(){
			return false
		}
	}
	return true
}

func (t BranchingType) participants() []Participant{
	ans := t.prefix.participants()
	for _, val := range t.branches {
		ans = append(ans, val.participants()...)
	}
	return ans
}

func (t BranchingType) project(p Participant) (LocalType, error){
	branches := make(map[string]LocalType)

	for key, value := range t.branches{
		candidate, err := value.project(p)
		if err != nil {
			return nil, err
		}
		branches[key] = candidate
	}

	unique := func(branches map[string]LocalType) bool{
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
		return LocalSelectionType{ channel:t.prefix.channel,branches: branches}, nil
	} else if t.prefix.P2 == p {
		return LocalBranchingType{ channel:t.prefix.channel, branches : branches}, nil
	} else if unique(branches) {
		for _, branch := range branches{
			return branch, nil
		}
	}
	return nil, errors.New("projection undefined")
}

func (t BranchingType) equals(g GlobalType) bool{
	switch g.(type){
	case BranchingType:
		gt := g.(BranchingType)
		for x := range t.branches {
			if !t.branches[x].equals(gt.branches[x]){
				return false
			}
		}
		return t.prefix == gt.prefix
	}
	return false
}

type ParallelType struct{
	a, b GlobalType
}

func (t ParallelType) channels() ChannelSet{
	return append(t.a.channels(),t.b.channels()...)
}

func (t ParallelType) Prefixes() [][]Prefix{
	return append(t.a.Prefixes(), t.b.Prefixes()...)
}

func (t ParallelType) isWellFormed() bool{
	return t.a.isWellFormed() && t.b.isWellFormed()
}

func (t ParallelType) participants() []Participant{
	return append(t.a.participants(), t.b.participants()...)
}

func (t ParallelType) project(p Participant) (LocalType, error) {
	if contains(p, t.a.participants()) {
		if contains(p, t.b.participants()) {
			return nil, errors.New("projection undefined")
		}
		return t.a.project(p)
	}
	if contains(p, t.b.participants()) {
		return t.b.project(p)
	}
	ans := LocalEndType{}
	return ans, nil
}

func (t ParallelType) equals(g GlobalType) bool{
	switch g.(type){
	case ParallelType:
		gt := g.(ParallelType)
		return t.a.equals(gt.a) && t.b.equals(gt.b)
	}
	return false
}

type NameType string

func (t NameType) isWellFormed() bool{
	return true
}

func (t NameType) Prefixes() [][]Prefix{
	return make([][]Prefix,0,0)
}

func (t NameType) participants() []Participant{
	return make([]Participant,0,0)
}

func (t NameType) project(p Participant) (LocalType, error){
	return LocalNameType(t), nil
}

func (t NameType) channels() ChannelSet{
	return make([]Channel, 0, 0)
}

func (t NameType)  equals(g GlobalType) bool{
	switch g.(type){
	case NameType:
		return t == g.(NameType)
	}
	return false
}

type RecursiveType struct{
	bind NameType
	body GlobalType
}

func (t RecursiveType) channels() ChannelSet{
	return t.body.channels()
}

func (t RecursiveType) isWellFormed() bool{
	return t.body.isWellFormed()
}

func (t RecursiveType) Prefixes() [][]Prefix{
	return t.body.Prefixes()
}

func (t RecursiveType) participants() []Participant{
	return t.body.participants()
}

func (t RecursiveType) project(p Participant) (LocalType, error){
	body, err := t.body.project(p)
	if err != nil {
		return nil, err
	}
	return LocalRecursiveType{bind:LocalNameType(t.bind),body:body}, nil
}

func (t RecursiveType)  equals(g GlobalType) bool{
	switch g.(type){
	case RecursiveType:
		gt := g.(RecursiveType)
		return t.bind.equals(gt.bind) && t.body.equals(gt.body)
	}
	return false
}

type EndType struct{}

func (t EndType) isWellFormed() bool{
	return true
}

func (t EndType) channels() ChannelSet{
	return make([]Channel, 0, 0)
}
func (t EndType) Prefixes() [][]Prefix{
	return make([][]Prefix,0,0)
}

func (t EndType) participants() []Participant{
	return make([]Participant, 0, 0)
}

func (t EndType) project(p Participant) (LocalType, error){
	return LocalEndType(t), nil
}

func (t EndType)  equals(g GlobalType) bool{
	switch g.(type){
	case EndType:
		return true
	}
	return false
}

func linear(original_gt GlobalType) bool{
	gt := unfold(original_gt, make(map[NameType] GlobalType))
	return linearInternal(gt, make([]Prefix,0,0))
}

//Definition 4.2
func coherent(original_gt GlobalType) bool{
	if !linear(original_gt) {
		return false
	}
	gt := unfold(original_gt, make(map[NameType] GlobalType))
	for _, p := range gt.participants() {
		_ , err := gt.project(p)
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
	/*
overall implementation idea:
since we already have unwrapped, we only need to locally check and there's a finite amount of nodes to explore (we already removed the cycles via unfold)

- 
*/
	switch gt.(type){
	case ValueType:
		t := gt.(ValueType)
		filtered_lessthan :=filter_shared_channel(lessthan, t.prefix)
		if !(InputDependency(filtered_lessthan, t.prefix) && OutputDependency(filtered_lessthan, t.prefix)){
			fmt.Printf("ERROR: Failed to collect dependencies for ValueType %+v\n", t)
			return false
		}
		linearInternal(t.next,append(lessthan,t.prefix))
	case BranchingType:
		t := gt.(BranchingType)
		filtered_lessthan := filter_shared_channel(lessthan, t.prefix)
		if !(InputDependency(filtered_lessthan, t.prefix) && OutputDependency(filtered_lessthan, t.prefix)){
			fmt.Printf("ERROR: Failed to collect dependencies for BranchingType %+v\n", t)
			return false
		}
		new_lessthan:=append(lessthan, t.prefix)
		for _, value := range t.branches {
			if ! linearInternal(value, new_lessthan) {
				return false
			}
		}
	case ParallelType:
		t := gt.(ParallelType)
		for _, prefixes := range t.b.Prefixes() {
			//fmt.Printf("DEBUG: Checking Parallel linearity with %+v and %+v\n",lessthan, prefixes)
			if ! linearInternal(t.a, append(lessthan,prefixes...)){
				return false
			}
		}
		for _, prefixes := range t.a.Prefixes() {
			if ! linearInternal(t.b, append(lessthan,prefixes...)) {
				return false
			}
		}
	case RecursiveType:
		t := gt.(RecursiveType)
		//fmt.Printf("DEBUG: Entering body of type %+v\n", t)
		return linearInternal(t.body, lessthan)
	case NameType:
	case EndType:
	}
	return true
}

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

func unfold(gt GlobalType, env map[NameType] GlobalType) GlobalType{
	switch gt.(type){
	case ValueType:
		t := gt.(ValueType)
		return ValueType{prefix: t.prefix, value: t.value, next:unfold(t.next,env)}
	case BranchingType:
		t := gt.(BranchingType)
		branches := make(map[string]GlobalType)
		for key, value := range t.branches{
			branches[key] = unfold(value, env)
		}
		return BranchingType{prefix: t.prefix, branches:branches}
	case ParallelType:
		t := gt.(ParallelType)
		return ParallelType{a: unfold(t.a,env), b: unfold(t.b, env)}
	case RecursiveType:
		t := gt.(RecursiveType)
		if val, ok := env[t.bind]; ok {
			if val != t {
				//name hiding!
				old_val := val
				env[t.bind] = t
				ans := RecursiveType{bind:t.bind, body:unfold(t.body, env)}
				env[t.bind] = old_val
				return ans
			} else {
				//I already unfolded once. then return (avoid infinite loop)
				return t
			}
		}
		env[t.bind] = t
		return RecursiveType{bind:t.bind, body:unfold(t.body, env)}
	case NameType:
		t := gt.(NameType)
		if val, ok := env[t]; ok {
			return val
		}
		return t
	case EndType:
		return gt
	}
	return nil
}

// LOCAL TYPES

type LocalType interface{
	equals(t LocalType) bool
}

type ProjectionType struct{
	// Originall, Type @ participant
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

func findProjection(participant Participant, projections []ProjectionType) (ProjectionType, error){
	var ans ProjectionType
	for _, proj := range projections{
		if participant == proj.participant {
			return proj, nil
		}
	}
	return ans, errors.New(fmt.Sprintf("Could not find projection for participant %+v in set %+v", participant, projections))
}


type LocalSendType struct{
	channel Channel
	value []Sort
	next LocalType
}

func (t LocalSendType) equals(l LocalType) bool{
	switch l.(type){
	case LocalSendType:
		lt := l.(LocalSendType)
		return t.channel == lt.channel && equals(t.value, lt.value) && t.next.equals(lt.next)
	}
	return false
}

type LocalReceiveType struct{
	channel Channel
	value []Sort
	next LocalType
}

func (t LocalReceiveType) equals(l LocalType) bool{
	switch l.(type){
	case LocalReceiveType:
		lt := l.(LocalReceiveType)
		return t.channel == lt.channel && equals(t.value, lt.value) && t.next.equals(lt.next)
	}
	return false
}

type LocalSelectionType struct{
	// k \oplus
	channel Channel
	branches map[string] LocalType
}

func (t LocalSelectionType) equals(l LocalType) bool{
	switch l.(type){
	case LocalSelectionType:
		lt := l.(LocalSelectionType)
		for k := range t.branches{
			if !t.branches[k].equals(lt.branches[k]){
				return false
			}
		}
		return t.channel == lt.channel
	}
	return false
}

type LocalBranchingType struct{
	// k &
	channel Channel
	branches map[string] LocalType
}


func (t LocalBranchingType) equals(l LocalType) bool{
	switch l.(type){
	case LocalBranchingType:
		lt := l.(LocalBranchingType)
		for k := range t.branches{
			if !t.branches[k].equals(lt.branches[k]){
				return false
			}
		}
		return t.channel == lt.channel
	}
	return false
}

type LocalNameType string

func (t LocalNameType) equals(l LocalType) bool{
	switch l.(type){
	case LocalNameType:
		return t == l.(LocalNameType)
	}
	return false
}

type LocalRecursiveType struct{
	bind LocalNameType
	body LocalType
}

func (t LocalRecursiveType) equals(l LocalType) bool{
	switch l.(type){
	case LocalRecursiveType:
		lt := l.(LocalRecursiveType)
		return t.bind.equals(lt.bind) && t.body.equals(lt.body)
	}
	return false
}

type LocalEndType struct{}

func (t LocalEndType) equals(l LocalType) bool{
	switch l.(type){
	case LocalEndType:
		return true
	}
	return false
}

// end of local types and definition of projection.



// PROGRAMMING PHRASES (SYNTAX)

type SortingNames map[string]SortSet

type ProcessVariable struct{
	sorts []Sort
	types []ProjectionType
}

type SortingVariables map[string]ProcessVariable

type GlobalTypeEnv map[string]GlobalType

type Typing interface{
	find(key []Channel) ([]ProjectionType, bool)
	domain() []ChannelSet
	add(key []Channel, values []ProjectionType) Typing
	remove(key []Channel) Typing
}
	
type EmptyTyping struct{}

func (et EmptyTyping) add(key []Channel, values []ProjectionType) Typing {
	return TypingPair{key : key, values: values, next: et}
}
func (et EmptyTyping) find(key []Channel) ([]ProjectionType, bool){
	return nil, false
}

func (et EmptyTyping) domain() []ChannelSet{
	return make([]ChannelSet,0,0)
}

func (et EmptyTyping) remove(key []Channel) Typing{
	return et
}

type TypingPair struct{
	key ChannelSet
	values []ProjectionType
	next Typing
}

func (tp TypingPair) remove(key []Channel) Typing{
	if tp.key.equals(key){
		return tp.next
	}
	return TypingPair{key:tp.key, values:tp.values, next:tp.next.remove(key)}
}

func (tp TypingPair) add(key []Channel, values []ProjectionType) Typing {
	return TypingPair{key: key, values: values, next:tp}
}

func (tp TypingPair) domain() []ChannelSet{
	return append(tp.next.domain(), tp.key)
}

func (tp TypingPair) find (key []Channel) ([]ProjectionType, bool){
	if len(tp.key) == len(key){
		eq := true
		for k := range key {
			if !(tp.key[k]==key[k]){
				eq = false
				break
			}
		}
		if eq {
			return tp.values, true
		}
	}
	return tp.next.find(key)
}


func compatible(a, b Typing) bool {
	for _, channelsa := range a.domain(){
		for _, channelsb := range b.domain(){
			if !(channelsa.disjoint(channelsb)){
				if !(channelsa.equals(channelsb)){
					//then check that Typing1(s) o Typing2(s) is defined
					participantsa := make([]Participant,0,0)
					participantsb := make([]Participant,0,0)
					rangea , _ := a.find(channelsa)
					rangeb , _ := b.find(channelsb)
					for _, typesa := range rangea{
						participantsa = append(participantsa, typesa.participant)
					}
					for _, typesb := range rangeb{
						participantsb = append(participantsb, typesb.participant)
					}
					if !disjoint(participantsa, participantsb) {
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
	//composition as defined in 4.5
	//if !compatible(a,b){
	//	return nil, errors.New("composition undefined by lack of compatibility")
	//}
	var ans Typing
	ans = EmptyTyping{}
	for _, dom := range a.domain(){
		domInA , _ := a.find(dom)
		if domInB, ok := b.find(dom); ok{
			ans = ans.add(dom, append(domInA,domInB...))
		} else{
			ans = ans.add(dom, domInA)
		}
	}
	for _, dom := range b.domain(){
		domInB , _ := b.find(dom)
		if domInA, ok := a.find(dom); ok{
			ans = ans.add(dom, append(domInA, domInB...))
		} else {
			ans = ans.add(dom, domInA)
		}
	}
	return ans
}

type Program interface{
	typecheck(names SortingNames, vars SortingVariables, gts GlobalTypeEnv) (Typing, error)
}
type Process string
type Exp string
//Follow the "type:exp" style of strings. This is result of typechecking expressions in a lame way.

func (e Exp) eval(){
	fmt.Printf("I should evaluate this expression, which should return a %s\n",e)
}
func (e Exp) typecheck() Sort{
	split := strings.Split(string(e),":")
	return Sort(split[0])
}

type LocalName string

// Structs that shall be a program

type RequestSession struct{
	//\bar{a}[2..n](\~s).P is a program and a is a globaltype.  The participants set
	// contains all participants "but the leader" (or starter, which
	// these guys name 1. crystal clear (not).
	participants []Participant
	a string // should be a name
	s ChannelSet
	P Program
}

func (rs RequestSession) typecheck(names SortingNames, vars SortingVariables, gts GlobalTypeEnv) (Typing, error){
	//rule [Mcast] in fig 7
	//first, the easy part: to check that 2..n is actually all the participants in the set but one.
	type_participants := gts[rs.a].participants()
	if count(rs.participants) != count(type_participants) {
		return nil, errors.New("Malformed RequestSession : [2..n] is not participants(G)-1")
	}
	for _, p := range rs.participants{
		if !contains(p,type_participants){
			return nil, errors.New(fmt.Sprintf("Malformed RequestSession: participant %v does not participate in global type %+v",p,gts[rs.a]))
		}
	}
	//now find actual leader projection
	var participant Participant
	for _, participant = range type_participants{
		if !contains(participant,rs.participants){
			break
		}
	}
	
	typing, err := rs.P.typecheck(names, vars, gts)
	if err != nil {
		return nil, err
	}
	if projections, ok := typing.find(rs.s); ok{
		if (rs.s.uniquify().Len() != gts[rs.a].channels().uniquify().Len()) {
			return nil, errors.New("MCast Inconsistency on size of channels in s and G. Should be equal.")
		}
		if actual, err := gts[rs.a].project(participant); err == nil{
			if projection, err := findProjection(participant,projections); err==nil{
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
		return typing.remove(rs.s), nil
	}
	return nil, errors.New("The typing did not contain the set of channels defined in MCast")
}

type AcceptSession struct{
	//a[p](\~s).P
	a string //which should be a name :)
	p Participant
	s ChannelSet
	P Program
}

func (rs AcceptSession) typecheck(envNames SortingNames, envVars SortingVariables, gts GlobalTypeEnv) (Typing, error){
	//rule [Macc] in fig 7
	// quite similar to [Mcast]
	//now find actual leader projection

	participant := rs.p
	
	typing, err := rs.P.typecheck(envNames, envVars, gts)
	if err != nil {
		return nil, err
	}
	if projections, ok := typing.find(rs.s); ok{
		if (rs.s.uniquify().Len() != gts[rs.a].channels().uniquify().Len()) {
			return nil, errors.New("MCast Inconsistency on size of channels in s and G. Should be equal.")
		}
		if actual, err := gts[rs.a].project(participant); err == nil{
			if projection, err := findProjection(participant,projections); err==nil{
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
		return typing.remove(rs.s), nil
	}
	return nil, errors.New("The typing did not contain the set of channels defined in MCast")
}


type SendValue struct{
	//s_k!<\~e>;P
	s ChannelSet
	k Channel
	expressions []Exp
	P Program
}

func (sv SendValue) typecheck(envNames SortingNames, envVars SortingVariables, gts GlobalTypeEnv) (Typing, error){
	// Rule [Send]
	P, err := sv.P.typecheck(envNames, envVars, gts)
	if err != nil {
		return nil, err
	}

	expSorts := make([]Sort, len(sv.expressions), len(sv.expressions))

	for x , v:= range sv.expressions{
		expSorts[x] = v.typecheck()
	}

	channelsType, found := P.find(sv.s)
	if !found {
		return nil, errors.New("Didn't found a typing for the channels in the system.")
	}

	if len(channelsType) != 1 {
		return nil, errors.New("Channels Type in Send is not a singleton.")
	}
		
	return P.add(sv.s, append(make([]ProjectionType,0,1),
		ProjectionType{participant:channelsType[0].participant, T:LocalSendType{channel: sv.k,  value:expSorts, next:channelsType[0].T}})) , nil
}

type ReceiveValue struct{
	//s_k?(\~x);P
	s ChannelSet
	k Channel
	names []string //\~x
	types SortSet
	P Program
}

func (rv ReceiveValue) typecheck(envNames SortingNames, envVars SortingVariables, gts GlobalTypeEnv) (Typing, error){
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
		ProjectionType{participant:channelsType[0].participant, T:LocalReceiveType{channel: rv.k,  value:rv.types, next:channelsType[0].T}})) , nil
}


// We do not consider [Deleg] nor [SRec, because we do not want to send session types through channels (yet). 

type SelectLabel struct{
	//s_k <| l; P
	channel Channel //k
	label string
	T LocalSelectionType //This is to ease typing.
	P Program
}

func (sl SelectLabel) typecheck(envNames SortingNames, envVars SortingVariables, gts GlobalTypeEnv) (Typing, error){
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

type BranchLabel struct{
	// s |> {li : Pi} i \in I
	channel Channel//s
	branches map[string]Program
}

func (bl BranchLabel) typecheck(envNames SortingNames, envVars SortingVariables, gts GlobalTypeEnv) (Typing, error){

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
		ProjectionType{T:LocalBranchingType{channel:bl.channel,
			branches:typings}, participant:participant[0]}),  next:rest[0]}, nil

}

type Conditional struct{
	//if e then P else Q
	E Exp
	Then Program
	Else Program
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
	

type Parallel struct{
	P Program
	Q Program
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

type Inaction struct{
	//0
}

func (i Inaction) typecheck(envNames SortingNames, envVars SortingVariables, gts GlobalTypeEnv) (Typing, error){
	// Rule [Inact]
	return EmptyTyping{},nil
}

type Hiding struct{
	//(\eta n) P
	n string // name to hide :)
	G GlobalType // type to hide :)
	P Program
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

type VarDef struct{
	//def X(~x~s1...~sn) in P, but I add the sorts. Why? Because the
	//type system is specification oriented and not implementation
	//oriented and I am not going to nondeterministically choose the
	//correct set of sorts that I need to add for each variable.

	// We make a variant which is type annotated. Easier to typecheck.

	//def X:typevar (\~x,\~s1...\~sn) = P in Q
	
	identifier string //X
	argvars []string //\~x
	argtypes []SortSet //types for \~x. Not on the original spec, but to simplify typing.
 	pv ProcessVariable //Type for X
	s []ChannelSet
	P, Q Program
}

func (vd VarDef) typecheck(envNames SortingNames, envVars SortingVariables, gts GlobalTypeEnv) (Typing, error){
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

type CallProcess struct{
	//X<\~e,\~s>
	identifier string//X
	expressions []Exp//~e
	channelSets []ChannelSet//~s
}

func (cp CallProcess) typecheck(envNames SortingNames, envVars SortingVariables, gts GlobalTypeEnv) (Typing, error) {
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

