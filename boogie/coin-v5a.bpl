type Any;                       // The set of all Pact values.
const unique Void : Any;

type Ref; // Set of all Whiley references

function Ref#box(Ref) returns (Any);
function Ref#unbox(Any) returns (Ref);
function Ref#is(v : Any) returns (bool) {
  (exists r:Ref :: Ref#box(r) == v)
}
axiom (forall r:Ref :: Ref#unbox(Ref#box(r)) == r);
axiom (forall r:Ref :: Ref#box(r) != Void);

const unique Ref#Empty : [Ref]Any;

type Type;
const unique False : Type;

// Meta type test
function Type#is([Ref]Any, Type, Any) returns (bool);

const unique Type#U : Type;     // Unit meta type
const unique Type#I : Type;     // Int meta type
const unique Type#D : Type;     // Decimal meta type
const unique Type#S : Type;     // String meta type

type Unit;
const unique Unit : Unit;

function Unit#is(v:Any) returns (bool) {
  (Unit#box(Unit) == v)
}
function Unit#unbox(Any) returns (Unit);
function Unit#box(Unit) returns (Any);

axiom (Unit#unbox(Unit#box(Unit)) == Unit);
axiom (Unit#box(Unit) != Void);

// Unit meta axiom
axiom (forall HEAP:[Ref]Any,v:Any :: Type#is(HEAP,Type#I,v) <==> Unit#is(v));

function Int#is(v:Any) returns (bool) {
  (exists i:int :: Int#box(i) == v)
}
function Int#unbox(Any) returns (int);
function Int#box(int) returns (Any);

axiom (forall i:int :: Int#unbox(Int#box(i)) == i);
axiom (forall i:int :: Int#box(i) != Void);

// Int meta axiom
axiom (forall HEAP:[Ref]Any,v:Any :: Type#is(HEAP,Type#I,v) <==> Int#is(v));

function Array#box([int]Any) returns (Any);
function Array#unbox(Any) returns ([int]Any);
function Array#is(v:Any) returns (bool) {
  (exists a:[int]Any :: Array#box(a) == v)
}
axiom (forall i:[int]Any :: Array#unbox(Array#box(i))==i);
axiom (forall a:[int]Any :: Array#box(a) != Void);

// Helper constraining index to be in-bounds
function Array#in(a : [int]Any, i : int) returns (bool) {
  (i >= 0) && (i < Array#Length(a))
}

// Extraction for array length
function Array#Length([int]Any) returns (int);

// Length of an array is non-negative
axiom (forall a:[int]Any :: 0 <= Array#Length(a));

// Updates don’t affect array length
axiom (forall a:[int]Any,i:int,v:Any ::
  (v != Void && Array#in(a,i))
   ==> (Array#Length(a) == Array#Length(a[i:=v])));

// Construct (empty) array literal of size n
function Array#Empty(int) returns ([int]Any);

// Fix out-of-bounds indices for array literal

axiom (forall l:int,i:int ::
  (i < 0 || l <= i) ==> (Array#Empty(l)[i] == Void));

// Fix in-bounds indices for array literal
axiom (forall l:int,i:int ::
  (0 <= i && i < l) ==> (Array#Empty(l)[i] != Void));

// Array length must match length of array literal
axiom (forall a:[int]Any,l:int ::
  (0 <= l && Array#Empty(l)==a) ==> (Array#Length(a)==l));

function Array#Generator(Any, int) returns ([int]Any);

// Every element of array generator matches given value
axiom (forall v:Any,l:int,i:int ::
  (0<=i && i<l && v!=Void) ==> Array#Generator(v,l)[i]==v);

// Fix out-of-bounds indices for array generator
axiom (forall v:Any,l:int,i:int ::
  (i < 0 || l <= i) ==> (Array#Generator(v,l)[i] == Void));

// Array length must match length of array generator
axiom (forall a:[int]Any,v:Any,l:int ::
  (0<=l && Array#Generator(v,l)==a) ==> Array#Length(a)==l);

type Lambda; // Set of all lambda values

function Lambda#box(Lambda) returns (Any);
function Lambda#unbox(Any) returns (Lambda);
function Lambda#is(v : Any) returns (bool) {
  (exists l:Lambda :: Lambda#box(l) == v)
}

axiom (forall l:Lambda :: Lambda#unbox(Lambda#box(l))==l);
axiom (forall l:Lambda :: Lambda#box(l) != Void);

type CapName;

type CapSigField;
const unique $paramTy : CapSigField;
const unique $valueTy : CapSigField;

function CapSig#box([CapSigField]Type) returns (Type);
function CapSig#unbox(Type) returns ([CapSigField]Type);
function CapSig#is(v : Type) returns (bool) {
  (exists r:[CapSigField]Type :: CapSig#box(r) == v)
}
axiom (forall i:[CapSigField]Type :: CapSig#unbox(CapSig#box(i)) == i);
axiom (forall r:[CapSigField]Type :: CapSig#box(r) != False);

const unique CapSig#Empty : [CapSigField]Type;

// Every field in an empty record holds False
axiom (forall f:CapSigField :: CapSig#Empty[f] == False);

type CapField;
const unique $param : CapField;
const unique $value : CapField;

function Cap#box([CapField]Any) returns (Any);
function Cap#unbox(Any) returns ([CapField]Any);
function Cap#is(S:Type, v:Any) returns (bool) {
  (exists r:[CapField]Any :: Cap#box(r) == v) &&
  (exists s:[CapSigField]Type :: CapSig#box(s) == S)
}
axiom (forall i:[CapField]Any :: Cap#unbox(Cap#box(i)) == i);
axiom (forall r:[CapField]Any :: Cap#box(r) != Void);

const unique Cap#Empty : [CapField]Any;

// Every field in an empty record holds Void
axiom (forall f:CapField :: Cap#Empty[f] == Void);
axiom (forall HEAP:[Ref]Any,S:Type,v:Any ::
  Cap#is(S, v) ==>
    Type#is(HEAP,CapSig#unbox(S)[$paramTy],Cap#unbox(v)[$param]));
axiom (forall HEAP:[Ref]Any,S:Type,v:Any ::
  Cap#is(S, v) ==>
    Type#is(HEAP,CapSig#unbox(S)[$valueTy],Cap#unbox(v)[$value]));

var CAPS : Any;
var ExcV : bool;

procedure with_capability(S : Type, c : Any) returns (r : Unit);
  requires Cap#is(S, c);
  ensures r == Unit;

procedure require_capability(S : Type, c : Any) returns (r : Unit);
  requires Cap#is(S, c);
  ensures r == Unit;

// function enforce-one(node: ref): bool {}
