type {:finite} TyUnit;
const unique unit : TyUnit;
axiom (forall u:TyUnit :: u == unit);

type TySym;

type Cap N P V;
function cap <N, P, V>(N, P, V) : Cap N P V;
type CAPS = <N, P, V> [Cap N P V]bool ;

var CAPS : CAPS;
var ExcV : bool;

procedure with_capability<N, P, V>(S:Cap N P V);
  modifies CAPS;
  modifies ExcV;
  requires ExcV == false;

implementation with_capability<N, P, V>(S:Cap N P V)
{
  var u : TyUnit;
  if (CAPS[S] != true) {
    CAPS := CAPS[S := true];
    call u := f#1(unit);
    CAPS := CAPS[S := false];
  }
}

procedure require_capability<N, P, V>(S:Cap N P V) returns (r:TyUnit);
  modifies ExcV;
  requires ExcV == false;
  ensures r == unit;

implementation require_capability<N, P, V>(S:Cap N P V) returns (r:TyUnit)
{
  if (CAPS[S] == true) {
    r := unit;
  } else {
    ExcV := true;
  }
}

//////////////////////////////////////////////////////////////////////////

const unique TRANSFER : TySym;
const unique John : TySym;
const unique Jose : TySym;

procedure f#1(u:TyUnit) returns (r:TyUnit);
  modifies ExcV;
  requires ExcV == false;

implementation f#1(_:TyUnit) returns (r:TyUnit)
{
  var u : TyUnit;
  call u := require_capability(cap(TRANSFER, John, Jose));
  r := u;
}

