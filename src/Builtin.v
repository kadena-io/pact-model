Require Export
  Ty
  Exp.

Open Scope Ty_scope.

Inductive Builtin : Ty → Ty → Set :=
  (* IntOps *)
  (* Integer Add *)
  | AddInt           : Builtin (ℤ × ℤ) ℤ
  (* Int Num functions *)
  | SubInt           : Builtin (ℤ × ℤ) ℤ
  | DivInt           : Builtin (ℤ × ℤ) ℤ
  | MulInt           : Builtin (ℤ × ℤ) ℤ
  | NegateInt        : Builtin (ℤ × ℤ) ℤ
  | AbsInt           : Builtin (ℤ × ℤ) ℤ
  (* Int fractional *)
  | ExpInt           : Builtin (ℤ × ℤ) ℤ
  | LnInt            : Builtin (ℤ × ℤ) ℤ
  | SqrtInt          : Builtin (ℤ × ℤ) ℤ
  | LogBaseInt       : Builtin (ℤ × ℤ) ℤ
  (* General int ops *)
  | ModInt           : Builtin (ℤ × ℤ) ℤ
  | BitAndInt        : Builtin (ℤ × ℤ) ℤ
  | BitOrInt         : Builtin (ℤ × ℤ) ℤ
  | BitXorInt        : Builtin (ℤ × ℤ) ℤ
  | BitShiftInt      : Builtin (ℤ × ℤ) ℤ
  | BitComplementInt : Builtin (ℤ × ℤ) ℤ
  (* Int show instance *)
  | ShowInt          : Builtin (ℤ × ℤ) ℤ
  (* Int Equality *)
  | EqInt            : Builtin (ℤ × ℤ) ℤ
  | NeqInt           : Builtin (ℤ × ℤ) ℤ
  | GTInt            : Builtin (ℤ × ℤ) ℤ
  | GEQInt           : Builtin (ℤ × ℤ) ℤ
  | LTInt            : Builtin (ℤ × ℤ) ℤ
  | LEQInt           : Builtin (ℤ × ℤ) ℤ
  (* If *)
  | IfElse           : Builtin (ℤ × ℤ) ℤ
  (* Decimal ops *)
  (* Decimal add *)
  | AddDec           : Builtin (ℤ × ℤ) ℤ
  (* Decimal num *)
  | SubDec           : Builtin (ℤ × ℤ) ℤ
  | DivDec           : Builtin (ℤ × ℤ) ℤ
  | MulDec           : Builtin (ℤ × ℤ) ℤ
  | NegateDec        : Builtin (ℤ × ℤ) ℤ
  | AbsDec           : Builtin (ℤ × ℤ) ℤ
  (* Decimal rounding ops *)
  | RoundDec         : Builtin (ℤ × ℤ) ℤ
  | CeilingDec       : Builtin (ℤ × ℤ) ℤ
  | FloorDec         : Builtin (ℤ × ℤ) ℤ
  (* Decimal rounding ops *)
  | ExpDec           : Builtin (ℤ × ℤ) ℤ
  | LnDec            : Builtin (ℤ × ℤ) ℤ
  | LogBaseDec       : Builtin (ℤ × ℤ) ℤ
  | SqrtDec          : Builtin (ℤ × ℤ) ℤ
  (* Decimal Show *)
  | ShowDec          : Builtin (ℤ × ℤ) ℤ
  (* Decimal Equality *)
  | EqDec            : Builtin (ℤ × ℤ) ℤ
  | NeqDec           : Builtin (ℤ × ℤ) ℤ
  (* Decimal ord *)
  | GTDec            : Builtin (ℤ × ℤ) ℤ
  | GEQDec           : Builtin (ℤ × ℤ) ℤ
  | LTDec            : Builtin (ℤ × ℤ) ℤ
  | LEQDec           : Builtin (ℤ × ℤ) ℤ
  (* Bool Comparisons *)
  | AndBool          : Builtin (ℤ × ℤ) ℤ
  | OrBool           : Builtin (ℤ × ℤ) ℤ
  | NotBool          : Builtin (ℤ × ℤ) ℤ
  (* other bool ops *)
  | EqBool           : Builtin (ℤ × ℤ) ℤ
  | NeqBool          : Builtin (ℤ × ℤ) ℤ
  | ShowBool         : Builtin (ℤ × ℤ) ℤ
  (* String Equality *)
  | EqStr            : Builtin (ℤ × ℤ) ℤ
  | NeqStr           : Builtin (ℤ × ℤ) ℤ
  (* String Ord *)
  | GTStr            : Builtin (ℤ × ℤ) ℤ
  | GEQStr           : Builtin (ℤ × ℤ) ℤ
  | LTStr            : Builtin (ℤ × ℤ) ℤ
  | LEQStr           : Builtin (ℤ × ℤ) ℤ
   (* String Add *)
  | AddStr           : Builtin (ℤ × ℤ) ℤ
  (* String ListLike *)
  | ConcatStr        : Builtin (ℤ × ℤ) ℤ
  | DropStr          : Builtin (ℤ × ℤ) ℤ
  | TakeStr          : Builtin (ℤ × ℤ) ℤ
  | LengthStr        : Builtin (ℤ × ℤ) ℤ
  | ReverseStr       : Builtin (ℤ × ℤ) ℤ
  (* String Show *)
  | ShowStr          : Builtin (ℤ × ℤ) ℤ
  (* Object equality *)
  | EqObj            : Builtin (ℤ × ℤ) ℤ
  | NeqObj           : Builtin (ℤ × ℤ) ℤ
  (* List Equality *)
  | EqList           : Builtin (ℤ × ℤ) ℤ
  | NeqList          : Builtin (ℤ × ℤ) ℤ
  (* List Ord *)
  | GTList           : Builtin (ℤ × ℤ) ℤ
  | GEQList          : Builtin (ℤ × ℤ) ℤ
  | LTList           : Builtin (ℤ × ℤ) ℤ
  | LEQList          : Builtin (ℤ × ℤ) ℤ
  (* List Show *)
  | ShowList         : Builtin (ℤ × ℤ) ℤ
  (* List Add *)
  | AddList          : Builtin (ℤ × ℤ) ℤ
  (* ListLike List *)
  | TakeList         : Builtin (ℤ × ℤ) ℤ
  | DropList         : Builtin (ℤ × ℤ) ℤ
  | LengthList       : Builtin (ℤ × ℤ) ℤ
  | ConcatList       : Builtin (ℤ × ℤ) ℤ
  | ReverseList      : Builtin (ℤ × ℤ) ℤ
  (* Misc list ops *)
  | FilterList       : Builtin (ℤ × ℤ) ℤ
  | DistinctList     : Builtin (ℤ × ℤ) ℤ
  | MapList          : Builtin (ℤ × ℤ) ℤ
  | ZipList          : Builtin (ℤ × ℤ) ℤ
  | FoldList         : Builtin (ℤ × ℤ) ℤ
  (* Unit ops *)
  | EqUnit           : Builtin (ℤ × ℤ) ℤ
  | NeqUnit          : Builtin (ℤ × ℤ) ℤ
  | ShowUnit         : Builtin (ℤ × ℤ) ℤ
  (* Others *)
  | Enforce          : Builtin (ℤ × ℤ) ℤ
  | EnforceOne       : Builtin (ℤ × ℤ) ℤ
  | Enumerate        : Builtin (ℤ × ℤ) ℤ
  | EnumerateStepN   : Builtin (ℤ × ℤ) ℤ.
