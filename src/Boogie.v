Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.
Require Import Pact.Lib.
Require Import Pact.Data.MapSet.
Require Import Coq.Classes.RelationClasses.

(** Abstract syntax for the Boogie intermediate language.

    This representation is dependently-typed to ensure correct construction. *)

Module Boogie.

Import ListNotations.

Definition Id := string.

Inductive Ty : Set :=
  | TAtom : TypeAtom → Ty
  | TMap : MapType → Ty
  | TId : Id → TypeCtorArgs → Ty

with TypeAtom : Set :=
  | TBool
  | TInt
  | TReal

with MapType : Set :=
  | Mp : TypeArgs → list Ty → Ty → MapType

with TypeArgs : Set :=
  | ArgsNone : TypeArgs
  | Args : list Id → TypeArgs
  | ArgsAng : list Id → TypeArgs

with TypeCtorArgs : Set :=
  | CtorNone : TypeCtorArgs
  | CtorAtom : TypeAtom → TypeCtorArgs → TypeCtorArgs
  | CtorId : Id → TypeCtorArgs → TypeCtorArgs
  | CtorMap : MapType → TypeCtorArgs.

Definition nullaryType (n : Id) : Ty := TId n CtorNone.
Definition noType : Ty := nullaryType "NoType"%string.

Record NewType : Set := {
  tId : Id;
  tArgs : list Id;
  tValue : option Ty
}.

Definition ParentEdge : Set := bool * Id.
Definition ParentInfo : Set := option (list ParentEdge).

Definition FArg : Set := option Id * Ty.
Definition dummyFArg : Id := ""%string.

Inductive UnOp : Ty → Ty → Set :=
  | Not : UnOp (TAtom TBool) (TAtom TBool)
  | NegI : UnOp (TAtom TInt) (TAtom TInt)
  | NegR : UnOp (TAtom TReal) (TAtom TReal).

Inductive BinOp : Ty → Ty → Ty → Set :=
  | And     : BinOp (TAtom TBool) (TAtom TBool) (TAtom TBool)
  | Or      : BinOp (TAtom TBool) (TAtom TBool) (TAtom TBool)
  | Implies : BinOp (TAtom TBool) (TAtom TBool) (TAtom TBool)
  | Explies : BinOp (TAtom TBool) (TAtom TBool) (TAtom TBool)
  | Equiv   : BinOp (TAtom TBool) (TAtom TBool) (TAtom TBool)
  | PlusI   : BinOp (TAtom TInt) (TAtom TInt) (TAtom TInt)
  | MinusI  : BinOp (TAtom TInt) (TAtom TInt) (TAtom TInt)
  | TimesI  : BinOp (TAtom TInt) (TAtom TInt) (TAtom TInt)
  | DivI    : BinOp (TAtom TInt) (TAtom TInt) (TAtom TInt)
  | ModI    : BinOp (TAtom TInt) (TAtom TInt) (TAtom TInt)
  | PlusR   : BinOp (TAtom TReal) (TAtom TReal) (TAtom TReal)
  | MinusR  : BinOp (TAtom TReal) (TAtom TReal) (TAtom TReal)
  | TimesR  : BinOp (TAtom TReal) (TAtom TReal) (TAtom TReal)
  | DivR    : BinOp (TAtom TReal) (TAtom TReal) (TAtom TReal)
  | ModR    : BinOp (TAtom TReal) (TAtom TReal) (TAtom TReal)
  | Eq {t}  : BinOp t t (TAtom TBool)
  | Neq {t} : BinOp t t (TAtom TBool)
  | Lc {t}  : BinOp t t (TAtom TBool) (* <: *)
  | LsI     : BinOp (TAtom TInt) (TAtom TInt) (TAtom TBool)
  | LeqI    : BinOp (TAtom TInt) (TAtom TInt) (TAtom TBool)
  | GtI     : BinOp (TAtom TInt) (TAtom TInt) (TAtom TBool)
  | GeqI    : BinOp (TAtom TInt) (TAtom TInt) (TAtom TBool)
  | LsR     : BinOp (TAtom TReal) (TAtom TReal) (TAtom TBool)
  | LeqR    : BinOp (TAtom TReal) (TAtom TReal) (TAtom TBool)
  | GtR     : BinOp (TAtom TReal) (TAtom TReal) (TAtom TBool)
  | GeqR    : BinOp (TAtom TReal) (TAtom TReal) (TAtom TBool).

Inductive QOp : list Ty → Set :=
  | Forall {ts} : QOp ts
  | Exists {ts} : QOp ts
  | Lambda {ts} : QOp ts.

Definition IdType : Set := Id * Ty.

Inductive ilist {A : Set} (B : A → Set) : list A → Set :=
  | Nil : ilist B []
  | Cons {t : A} {ts : list A} : B t → ilist B ts → ilist B (t :: ts).

Inductive Expression : Ty → Set :=
  | FF : Expression (TAtom TBool)
  | TT : Expression (TAtom TBool)
  | Numeral : N → Expression (TAtom TInt)
  | Var {t} : Id → Expression t
  | Application {ts t} : Id → ilist Expression ts → Expression t
  | MapSelection {args ts t} :
    Expression (TMap (Mp args ts t)) → ilist Expression ts → Expression t
  | MapUpdate {args ts t} :
    Expression (TMap (Mp args ts t)) → ilist Expression ts → Expression t →
    Expression (TMap (Mp args ts t))
  | Old {t} : Expression t → Expression t
  | IfExpr {t} :
    Expression (TAtom TBool) → Expression t → Expression t → Expression t
  | Coercion {t} : Expression t → ∀ u : Ty, Expression u
  | UnaryExpression {a b} :
    UnOp a b → Expression a → Expression b
  | BinaryExpression {a b c} :
    BinOp a b c → Expression a → Expression b → Expression c
  | Quantified {ts} :
    QOp ts → ilist (λ _, Id) ts → Expression (TAtom TBool) → Expression (TAtom TBool).

Record IdTypeWhere : Set := {
  itwId : Id;
  itwType : Ty;
  itwWhere : Expression itwType;
}.

Definition noWhere (itw : IdTypeWhere) : IdType := (itwId itw, itwType itw).

Inductive Contract : Set :=
  | Requires : bool → Expression (TAtom TBool) → Contract
  | Modifies : bool → list Id → Contract
  | Ensures : bool → Expression (TAtom TBool) → Contract.

Inductive SpecType : Set :=
  | Constructors
  | Inline
  | Precondition
  | Postcondition
  | LoopInvariant
  | Where
  (* | Requires *)
  (* | Modifies *)
  (* | Ensures *)
  | Axiom_.

Record SpecClause : Set := {
  specType : SpecType;
  specFree : bool;
  specExpr : Expression (TAtom TBool)
}.

Inductive WildcardExpression : Ty → Set :=
  | Wildcard {t} : WildcardExpression t
  | Expr {t} : Expression t → WildcardExpression t.

Inductive Statement : Set :=
  | Predicate : SpecClause → Statement
  | Havoc : list Id → Statement
  (** The semantics of the statements:

        a[j] := E;
        b[i][m, n] := F;

      is defined as having the same semantics as:

        a := a[j := E];
        b := b[i := b[i][m, n := F]];

      Since this library is only for generating Boogie code, and not for
      parsing or representing it, the former syntax is not supported. *)
  | Assign {ts} : ilist (λ t, Id * Expression t)%type ts → Statement
  | Call {ts} : list Id → Id → ilist Expression ts → Statement
  | CallForall {ts} : Id → ilist WildcardExpression ts → Statement
  | If : WildcardExpression (TAtom TBool) → Block → option Block → Statement
  | While : WildcardExpression (TAtom TBool) → list SpecClause → Block → Statement
  | Break : option Id → Statement
  | Return : Statement
  | Goto : list Id → Statement
  | Skip

with LStatement : Set :=
  | LS : list Id → Statement → LStatement

with Block : Set :=
  | MkBlock : list LStatement → Block.

Definition singletonBlock {a a1 : Set} (s : a) : list (list a1 * a) :=
  [([], s)].

Definition Body : Set := list (list IdTypeWhere) * Block.

Definition BasicBlock : Set := Id * list Statement.

Definition BasicBody : Set := list IdTypeWhere * Map Id (list Statement).

Inductive Decl : Set :=
  | TypeDecl : list NewType → Decl
  | ConstantDecl : bool → list Id → Ty → ParentInfo → bool → Decl
  | FunctionDecl :
    Id → list Id → list FArg → ∀ ret : FArg, option (Expression (snd ret)) → Decl
  | AxiomDecl : Expression (TAtom TBool) → Decl
  | VarDecl : list IdTypeWhere → Decl
  | ProcedureDecl :
    Id → list Id → list IdTypeWhere → list IdTypeWhere → list Contract →
    option Body → Decl
  | ImplementationDecl :
    Id → list Id → list IdType → list IdType → list Body → Decl.

Inductive Program : Set :=
  | MkProgram : list Decl → Program.

End Boogie.
