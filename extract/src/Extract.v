Set Warnings "-extraction-reserved-identifier".

From Coq Require Extraction.

Require Import
  Coq.Strings.Ascii
  Pact.Data.Semigroup
  Pact.Lib
  Pact.Ty
  Pact.Exp
  Pact.Eval.

From Equations Require Import Equations.
Set Equations With UIP.

(** Eq *)

Extraction Implicit eq_rect   [ 2 5 ].
Extraction Implicit eq_rect_r [ 2 5 ].
Extraction Implicit eq_rec    [ 2 5 ].
Extraction Implicit eq_rec_r  [ 2 5 ].

Extract Inlined Constant eq_rect   => "(\_ _ x _ -> x)".
Extract Inlined Constant eq_rect_r => "(\_ _ x _ -> x)".
(* eq_rec   : ∀ (A : Type) (x : A) (P : A → Set), P x → ∀ y : A, x = y → P y *)
Extract Inlined Constant eq_rec    => "(\_ _ x _ -> x)".
(* eq_rec_r : ∀ (A : Type) (x : A) (P : A → Set), P x → ∀ y : A, y = x → P y *)
Extract Inlined Constant eq_rec_r  => "(\_ _ x _ -> x)".

(** Ord *)

Extract Inductive comparison =>
  "Prelude.Ordering" ["Prelude.EQ" "Prelude.LT" "Prelude.GT"].

(** Int *)

Extract Inductive Datatypes.nat => "Prelude.Int"
  ["(0 :: Prelude.Int)" "Prelude.succ"]
  "(\fO fS n -> if n Prelude.<= 0 then fO Prelude.undefined else fS (Prelude.pred n))".

Extract Inlined Constant EqNat.beq_nat         =>
  "((Prelude.==) :: Prelude.Int -> Prelude.Int -> Prelude.Bool)".
Extract Inlined Constant Compare_dec.le_lt_dec =>
  "((Prelude.<=) :: Prelude.Int -> Prelude.Int -> Prelude.Bool)".
Extract Inlined Constant Compare_dec.le_gt_dec => "(Prelude.>)".
Extract Inlined Constant Compare_dec.le_dec    =>
  "((Prelude.<=) :: Prelude.Int -> Prelude.Int -> Prelude.Bool)".
Extract Inlined Constant Compare_dec.lt_dec    => "(Prelude.<)".
Extract Inlined Constant Compare_dec.leb       =>
  "((Prelude.<=) :: Prelude.Int -> Prelude.Int -> Prelude.Bool)".

Extract Inlined Constant plus  => "(Prelude.+)".
Extract Inlined Constant minus => "(Prelude.-)".
Extract Inlined Constant mult  => "(Prelude.* )".
Extract Inlined Constant Nat.pred  =>
  "(Prelude.pred :: Prelude.Int -> Prelude.Int)".
Extract Inlined Constant min   => "Prelude.min".
Extract Inlined Constant max   =>
  "(Prelude.max :: Prelude.Int -> Prelude.Int -> Prelude.Int)".

(** Z, positive, Q *)

Require Import Coq.ZArith.ZArith.

Extract Inductive positive => "Prelude.Int" [
  "(\x -> 2 Prelude.* x Prelude.+ 1)"
  "(\x -> 2 Prelude.* x)"
  "1" ]
  "(\fI fO fH n -> if n Prelude.== 1 then fH Prelude.undefined else
                   if Prelude.odd n then fI (n `Prelude.div` 2)
                                    else fO (n `Prelude.div` 2))".

Extract Inductive Z => "Prelude.Int" [ "0" "(\x -> x)" "Prelude.negate" ]
  "(\fO fP fN n -> if n Prelude.== 0 then fO Prelude.undefined else
                   if n Prelude.> 0 then fP n else fN (Prelude.negate n))".

Extract Inlined Constant Z.add       => "(Prelude.+)".
Extract Inlined Constant Z.sub       => "(Prelude.-)".
Extract Inlined Constant Z.mul       => "(Prelude.*)".
Extract Inlined Constant Z.max       => "Prelude.max".
Extract Inlined Constant Z.min       => "Prelude.min".
Extract Inlined Constant Z_ge_lt_dec => "(Prelude.>=)".
Extract Inlined Constant Z_gt_le_dec => "(Prelude.>)".

Extract Constant Z.div =>
  "(\n m -> if m Prelude.== 0 then 0 else Prelude.div n m)".
Extract Constant Z.modulo =>
  "(\n m -> if m Prelude.== 0 then 0 else Prelude.mod n m)".

Extract Inductive N => "Prelude.Int" [ "0" "(\x -> x)" ]
  "(\fO fP n -> if n Prelude.== 0 then fO Prelude.undefined else fP n)".

Extract Inlined Constant N.add       => "(Prelude.+)".
Extract Inlined Constant N.sub       => "(Prelude.-)".
Extract Inlined Constant N.mul       => "(Prelude.*)".
Extract Inlined Constant N.max       => "Prelude.max".
Extract Inlined Constant N.min       => "Prelude.min".
Extract Inlined Constant N.ltb       => "(Prelude.<)".
Extract Inlined Constant N.leb       => "(Prelude.<=)".
Extract Inlined Constant N.of_nat    => "".

(** Bool *)

Extract Inductive bool    => "Prelude.Bool" ["Prelude.True" "Prelude.False"].
Extract Inductive sumbool => "Prelude.Bool"
  ["(\_ -> Prelude.True)" "(\_ -> Prelude.False)"]
  "(\fT fF b -> if b then fT Prelude.undefined else fF Prelude.undefined)".

(* Extract Inlined Constant Equality.bool_beq => *)
(*   "((Prelude.==) :: Prelude.Bool -> Prelude.Bool -> Prelude.Bool)". *)
Extract Inlined Constant Bool.bool_dec     =>
  "((Prelude.==) :: Prelude.Bool -> Prelude.Bool -> Prelude.Bool)".

Extract Inlined Constant Sumbool.sumbool_of_bool => "".

Extract Inlined Constant negb => "Prelude.not".
Extract Inlined Constant orb  => "(Prelude.||)".
Extract Inlined Constant andb => "(Prelude.&&)".

(** Maybe *)

Extract Inductive option => "Prelude.Maybe" ["Prelude.Just" "Prelude.Nothing"].
Extract Inductive sumor  => "Prelude.Maybe" ["Prelude.Just" "Prelude.Nothing"].

(** Either *)

Extract Inductive sum => "Prelude.Either" ["Prelude.Left" "Prelude.Right"].

(** List *)

Extract Inductive list => "[]" ["[]" "(:)"].

Extract Inlined Constant app             => "(\_ -> (Prelude.++))".
Extract Inlined Constant List.map        => "(\_ _ -> Prelude.map)".
Extract         Constant List.fold_left  => "\f l z -> Data.List.foldl f z l".
Extract Inlined Constant List.fold_right => "Data.List.foldr".
Extract Inlined Constant List.find       => "Data.List.find".
Extract Inlined Constant List.length     =>
  "(Data.List.length :: [a] -> Prelude.Int)".

(** Tuple *)

Extract Inductive prod => "(,)" ["(,)"].
Extract Inductive sigT => "(,)" ["(,)"].

Extract Inlined Constant fst    => "Prelude.fst".
Extract Inlined Constant snd    => "Prelude.snd".
Extract Inlined Constant projT1 => "Prelude.fst".
Extract Inlined Constant projT2 => "Prelude.snd".

Extract Inlined Constant proj1_sig => "".

(** Unit *)

Extract Inductive unit => "()" ["()"].

(** Vector *)

Require Import Coq.Vectors.Vector.

Extract Inductive Vector.t =>
  "HString.Vector" ["HString.Nil" "HString.Cons"].
Extract Inductive VectorDef.t =>
  "HString.Vector" ["HString.Nil" "HString.Cons"].

(** String *)

Extract Inductive string => "Prelude.String" ["[]" "(:)"].
Extract Inductive ascii  => "Prelude.Char" ["HString.asciiToChar"]
  "HString.foldChar".

Extract Inlined Constant ascii_of_nat => "Data.Char.chr".
Extract Inlined Constant nat_of_ascii => "Data.Char.ord".
Extract Inlined Constant ascii_of_N   => "Data.Char.chr".
Extract Inlined Constant ascii_of_pos => "Data.Char.chr".
Extract Inlined Constant ascii_eqdec  => "(Prelude.==)".
Extract Inlined Constant string_eqdec => "(Prelude.==)".

(** Equations *)

Extract Constant Signature "'a" "'b" "'c" => "".

(** Pact *)

(*
Extract Inductive Var => "Types.Var"
  ["Types.ZV" "Types.SV"]
  "(\fZV fSV v ->
     case v of
       Types.ZV _ _   -> fZV
       Types.SV _ _ v -> fSV v)".
*)

(** Final extraction *)

Extraction Language Haskell.

Unset Extraction KeepSingleton.
Set Extraction AutoInline.
Set Extraction Optimize.
Set Extraction AccessOpaque.
Set Extraction Conservative Types.

Extraction Blacklist Prelude.

Separate Extraction
  Pact.Ty.Ty
  Pact.Exp.Var
  Pact.Exp.Exp
  Pact.Eval.eval
  Pact.Eval.evalInModule.

(*
Require dpdgraph.dpdgraph.

Print FileDependGraph
  Pact.Ty
  Pact.Exp
  Pact.Eval.
*)
