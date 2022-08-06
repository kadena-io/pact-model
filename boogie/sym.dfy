module Seq {
  function Fold<T, TAcc(!new)>(s: seq<T>, f: (T, TAcc) -> TAcc, a0: TAcc) : (a: TAcc) {
    if s == [] then a0
    else
      var x: T := s[0];
      f(x, Fold(s[1..], f, a0))
  }

  predicate Symmetric<T(!new), TAcc(!new)>(P: T -> bool, f: (T, TAcc) -> TAcc) {
    forall x, y, a | P(x) && P(y) :: f(x, f(y, a)) == f(y, f(x, a))
  }

  lemma MoveFront<T>(i: int, s: seq<T>) returns (s': seq<T>)
    requires 0 <= i < |s|
    ensures |s'| == |s|
    ensures s'[0] == s[i]
    ensures multiset(s') == multiset(s)
    ensures multiset(s'[1..]) == multiset(s) - multiset{s[i]}
  {
    s' := [s[i]] + s[..i] + s[i + 1..];
    assert s[..i] + [s[i]] + s[i + 1..] == s;
    assert s'[1..] == s[..i] + s[i + 1..];
  }

  lemma ApplySymmetry<T(!new), TAcc(!new)>(P: T -> bool, f: (T, TAcc) -> TAcc, x: T, y: T, a: TAcc)
    requires P(x)
    requires P(y)
    requires Symmetric(P, f)
    ensures f(x, f(y, a)) == f(y, f(x, a))
  {}

  lemma Symmetric_Fold<T(!new), TAcc(!new)>(s0: seq<T>, s1: seq<T>, P: T -> bool, f: (T, TAcc) -> TAcc, a0: TAcc)
    requires Symmetric(P, f)
    requires forall x | x in s0 :: P(x)
    requires multiset(s0) == multiset(s1)
    decreases |s0|
    ensures Fold(s0, f, a0) == Fold(s1, f, a0)
  {
    calc { |s1|; |multiset(s1)|; |multiset(s0)|; |s0|; }
    if s0 == [] || s1 == [] {
    } else {
      var x0, x1 := s0[0], s1[0];
      var s0', s1' := s0[1..], s1[1..];

      assert s0 == [x0] + s0';
      assert multiset(s0') == multiset(s0) - multiset{x0};

      assert s1 == [x1] + s1';
      assert multiset(s1') == multiset(s1) - multiset{x1};

      if x0 == x1 {
        assert multiset(s0') == multiset(s1');
        Symmetric_Fold(s0', s1', P, f, a0);
      } else {
        assert x1 in multiset(s0') && x1 in s0';
        var i0 :| 0 <= i0 < |s0'| && s0'[i0] == x1;
        var s0'' := MoveFront(i0, s0');

        assert x0 in multiset(s1') && x0 in s1';
        var i1 :| 0 <= i1 < |s1'| && s1'[i1] == x0;
        var s1'' := MoveFront(i1, s1');

        var s0''', s1''' := s0''[1..], s1''[1..];
        assert multiset(s0''') == multiset(s0) - multiset{x0, x1};
        assert multiset(s1''') == multiset(s1) - multiset{x1, x0};

        forall x | x in s0' ensures P(x) { assert x in multiset(s0''); }
        forall x | x in s1' ensures P(x) { assert x in multiset(s1''); }
        forall x | x in s0''' ensures P(x) { assert x in multiset(s0'''); }
        forall x | x in s1''' ensures P(x) { assert x in multiset(s1'''); }

        calc {
          Fold(s0, f, a0);
          f(x0, Fold(s0', f, a0));
          { Symmetric_Fold(s0', s0'', P, f, a0); }
          f(x0, Fold(s0'', f, a0));
          f(x0, f(x1, Fold(s0''', f, a0)));
          { Symmetric_Fold(s0''', s1''', P, f, a0); }
          f(x0, f(x1, Fold(s1''', f, a0)));
          { ApplySymmetry(P, f, x0, x1, Fold(s1''', f, a0)); }
          f(x1, f(x0, Fold(s1''', f, a0)));
          f(x1, Fold(s1'', f, a0));
          { Symmetric_Fold(s1', s1'', P, f, a0); }
          f(x1, Fold(s1', f, a0));
          Fold(s1, f, a0);
        }
      }
    }
  }
}

module Set {
  import Seq

  predicate IsFold<T(!new), TAcc(!new)>(s: set<T>, f: (T, TAcc) -> TAcc, a0: TAcc, sq: seq<T>, a: TAcc) {
    a == Seq.Fold(sq, f, a0)
  }

  lemma IsFold_Nil<T(!new), TAcc(!new)>(f: (T, TAcc) -> TAcc, a0: TAcc)
    ensures IsFold({}, f, a0, [], a0)
  {}

  lemma IsFold_Cons<T(!new), TAcc(!new)>(s: set<T>, f: (T, TAcc) -> TAcc, a0: TAcc, sq: seq<T>, a: TAcc, x: T)
    requires x in s
    requires IsFold(s - {x}, f, a0, sq, a)
    ensures IsFold(s, f, a0, [x] + sq, f(x, a))
  {}

  predicate ExistsFold<T(!new), TAcc(!new)>(s: set<T>, f: (T, TAcc) -> TAcc, a0: TAcc, a: TAcc) {
    exists sq: seq<T> | multiset(sq) == multiset(s) :: IsFold(s, f, a0, sq, a)
  }

  lemma ExistsFold_Nil<T(!new), TAcc(!new)>(f: (T, TAcc) -> TAcc, a0: TAcc)
    ensures ExistsFold({}, f, a0, a0)
  {
    IsFold_Nil(f, a0);
  }

  lemma ExistsFold_Cons<T(!new), TAcc(!new)>(s: set<T>, f: (T, TAcc) -> TAcc, a0: TAcc, a: TAcc, x: T)
    requires x in s
    requires ExistsFold(s - {x}, f, a0, a)
    ensures ExistsFold(s, f, a0, f(x, a))
  {
    var sq :| multiset(sq) == multiset(s - {x}) && IsFold(s - {x}, f, a0, sq, a);
    IsFold_Cons(s, f, a0, sq, a, x);
  }

  predicate AllFolds<T(!new), TAcc(!new)>(s: set<T>, f: (T, TAcc) -> TAcc, a0: TAcc, a: TAcc) {
    forall sq: seq<T> | multiset(sq) == multiset(s) :: IsFold(s, f, a0, sq, a)
  }

  lemma Symmetric_Fold<T(!new), TAcc(!new)>(s: set<T>, sq: seq<T>, f: (T, TAcc) -> TAcc, a0: TAcc)
    requires Seq.Symmetric(x => x in s, f)
    requires multiset(s) == multiset(sq)
    ensures Fold'(s, f, a0) == Seq.Fold(sq, f, a0)
  {
    assert ExistsFold(s, f, a0, Fold'(s, f, a0));
    var sq0 :| multiset(sq0) == multiset(s) && IsFold(s, f, a0, sq0, Fold'(s, f, a0));
    forall x | x in sq ensures x in s { assert x in multiset(sq); }
    Seq.Symmetric_Fold(sq, sq0, x => x in s, f, a0);
  }

  lemma ExistsFold_AllFolds<T(!new), TAcc(!new)>(s: set<T>, f: (T, TAcc) -> TAcc, a0: TAcc, a: TAcc)
    requires Seq.Symmetric(x => x in s, f)
    requires ExistsFold(s, f, a0, a)
    ensures AllFolds(s, f, a0, a)
  {
    var sq0 :| multiset(sq0) == multiset(s) && IsFold(s, f, a0, sq0, a);
    forall sq: seq<T> | multiset(sq) == multiset(s)
      ensures IsFold(s, f, a0, sq, a)
    {
      Symmetric_Fold(s, sq0, f, a0);
      Symmetric_Fold(s, sq, f, a0);
    }
  }

  lemma ExistsFold_Unique<T(!new), TAcc(!new)>(s: set<T>, f: (T, TAcc) -> TAcc, a0: TAcc, a: TAcc, a': TAcc)
    requires Seq.Symmetric(x => x in s, f)
    requires ExistsFold(s, f, a0, a)
    requires ExistsFold(s, f, a0, a')
    ensures a == a'
  {
    var sq :| multiset(sq) == multiset(s) && IsFold(s, f, a0, sq, a);
    var sq' :| multiset(sq') == multiset(s) && IsFold(s, f, a0, sq', a');
    Symmetric_Fold(s, sq, f, a0);
    Symmetric_Fold(s, sq', f, a0);
  }

  function {:opaque} Fold'<T(!new), TAcc(!new)>(s: set<T>, f: (T, TAcc) -> TAcc, a0: TAcc) : (a: TAcc)
    requires Seq.Symmetric(x => x in s, f)
    ensures ExistsFold(s, f, a0, a)
  {
    if s == {} then
      ExistsFold_Nil(f, a0);
      a0
    else
      var x: T :| x in s;
      var a1 := Fold'(s - {x}, f, a0);
      ExistsFold_Cons(s, f, a0, a1, x);
      f(x, a1)
  } by method {
    ghost var seen, sq := {}, [];
    var s1 := s;
    a := a0;
    while s1 != {}
      invariant s1 !! seen
      invariant s1 + seen == s
      invariant multiset(sq) == multiset(seen)
      invariant IsFold(seen, f, a0, sq, a)
    {
      var x: T :| x in s1;
      s1 := s1 - {x};
      seen := seen + {x};
      sq := [x] + sq;
      a := f(x, a);
    }
    ExistsFold_Unique(s, f, a0, a, Fold'(s, f, a0));
  }

  function SeqOfSet<K>(s: set<K>): (sq: seq<K>)
    ensures multiset(sq) == multiset(s)
  {
    if s == {} then [] else var x :| x in s; [x] + SeqOfSet(s - {x})
  }

  function method {:opaque} Fold<T(!new), TAcc(!new)>(s: set<T>, f: (T, TAcc) -> TAcc, a0: TAcc) : (a: TAcc)
    requires Seq.Symmetric(x => x in s, f)
    ensures forall sq: seq<T> | multiset(sq) == multiset(s) :: a == Seq.Fold(sq, f, a0)
  {
    var a := Fold'(s, f, a0);
    assert forall sq: seq<T> | multiset(sq) == multiset(s) :: a == Seq.Fold(sq, f, a0) by {
      forall sq | multiset(sq) == multiset(s) ensures a == Seq.Fold(sq, f, a0) {
        Symmetric_Fold(s, sq, f, a0);
      }
    }
    a
  }
}
