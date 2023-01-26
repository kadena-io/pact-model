---- MODULE SynchronousL2 ----

EXTENDS TLC, Naturals, Integers, Sequences, FiniteSets

CONSTANT Supply

(* --termination --fair algorithm SynchronousL2 {

variables
    Accounts    = [ Alice |-> Supply \div 2
                  , Bob   |-> Supply \div 2 ],
    Locked      = Empty,
    L2Accounts  = Empty,
    KadenaState = "Normal",
    L2State     = "Waiting",
    block       = 1
    ;

define {
  KadenaStates == { 
    "Normal",        \* Regular blockchain operation
    "Submit",        \* On-chain contract wishes to lockup
    "Locked"         \* Accounts are locked on Kadena
  }
  L2States == { 
    "Waiting",       \* Waiting on account locks to release funds
    "Working",       \* Handling transactions on L2
    "Ready"          \* Ready to prepare the return state
  }

  Empty == [ Alice |-> 0, Bob |-> 0 ]

  Total(accounts) == accounts.Alice + accounts.Bob

  \* It is always the case that no matter what state the system is in,
  \* eventually the KadenaState will be Normal again.
  Liveness == []<>(KadenaState = "Normal")
}

macro conserves_mass() {
    assert Total(Accounts) + Total(Locked) = Supply;
}

\* This is a fair process because it is guaranteed, for the purposes of this
\* formal model, to never get "stuck".

fair+ process ( Kadena = 1 )
{
Loop:
  either {
    await KadenaState = "Normal";

    assert Total(Locked) = 0;

    \* Any block may request transfer of funds to the L2
    with (nextState \in { "Normal", "Submit" }) {
      KadenaState := nextState;
    };

    assert L2State = "Waiting";
  }
  or {
    await KadenaState = "Submit";

    assert Total(Locked) = 0;

    Locked     := Accounts;
    Accounts   := Empty;
    L2Accounts := Locked;

    KadenaState  := "Locked";

    assert L2State = "Waiting";
    L2State := "Working";
  }
  or {
    await KadenaState = "Locked";

    either {
      await L2State = "Ready";

      assert Total(Locked) = Total(L2Accounts);

      Locked   := Empty;
      Accounts := L2Accounts;

      KadenaState  := "Normal";

      L2State := "Waiting";
    }
    or {
      assert Total(Accounts) = 0;

      assert L2State = "Working";
    };
  };

Step:
  block := block + 1;

  conserves_mass();
}

fair+ process ( L2 = 2 )
{
Loop:
  either {
    await L2State = "Waiting";

    assert Total(L2Accounts) = 0;

    assert \/ KadenaState = "Normal"
           \/ KadenaState = "Submit";
  }
  or {
    await L2State = "Working";

    assert Total(L2Accounts) = Supply;

    \* At some point in the future, the L2 will want to settle
    with (nextState \in { "Working", "Ready" }) {
      L2State := nextState;
    };

    assert KadenaState = "Locked";
  }
  or {
    await L2State = "Ready";

    assert Total(L2Accounts) = Supply;

    assert KadenaState = "Locked";
  };
}

} *)
\* BEGIN TRANSLATION (chksum(pcal) = "cac5dc80" /\ chksum(tla) = "179c0e42")
\* Label Loop of process Kadena at line 47 col 3 changed to Loop_
VARIABLES Accounts, Locked, L2Accounts, KadenaState, L2State, block, pc

(* define statement *)
KadenaStates == {
  "Normal",
  "Submit",
  "Locked"
}
L2States == {
  "Waiting",
  "Working",
  "Ready"
}

Empty == [ Alice |-> 0, Bob |-> 0 ]
Total(accounts) == accounts.Alice + accounts.Bob



Liveness == []<>(KadenaState = "Normal")


vars == << Accounts, Locked, L2Accounts, KadenaState, L2State, block, pc >>

ProcSet == {1} \cup {2}

Init == (* Global variables *)
        /\ Accounts = [ Alice |-> Supply \div 2
                      , Bob   |-> Supply \div 2
                      ]
        /\ Locked = Empty
        /\ L2Accounts = Empty
        /\ KadenaState = "Normal"
        /\ L2State = "Waiting"
        /\ block = 1
        /\ pc = [self \in ProcSet |-> CASE self = 1 -> "Loop_"
                                        [] self = 2 -> "Loop"]

Loop_ == /\ pc[1] = "Loop_"
         /\ \/ /\ KadenaState = "Normal"
               /\ Assert(Total(Locked) = 0, 
                         "Failure of assertion at line 50, column 5.")
               /\ \E nextState \in { "Normal", "Submit" }:
                    KadenaState' = nextState
               /\ Assert(L2State = "Waiting", 
                         "Failure of assertion at line 57, column 5.")
               /\ UNCHANGED <<Accounts, Locked, L2Accounts, L2State>>
            \/ /\ KadenaState = "Submit"
               /\ Assert(Total(Locked) = 0, 
                         "Failure of assertion at line 62, column 5.")
               /\ Locked' = Accounts
               /\ Accounts' = Empty
               /\ L2Accounts' = Locked'
               /\ KadenaState' = "Locked"
               /\ Assert(L2State = "Waiting", 
                         "Failure of assertion at line 70, column 5.")
               /\ L2State' = "Working"
            \/ /\ KadenaState = "Locked"
               /\ \/ /\ L2State = "Ready"
                     /\ Assert(Total(Locked) = Total(L2Accounts), 
                               "Failure of assertion at line 79, column 7.")
                     /\ Locked' = Empty
                     /\ Accounts' = L2Accounts
                     /\ KadenaState' = "Normal"
                     /\ L2State' = "Waiting"
                  \/ /\ Assert(Total(Accounts) = 0, 
                               "Failure of assertion at line 89, column 7.")
                     /\ Assert(L2State = "Working", 
                               "Failure of assertion at line 91, column 7.")
                     /\ UNCHANGED <<Accounts, Locked, KadenaState, L2State>>
               /\ UNCHANGED L2Accounts
         /\ pc' = [pc EXCEPT ![1] = "Step"]
         /\ block' = block

Step == /\ pc[1] = "Step"
        /\ block' = block + 1
        /\ Assert(Total(Accounts) + Total(Locked) = Supply, 
                  "Failure of assertion at line 41, column 5 of macro called at line 98, column 3.")
        /\ pc' = [pc EXCEPT ![1] = "Done"]
        /\ UNCHANGED << Accounts, Locked, L2Accounts, KadenaState, L2State >>

Kadena == Loop_ \/ Step

Loop == /\ pc[2] = "Loop"
        /\ \/ /\ L2State = "Waiting"
              /\ Assert(Total(L2Accounts) = 0, 
                        "Failure of assertion at line 107, column 5.")
              /\ Assert(\/ KadenaState = "Normal"
                        \/ KadenaState = "Submit", 
                        "Failure of assertion at line 109, column 5.")
              /\ UNCHANGED L2State
           \/ /\ L2State = "Working"
              /\ Assert(Total(L2Accounts) = Supply, 
                        "Failure of assertion at line 115, column 5.")
              /\ \E nextState \in { "Working", "Ready" }:
                   L2State' = nextState
              /\ Assert(KadenaState = "Locked", 
                        "Failure of assertion at line 122, column 5.")
           \/ /\ L2State = "Ready"
              /\ Assert(Total(L2Accounts) = Supply, 
                        "Failure of assertion at line 127, column 5.")
              /\ Assert(KadenaState = "Locked", 
                        "Failure of assertion at line 129, column 5.")
              /\ UNCHANGED L2State
        /\ pc' = [pc EXCEPT ![2] = "Done"]
        /\ UNCHANGED << Accounts, Locked, L2Accounts, KadenaState, block >>

L2 == Loop

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == Kadena \/ L2
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)
        /\ SF_vars(Kadena)
        /\ SF_vars(L2)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

==============================================
Specification.
