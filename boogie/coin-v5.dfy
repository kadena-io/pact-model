class guard {
}

class coin_table {
  var coin_balances : map<string, real>;
}

class coin {

// type TyGuard;
// type TyString;
// type TyObject;
// type TyTime;

// function length(str:TyString): int;

// const unique emptyString : TyString;
// axiom (length(emptyString) == 0);
// axiom (forall s:TyString :: s != emptyString ==> length(s) > 0);

//////////////////////////////////////////////////////////////////////////////

// (module coin GOVERNANCE

//   @doc "'coin' represents the Kadena Coin Contract. This contract provides both the \
//   \buy/redeem gas support in the form of 'fund-tx', as well as transfer,       \
//   \credit, debit, coinbase, account creation and query, as well as SPV burn    \
//   \create. To access the coin contract, you may use its fully-qualified name,  \
//   \or issue the '(use coin)' command in the body of a module declaration."

//   @model
//     [ (defproperty conserves-mass
//         (= (column-delta coin-table 'balance) 0.0))

//       (defproperty valid-account (account:string)
//         (and
//           (>= (length account) 3)
//           (<= (length account) 256)))
//     ]

//   (implements fungible-v2)
//   (implements fungible-xchain-v1)

//   ;; coin-v2
//   (bless "ut_J_ZNkoyaPUEJhiwVeWnkSQn9JT9sQCWKdjjVVrWo")

//   ;; coin v3
//   (bless "1os_sLAUYvBzspn5jjawtRpJWiH1WPfhyNraeVvSIwU")

//   ;; coin v4
//   (bless "BjZW0T2ac6qE_I5X8GE4fal6tTqjhLTC7my0ytQSxLU")

//   ; --------------------------------------------------------------------------
//   ; Schemas and Tables

//   (defschema coin-schema
//     @doc "The coin contract token schema"
//     @model [ (invariant (>= balance 0.0)) ]

//     balance:decimal
//     guard:guard)

//   (deftable coin-table:{coin-schema})

// method len <K, V>(arr:[K]V) returns (int);
// axiom (forall <K, V> A:[K]V :: len(A) >= 0);

// method is_in <V>(i:int, arr:[int]V) returns (bool);
// axiom (forall <V> i:int, arr:[int]V ::
//   is_in(i, arr) ==> 0 <= i && i < len(arr));

// method not_in <V>(i:int, arr:[int]V) returns (bool);
// axiom (forall <V> i:int, arr:[int]V ::
//   not_in(i, arr) ==> i < 0 || i >= len(arr));

// method create_table();
//   modifies coin_table#balance;
//   ensures (forall k:TyString :: coin_table#balance[k] == 0.0);
//   ensures len(coin_table#keys) == 0;
// {
//   assume len(coin_table#keys) == 0;
//   coin_table#balance := (lambda k:TyString :: 0.0);
// }

var coins : coin_table;

constructor(db:coin_table)
{
  coins := db;
}

// conserves-mass
method map_sum(reals: set<real>) returns (r:real)
{
  r := 0.0;

  var items := reals;
  while items != {} decreases |items|
  {
    var item :| item in items;
    items := items - { item };

    r := r + item;
  }
}

function SumSeq(s: seq<(string, real)>): real
{
  if s == [] then
    0.0
  else
    s[0].1 + SumSeq(s[1..])
}

function Pick<K>(s: set<K>): K
  requires s != {}
{
  var x :| x in s; x
}

function Sum(s: set<(string, real)>): real
{
  if s == {} then
    0.0
  else
    var item := Pick(s);
    item.1 + Sum(s - { item })
}

function Delta(s1: map<string, real>, s2: map<string, real>): real
  decreases s1, s2
  requires forall k:string :: k in s1 <==> k in s2
{
  if |s1| == 0 then
    0.0
  else
    var k := Pick(s1.Keys);
    (s1[k] - s2[k]) + Delta(s1 - { k }, s2 - { k })
}

// jww (2022-08-06): How do I prove that it doesn't matter what order you pick
// elements in, the answer from Delta is always the same?

// lemma DeltaLemma(s1: map<string, real>, s2: map<string, real>)
//   requires forall k:string :: k in s1 <==> k in s2
//   ensures forall k:string :: k in s1 ==>
//     Delta(s1, s2) == (s1[k] - s2[k]) + Delta(s1 - { k }, s2 - { k })
// {
// }

lemma SumMyWay(s: set<(string, real)>, y: (string, real))
  requires y in s
  ensures Sum(s) == y.1 + Sum(s - {y})
{
  var x : (string, real) := Pick(s);
  if y == x {
  } else {
    calc {
      Sum(s);
    ==  // def. Sum
      x.1 + Sum(s - {x});
    ==  { SumMyWay(s - {x}, y); }
      x.1 + y.1 + Sum(s - {x} - {y});
    ==  { assert s - {x} - {y} == s - {y} - {x}; }
      y.1 + x.1 + Sum(s - {y} - {x});
    ==  { SumMyWay(s - {y}, x); }
      y.1 + Sum(s - {y});
    }
  }
}

lemma AddToSum(s: set<(string, real)>, y: (string, real))
  requires y !in s
  ensures Sum(s + {y}) == Sum(s) + y.1
{
  SumMyWay(s + {y}, y);
}

predicate IsTotalOrder<A(!new)>(R: (A, A) -> bool) {
  // connexity
  && (forall a, b :: R(a, b) || R(b, a))
  // antisymmetry
  && (forall a, b :: R(a, b) && R(b, a) ==> a == b)
  // transitivity
  && (forall a, b, c :: R(a, b) && R(b, c) ==> R(a, c))
}

function method MapToSequence<A(!new),B>(m: map<A,B>, R: (A, A) -> bool): seq<(A,B)>
  requires IsTotalOrder(R)
{
  var keys := SetToSequence(m.Keys, (a,a') => R(a, a'));
  seq(|keys|, i requires 0 <= i < |keys| => (keys[i], m[keys[i]]))
}

function method SetToSequence<A(!new)>(s: set<A>, R: (A, A) -> bool): seq<A>
  requires IsTotalOrder(R)
  ensures var q := SetToSequence(s, R);
    forall i :: 0 <= i < |q| ==> q[i] in s
{
  if s == {} then [] else
    ThereIsAMinimum(s, R);
    var x :| x in s && forall y :: y in s ==> R(x, y);
    [x] + SetToSequence(s - {x}, R)
}

lemma ThereIsAMinimum<A(!new)>(s: set<A>, R: (A, A) -> bool)
  requires s != {} && IsTotalOrder(R)
  ensures exists x :: x in s && forall y :: y in s ==> R(x, y)

// valid-account
predicate valid_account(account:string) {
  |account| >= 3 && |account| <= 256
}

twostate function column_delta(): real
  reads this, coins
  requires forall k:string :: k in old(coins.coin_balances) <==> k in coins.coin_balances
{
  // Sum(old(coins.coin_balances.Items)) - Sum(coins.coin_balances.Items)
  Delta(old(coins.coin_balances), coins.coin_balances)
}

twostate predicate conserves_mass()
  reads this, coins
  requires forall k:string :: k in old(coins.coin_balances) <==> k in coins.coin_balances
{
  column_delta() == 0.0
}

method sample_transfer(sender:string, receiver:string, amount:real)
  // this table is updated
  modifies coins;

  // inputs arguments are valid
  requires amount >= 0.0;
  requires valid_account(sender)
  requires valid_account(receiver)
  requires sender != receiver

  // no accounts with negative balance before or after
  requires forall k:string :: k in coins.coin_balances ==> coins.coin_balances[k] >= 0.0
  ensures forall k:string :: k in coins.coin_balances ==> coins.coin_balances[k] >= 0.0

  // sender and receiver are present before and after
  requires sender in coins.coin_balances
  ensures sender in coins.coin_balances
  requires receiver in coins.coin_balances
  ensures receiver in coins.coin_balances

  // a simple implication of the transfer
  requires coins.coin_balances[sender] >= amount
  ensures coins.coin_balances[receiver] >= amount

  // no accounts created or destroyed
  ensures forall k:string :: k in old(coins.coin_balances) <==> k in coins.coin_balances

  // conserves mass: all other account balances are unchanged
  ensures forall k:string :: k in coins.coin_balances && k != sender && k != receiver ==>
    old(coins.coin_balances[k]) == coins.coin_balances[k]
  // conserves mass: delta of sender + receiver is zero
  ensures old(coins.coin_balances[sender]) + old(coins.coin_balances[receiver]) ==
    coins.coin_balances[sender] + coins.coin_balances[receiver]
{
  coins.coin_balances :=
    coins.coin_balances[sender   := coins.coin_balances[sender] - amount];
  coins.coin_balances :=
    coins.coin_balances[receiver := coins.coin_balances[receiver] + amount];
}

//   ; --------------------------------------------------------------------------
//   ; Capabilities

//   (defcap GOVERNANCE ()
//     (enforce false "Enforce non-upgradeability"))

//procedure GOVERNANCE();

//   (defcap GAS ()
//     "Magic capability to protect gas buy and redeem"
//     true)

//procedure GAS();

//   (defcap COINBASE ()
//     "Magic capability to protect miner reward"
//     true)

//procedure COINBASE();

//   (defcap GENESIS ()
//     "Magic capability constraining genesis transactions"
//     true)

//procedure GENESIS();

//   (defcap REMEDIATE ()
//     "Magic capability for remediation transactions"
//     true)

//procedure REMEDIATE();

//   (defcap DEBIT (sender:string)
//     "Capability for managing debiting operations"
//     (enforce-guard (at 'guard (read coin-table sender)))
//     (enforce (!= sender "") "valid sender"))

//procedure DEBIT(sender:TyString);

//   (defcap CREDIT (receiver:string)
//     "Capability for managing crediting operations"
//     (enforce (!= receiver "") "valid receiver"))

//procedure CREDIT(receiver:TyString);

//   (defcap ROTATE (account:string)
//     @doc "Autonomously managed capability for guard rotation"
//     @managed
//     true)

//procedure ROTATE(account:TyString);

//   (defcap TRANSFER:bool
//     ( sender:string
//       receiver:string
//       amount:decimal
//     )
//     @managed amount TRANSFER-mgr
//     (enforce (!= sender receiver) "same sender and receiver")
//     (enforce-unit amount)
//     (enforce (> amount 0.0) "Positive amount")
//     (compose-capability (DEBIT sender))
//     (compose-capability (CREDIT receiver))
//   )

//procedure TRANSFER(sender:TyString, receiver:TyString, amount:real) returns (r:bool);

//   (defun TRANSFER-mgr:decimal
//     ( managed:decimal
//       requested:decimal
//     )

//     (let ((newbal (- managed requested)))
//       (enforce (>= newbal 0.0)
//         (format "TRANSFER exceeded for balance {}" [managed]))
//       newbal)
//   )

//procedure TRANSFER_mgr(managed:real, requested:real) returns (r:real);

//   (defcap TRANSFER_XCHAIN:bool
//     ( sender:string
//       receiver:string
//       amount:decimal
//       target-chain:string
//     )

//     @managed amount TRANSFER_XCHAIN-mgr
//     (enforce-unit amount)
//     (enforce (> amount 0.0) "Cross-chain transfers require a positive amount")
//     (compose-capability (DEBIT sender))
//   )

//procedure TRANSFER_XCHAIN(sender:TyString, receiver:TyString, amount:real, target_chain:string) returns (r:bool);

//   (defun TRANSFER_XCHAIN-mgr:decimal
//     ( managed:decimal
//       requested:decimal
//     )

//     (enforce (>= managed requested)
//       (format "TRANSFER_XCHAIN exceeded for balance {}" [managed]))
//     0.0
//   )

//procedure TRANSFER_XCHAIN_mgr(managed:real, requested:real) returns (r:real);

//   (defcap TRANSFER_XCHAIN_RECD:bool
//     ( sender:string
//       receiver:string
//       amount:decimal
//       source-chain:string
//     )
//     @event true
//   )

//procedure TRANSFER_XCHAIN_RECD(sender:TyString, receiver:TyString, amount:real, source_chain:string) returns (r:bool);

//   ; v3 capabilities
//   (defcap RELEASE_ALLOCATION
//     ( account:string
//       amount:decimal
//     )
//     @doc "Event for allocation release, can be used for sig scoping."
//     @event true
//   )

//procedure RELEASE_ALLOCATION(account:TyString, amount:real);

//   ; --------------------------------------------------------------------------
//   ; Constants

//   (defconst COIN_CHARSET CHARSET_LATIN1
//     "The default coin contract character set")

const COIN_CHARSET : string;

//   (defconst MINIMUM_PRECISION 12
//     "Minimum allowed precision for coin transactions")

const MINIMUM_PRECISION : int;
// axiom (MINIMUM_PRECISION == 12);

//   (defconst MINIMUM_ACCOUNT_LENGTH 3
//     "Minimum account length admissible for coin accounts")

const MINIMUM_ACCOUNT_LENGTH : int;
// axiom (MINIMUM_ACCOUNT_LENGTH == 3);

//   (defconst MAXIMUM_ACCOUNT_LENGTH 256
//     "Maximum account name length admissible for coin accounts")

const MAXIMUM_ACCOUNT_LENGTH : int;
// axiom (MAXIMUM_ACCOUNT_LENGTH == 256);

//   (defconst VALID_CHAIN_IDS (map (int-to-str 10) (enumerate 0 19))
//     "List of all valid Chainweb chain ids")

// const VALID_CHAIN_IDS : [int]int; //jww (2022-08-05): ?

//   ; --------------------------------------------------------------------------
//   ; Utilities

//   (defun enforce-unit:bool (amount:decimal)
//     @doc "Enforce minimum precision allowed for coin transactions"

//     (enforce
//       (= (floor amount MINIMUM_PRECISION)
//          amount)
//       (format "Amount violates minimum precision: {}" [amount]))
//     )

//procedure enforce_unit(amount:real) returns (r:bool);

//   (defun validate-account (account:string)
//     @doc "Enforce that an account name conforms to the coin contract \
//          \minimum and maximum length requirements, as well as the    \
//          \latin-1 character set."

//     (enforce
//       (is-charset COIN_CHARSET account)
//       (format
//         "Account does not conform to the coin contract charset: {}"
//         [account]))

//     (let ((account-length (length account)))

//       (enforce
//         (>= account-length MINIMUM_ACCOUNT_LENGTH)
//         (format
//           "Account name does not conform to the min length requirement: {}"
//           [account]))

//       (enforce
//         (<= account-length MAXIMUM_ACCOUNT_LENGTH)
//         (format
//           "Account name does not conform to the max length requirement: {}"
//           [account]))
//       )
//   )

//procedure validate_account(account:TyString);

//   ; --------------------------------------------------------------------------
//   ; Coin Contract

//   (defun gas-only ()
//     "Predicate for gas-only user guards."
//     (require-capability (GAS)))

//procedure gas_only();

//   (defun gas-guard (guard:guard)
//     "Predicate for gas + single key user guards"
//     (enforce-one
//       "Enforce either the presence of a GAS cap or keyset"
//       [ (gas-only)
//         (enforce-guard guard)
//       ]))

//procedure gas_guard(guard:TyGuard);

//   (defun buy-gas:string (sender:string total:decimal)
//     @doc "This function describes the main 'gas buy' operation. At this point \
//     \MINER has been chosen from the pool, and will be validated. The SENDER   \
//     \of this transaction has specified a gas limit LIMIT (maximum gas) for    \
//     \the transaction, and the price is the spot price of gas at that time.    \
//     \The gas buy will be executed prior to executing SENDER's code."

//     @model [ (property (> total 0.0))
//              (property (valid-account sender))
//            ]

//     (validate-account sender)

//     (enforce-unit total)
//     (enforce (> total 0.0) "gas supply must be a positive quantity")

//     (require-capability (GAS))
//     (with-capability (DEBIT sender)
//       (debit sender total))
//     )

//procedure buy_gas(sender:TyString, total:real) returns (r:TyString);

//   (defun redeem-gas:string (miner:string miner-guard:guard sender:string total:decimal)
//     @doc "This function describes the main 'redeem gas' operation. At this    \
//     \point, the SENDER's transaction has been executed, and the gas that      \
//     \was charged has been calculated. MINER will be credited the gas cost,    \
//     \and SENDER will receive the remainder up to the limit"

//     @model [ (property (> total 0.0))
//              (property (valid-account sender))
//              (property (valid-account miner))
//            ]

//     (validate-account sender)
//     (validate-account miner)
//     (enforce-unit total)

//     (require-capability (GAS))
//     (let*
//       ((fee (read-decimal "fee"))
//        (refund (- total fee)))

//       (enforce-unit fee)
//       (enforce (>= fee 0.0)
//         "fee must be a non-negative quantity")

//       (enforce (>= refund 0.0)
//         "refund must be a non-negative quantity")

//       (emit-event (TRANSFER sender miner fee)) ;v3

//         ; directly update instead of credit
//       (with-capability (CREDIT sender)
//         (if (> refund 0.0)
//           (with-read coin-table sender
//             { "balance" := balance }
//             (update coin-table sender
//               { "balance": (+ balance refund) }))

//           "noop"))

//       (with-capability (CREDIT miner)
//         (if (> fee 0.0)
//           (credit miner miner-guard fee)
//           "noop"))
//       )

//     )

//procedure redeem_gas(miner:TyString, miner_guard:TyGuard, sender:string, total:real) returns (r:TyString);

//   (defun create-account:string (account:string guard:guard)
//     @model [ (property (valid-account account)) ]

//     (validate-account account)
//     (enforce-reserved account guard)

//     (insert coin-table account
//       { "balance" : 0.0
//       , "guard"   : guard
//       })
//     )

//procedure create_account(account:string, guard:TyGuard) returns (r:TyString);

//   (defun get-balance:decimal (account:string)
//     (with-read coin-table account
//       { "balance" := balance }
//       balance
//       )
//     )

//procedure get_balance(account:string) returns (r:real);

//   (defun details:object{fungible-v2.account-details}
//     ( account:string )
//     (with-read coin-table account
//       { "balance" := bal
//       , "guard" := g }
//       { "account" : account
//       , "balance" : bal
//       , "guard": g })
//     )

//procedure details(account:string) returns (r:TyObject);

//   (defun rotate:string (account:string new-guard:guard)
//     (with-capability (ROTATE account)
//       (with-read coin-table account
//         { "guard" := old-guard }

//         (enforce-guard old-guard)

//         (update coin-table account
//           { "guard" : new-guard }
//           )))
//     )

//procedure rotate(account:string, new_guard:TyGuard) returns (r:TyString);

//   (defun precision:integer
//     ()
//     MINIMUM_PRECISION)

//procedure precision() returns (r:int);

//   (defun transfer:string (sender:string receiver:string amount:decimal)
//     @model [ (property conserves-mass)
//              (property (> amount 0.0))
//              (property (valid-account sender))
//              (property (valid-account receiver))
//              (property (!= sender receiver)) ]

//     (enforce (!= sender receiver)
//       "sender cannot be the receiver of a transfer")

//     (validate-account sender)
//     (validate-account receiver)

//     (enforce (> amount 0.0)
//       "transfer amount must be positive")

//     (enforce-unit amount)

//     (with-capability (TRANSFER sender receiver amount)
//       (debit sender amount)
//       (with-read coin-table receiver
//         { "guard" := g }

//         (credit receiver g amount))
//       )
//     )

// method transfer(sender:TyString, receiver:TyString, amount:real) returns (r:TyString);
//   modifies coin_table#balance;

//   requires amount >= 0.0;
//   requires valid_account(sender);
//   requires valid_account(receiver);
//   requires sender != receiver;
// {
//   call validate_account(sender);
//   call validate_account(receiver);

  // var keys : [int]TyString;
  // var changes : [TyString]real;
  // var delta : real;
  // var i : int;

  // keys[0] := sender;
  // keys[1] := receiver;
  // assume len(keys) == 2;

  // changes[sender]   := - amount;
  // changes[receiver] := amount;

  // call delta := map_sum(keys, changes);
  // assert delta == 0.0;

  // i := 0;
  // while (i < len(keys))
  //   invariant 0 <= i && i <= len(keys);
  // {
  //   coin_table#balance[keys[i]] := coin_table#balance[keys[i]] + changes[keys[i]];
  // }
// }

//   (defun transfer-create:string
//     ( sender:string
//       receiver:string
//       receiver-guard:guard
//       amount:decimal )

//     @model [ (property conserves-mass) ]

//     (enforce (!= sender receiver)
//       "sender cannot be the receiver of a transfer")

//     (validate-account sender)
//     (validate-account receiver)

//     (enforce (> amount 0.0)
//       "transfer amount must be positive")

//     (enforce-unit amount)

//     (with-capability (TRANSFER sender receiver amount)
//       (debit sender amount)
//       (credit receiver receiver-guard amount))
//     )

//procedure transfer_create(sender:string, receiver:string, receiver_guard:TyGuard, amount:real) returns (r:TyString);

//   (defun coinbase:string (account:string account-guard:guard amount:decimal)
//     @doc "Internal function for the initial creation of coins.  This function \
//     \cannot be used outside of the coin contract."

//     @model [ (property (valid-account account))
//              (property (> amount 0.0))
//            ]

//     (validate-account account)
//     (enforce-unit amount)

//     (require-capability (COINBASE))
//     (emit-event (TRANSFER "" account amount)) ;v3
//     (with-capability (CREDIT account)
//       (credit account account-guard amount))
//     )

//procedure coinbase(account:string, account_guard:TyGuard, amount:real) returns (r:TyString);

//   (defun remediate:string (account:string amount:decimal)
//     @doc "Allows for remediation transactions. This function \
//          \is protected by the REMEDIATE capability"
//     @model [ (property (valid-account account))
//              (property (> amount 0.0))
//            ]

//     (validate-account account)

//     (enforce (> amount 0.0)
//       "Remediation amount must be positive")

//     (enforce-unit amount)

//     (require-capability (REMEDIATE))
//     (emit-event (TRANSFER "" account amount)) ;v3
//     (with-read coin-table account
//       { "balance" := balance }

//       (enforce (<= amount balance) "Insufficient funds")

//       (update coin-table account
//         { "balance" : (- balance amount) }
//         ))
//     )

//procedure remediate(account:string, amount:real) returns (r:TyString);

//   (defpact fund-tx (sender:string miner:string miner-guard:guard total:decimal)
//     @doc "'fund-tx' is a special pact to fund a transaction in two steps,     \
//     \with the actual transaction transpiring in the middle:                   \
//     \                                                                         \
//     \  1) A buying phase, debiting the sender for total gas and fee, yielding \
//     \     TX_MAX_CHARGE.                                                      \
//     \  2) A settlement phase, resuming TX_MAX_CHARGE, and allocating to the   \
//     \     coinbase account for used gas and fee, and sender account for bal-  \
//     \     ance (unused gas, if any)."

//     @model [ (property (> total 0.0))
//              (property (valid-account sender))
//              (property (valid-account miner))
//              ;(property conserves-mass) not supported yet
//            ]

//     (step (buy-gas sender total))
//     (step (redeem-gas miner miner-guard sender total))
//     )

//procedure fund_tx(sender:string, miner:string, miner_guard:TyGuard, total:real);

//   (defun debit:string (account:string amount:decimal)
//     @doc "Debit AMOUNT from ACCOUNT balance"

//     @model [ (property (> amount 0.0))
//              (property (valid-account account))
//            ]

//     (validate-account account)

//     (enforce (> amount 0.0)
//       "debit amount must be positive")

//     (enforce-unit amount)

//     (require-capability (DEBIT account))
//     (with-read coin-table account
//       { "balance" := balance }

//       (enforce (<= amount balance) "Insufficient funds")

//       (update coin-table account
//         { "balance" : (- balance amount) }
//         ))
//     )

//procedure debit(account:string, amount:real) returns (r:TyString);

//   (defun credit:string (account:string guard:guard amount:decimal)
//     @doc "Credit AMOUNT to ACCOUNT balance"

//     @model [ (property (> amount 0.0))
//              (property (valid-account account))
//            ]

//     (validate-account account)

//     (enforce (> amount 0.0) "credit amount must be positive")
//     (enforce-unit amount)

//     (require-capability (CREDIT account))
//     (with-default-read coin-table account
//       { "balance" : -1.0, "guard" : guard }
//       { "balance" := balance, "guard" := retg }
//       ; we don't want to overwrite an existing guard with the user-supplied one
//       (enforce (= retg guard)
//         "account guards do not match")

//       (let ((is-new
//              (if (= balance -1.0)
//                  (enforce-reserved account guard)
//                false)))

//         (write coin-table account
//           { "balance" : (if is-new amount (+ balance amount))
//           , "guard"   : retg
//           }))
//       ))

//procedure credit(account:string, guard:TyGuard, amount:real) returns (r:TyString);

//   (defun check-reserved:string (account:string)
//     " Checks ACCOUNT for reserved name and returns type if \
//     \ found or empty string. Reserved names start with a \
//     \ single char and colon, e.g. 'c:foo', which would return 'c' as type."
//     (let ((pfx (take 2 account)))
//       (if (= ":" (take -1 pfx)) (take 1 pfx) "")))

//procedure check_reserved(account:string) returns (r:TyString);

//   (defun enforce-reserved:bool (account:string guard:guard)
//     @doc "Enforce reserved account name protocols."
//     (if (validate-principal guard account)
//       true
//       (let ((r (check-reserved account)))
//         (if (= r "")
//           true
//           (if (= r "k")
//             (enforce false "Single-key account protocol violation")
//             (enforce false
//               (format "Reserved protocol guard violation: {}" [r]))
//             )))))

//procedure enforce_reserved(account:string, guard:TyGuard) returns (r:bool);

//   (defschema crosschain-schema
//     @doc "Schema for yielded value in cross-chain transfers"
//     receiver:string
//     receiver-guard:guard
//     amount:decimal
//     source-chain:string)

//   (defpact transfer-crosschain:string
//     ( sender:string
//       receiver:string
//       receiver-guard:guard
//       target-chain:string
//       amount:decimal )

//     @model [ (property (> amount 0.0))
//              (property (valid-account sender))
//              (property (valid-account receiver))
//            ]

//     (step
//       (with-capability
//         (TRANSFER_XCHAIN sender receiver amount target-chain)

//         (validate-account sender)
//         (validate-account receiver)

//         (enforce (!= "" target-chain) "empty target-chain")
//         (enforce (!= (at 'chain-id (chain-data)) target-chain)
//           "cannot run cross-chain transfers to the same chain")

//         (enforce (> amount 0.0)
//           "transfer quantity must be positive")

//         (enforce-unit amount)

//         (enforce (contains target-chain VALID_CHAIN_IDS)
//           "target chain is not a valid chainweb chain id")

//         ;; step 1 - debit delete-account on current chain
//         (debit sender amount)
//         (emit-event (TRANSFER sender "" amount))

//         (let
//           ((crosschain-details:object{crosschain-schema}
//             { "receiver" : receiver
//             , "receiver-guard" : receiver-guard
//             , "amount" : amount
//             , "source-chain" : (at 'chain-id (chain-data))
//             }))
//           (yield crosschain-details target-chain)
//           )))

//     (step
//       (resume
//         { "receiver" := receiver
//         , "receiver-guard" := receiver-guard
//         , "amount" := amount
//         , "source-chain" := source-chain
//         }

//         (emit-event (TRANSFER "" receiver amount))
//         (emit-event (TRANSFER_XCHAIN_RECD "" receiver amount source-chain))

//         ;; step 2 - credit create account on target chain
//         (with-capability (CREDIT receiver)
//           (credit receiver receiver-guard amount))
//         ))
//     )


//   ; --------------------------------------------------------------------------
//   ; Coin allocations

//   (defschema allocation-schema
//     @doc "Genesis allocation registry"
//     ;@model [ (invariant (>= balance 0.0)) ]

//     balance:decimal
//     date:time
//     guard:guard
//     redeemed:bool)

//   (deftable allocation-table:{allocation-schema})

//   (defun create-allocation-account
//     ( account:string
//       date:time
//       keyset-ref:string
//       amount:decimal
//     )

//     @doc "Add an entry to the coin allocation table. This function \
//          \also creates a corresponding empty coin contract account \
//          \of the same name and guard. Requires GENESIS capability. "

//     @model [ (property (valid-account account)) ]

//     (require-capability (GENESIS))

//     (validate-account account)
//     (enforce (>= amount 0.0)
//       "allocation amount must be non-negative")

//     (enforce-unit amount)

//     (let
//       ((guard:guard (keyset-ref-guard keyset-ref)))

//       (create-account account guard)

//       (insert allocation-table account
//         { "balance" : amount
//         , "date" : date
//         , "guard" : guard
//         , "redeemed" : false
//         })))

//procedure create_allocated_account(account:string, date:TyTime, keyset_ref:TyString, amount:real);

//   (defun release-allocation
//     ( account:string )

//     @doc "Release funds associated with allocation ACCOUNT into main ledger.   \
//          \ACCOUNT must already exist in main ledger. Allocation is deactivated \
//          \after release."
//     @model [ (property (valid-account account)) ]

//     (validate-account account)

//     (with-read allocation-table account
//       { "balance" := balance
//       , "date" := release-time
//       , "redeemed" := redeemed
//       , "guard" := guard
//       }

//       (let ((curr-time:time (at 'block-time (chain-data))))

//         (enforce (not redeemed)
//           "allocation funds have already been redeemed")

//         (enforce
//           (>= curr-time release-time)
//           (format "funds locked until {}. current time: {}" [release-time curr-time]))

//         (with-capability (RELEASE_ALLOCATION account balance)

//         (enforce-guard guard)

//         (with-capability (CREDIT account)
//           (emit-event (TRANSFER "" account balance))
//           (credit account guard balance)

//           (update allocation-table account
//             { "redeemed" : true
//             , "balance" : 0.0
//             })

//           "Allocation successfully released to main ledger"))
//     )))

//procedure release_allocation(account:string);

// )

}
