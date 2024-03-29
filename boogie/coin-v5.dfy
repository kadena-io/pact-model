datatype Status =
  | Success
  | Failure(error: string)
{
  predicate method IsFailure() {
    this.Failure?
  }

  function method PropagateFailure(): Status
    requires IsFailure()
  {
    this
  }
}

datatype Result<T> =
  | Ok(value: T)
  | Err(error: string)
{
  predicate method IsFailure() {
    this.Err?
  }

  function method PropagateFailure<U>(): Result<U>
    requires IsFailure()
  {
    Err(this.error) // this is Result<U>.Failure(...)
  }

  function method Extract(): T
    requires !IsFailure()
  {
    this.value
  }
}

type time
type guard = string
type Object = string

datatype Value =
  | Unit
  | Integer(n: int)
  | Decimal(d: real)
  | String(s: string)

datatype Capability = Token(name:string, params:seq<Value>, value:Value)

function method enforce(b:bool, msg:string): (r: Status)
  ensures r == Success ==> b
{
  if b
    then Success
    else Failure(msg)
}

function method enforce_one(msg:string, b:seq<Status>): (r: Status)
  decreases b
  ensures r == Success ==>
    |b| > 0 && (b[0] == Success || enforce_one(msg, b[1..]) == Success)
{
  if b == []
  then Failure(msg)
  else
    if b[0] == Success
    then Success
    else enforce_one(msg, b[1..])
}

//////////////////////////////////////////////////////////////////////////////
//
// SUGAR

// (with-read coin-table account
//   { "balance" := balance }
//   ... balance ...)
//
// ==
//
// var balance := coin_table_balance[account];
// ... balance ...;

// (update coin-table account
//   { "balance" : (- balance amount) })
//
// ==
//
// coin_table_balance[account] =
//   coin_table_balance[account := balance - amount];

//////////////////////////////////////////////////////////////////////////////

// (module coin GOVERNANCE

class coin {

var capabilities : set<Capability>;
var resources : map<(string,seq<Value>),Value>;

function method require_capability(cap: Capability): (r: Status)
  reads this
  ensures r == Success ==> cap in capabilities
{
  if cap in capabilities
    then Success
    else Failure("capability has not been granted")
}

method install_capability(cap: Capability) returns (r: Status)
  modifies this
  ensures (cap.name, cap.params) in resources
{
  var Token(name, params, value) := cap;
  resources := resources[ (name, params) := value ];
}

//   @doc "'coin' represents the Kadena Coin Contract. This contract provides both the \
//   \buy/redeem gas support in the form of 'fund-tx', as well as transfer,       \
//   \credit, debit, coinbase, account creation and query, as well as SPV burn    \
//   \create. To access the coin contract, you may use its fully-qualified name,  \
//   \or issue the '(use coin)' command in the body of a module declaration."

//   @model
//     [ (defproperty conserves-mass
//         (= (column-delta coin-table 'balance) 0.0))

function account_balances(m: map<string, real>, keys: seq<string>): real
  requires forall k | k in keys :: k in m
  decreases keys
{
  if keys == []
  then 0.0
  else m[keys[0]] + account_balances(m, keys[1..])
}

// An induction principal about account_balances that is needed whenever
// conserves_mass is used, both before and after any modifications.
lemma {:induction m} account_balances_n(m: map<string, real>, keys: seq<string>)
  requires |keys| > 0
  requires forall k | k in keys :: k in m
  ensures account_balances(m, keys) == m[keys[0]] + account_balances(m, keys[1..])
{
}

// conserves-mass says that given a set of account keys, the net balance of
// those accounts before and after must be zero. All other accounts must
// remain unchanged.
predicate conserves_mass(before: map<string, real>, after: map<string, real>, keys: seq<string>)
  requires forall k | k in keys :: k in before && k in after
{
  && (forall k | k !in keys && k in before && k in after :: before[k] == after[k])
  && account_balances(before, keys) == account_balances(after, keys)
}

//       (defproperty valid-account (account:string)
//         (and
//           (>= (length account) 3)
//           (<= (length account) 256)))
//     ]

predicate method valid_account(account:string) {
  |account| >= 3 && |account| <= 256
}

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

var coin_table_balance : map<string, real>;

constructor(pre_coin_table_balance:map<string, real>)
  requires forall k | k in pre_coin_table_balance :: pre_coin_table_balance[k] >= 0.0
  ensures coin_table_balance == pre_coin_table_balance
{
  coin_table_balance := pre_coin_table_balance;
}

predicate Valid()
  reads this
{
  forall k | k in coin_table_balance ::
    valid_account(k) && coin_table_balance[k] >= 0.0
}

//   ; --------------------------------------------------------------------------
//   ; Capabilities

//   (defcap GOVERNANCE ()
//     (enforce false "Enforce non-upgradeability"))

function method GOVERNANCE(): Capability
{
  Token("GOVERNANCE", [], Unit)
}

method GOVERNANCE__predicate() returns (r: Status)
{
  :-enforce(false, "Enforce non-upgradeability");
  return Success;
}

//   (defcap GAS ()
//     "Magic capability to protect gas buy and redeem"
//     true)

function method GAS(): Capability
{
  Token("GAS", [], Unit)
}

//   (defcap COINBASE ()
//     "Magic capability to protect miner reward"
//     true)

function method COINBASE(): Capability
{
  Token("COINBASE", [], Unit)
}

//   (defcap GENESIS ()
//     "Magic capability constraining genesis transactions"
//     true)

function method GENESIS(): Capability
{
  Token("GENESIS", [], Unit)
}

//   (defcap REMEDIATE ()
//     "Magic capability for remediation transactions"
//     true)

function method REMEDIATE(): Capability
{
  Token("REMEDIATE", [], Unit)
}

//   (defcap DEBIT (sender:string)
//     "Capability for managing debiting operations"
//     (enforce-guard (at 'guard (read coin-table sender)))
//     (enforce (!= sender "") "valid sender"))

function method DEBIT(sender:string): Capability
{
  Token("DEBIT", [String(sender)], Unit)
}

// method DEBIT__predicate(sender:string) returns (r:Status)
// {
//   jww (2022-08-08): TODO
// }

//   (defcap CREDIT (receiver:string)
//     "Capability for managing crediting operations"
//     (enforce (!= receiver "") "valid receiver"))

function method CREDIT(receiver:string): Capability
{
  Token("CREDIT", [String(receiver)], Unit)
}

method CREDIT__predicate(receiver:string) returns (r:Status)
{
  return Success;
}

//   (defcap ROTATE (account:string)
//     @doc "Autonomously managed capability for guard rotation"
//     @managed
//     true)

// method ROTATE(account:string) returns (r:Status)
// {
//   jww (2022-08-08): TODO
// }

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

// method TRANSFER(sender:string, receiver:string, amount:real) returns (r:Status)
// {
//   jww (2022-08-08): TODO
// }

//   (defun TRANSFER-mgr:decimal
//     ( managed:decimal
//       requested:decimal
//     )

//     (let ((newbal (- managed requested)))
//       (enforce (>= newbal 0.0)
//         (format "TRANSFER exceeded for balance {}" [managed]))
//       newbal)
//   )

// method TRANSFER_mgr(managed:real, requested:real) returns (r:real)
// {
//   jww (2022-08-08): TODO
// }

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

// method TRANSFER_XCHAIN(sender:string, receiver:string, amount:real, target_chain:string) returns (r:Status)
// {
//   jww (2022-08-08): TODO
// }

//   (defun TRANSFER_XCHAIN-mgr:decimal
//     ( managed:decimal
//       requested:decimal
//     )

//     (enforce (>= managed requested)
//       (format "TRANSFER_XCHAIN exceeded for balance {}" [managed]))
//     0.0
//   )

// method TRANSFER_XCHAIN_mgr(managed:real, requested:real) returns (r:real)
// {
//   jww (2022-08-08): TODO
// }

//   (defcap TRANSFER_XCHAIN_RECD:bool
//     ( sender:string
//       receiver:string
//       amount:decimal
//       source-chain:string
//     )
//     @event true
//   )

// method TRANSFER_XCHAIN_RECD(sender:string, receiver:string, amount:real, source_chain:string) returns (r:Status)
// {
//   jww (2022-08-08): TODO
// }

//   ; v3 capabilities
//   (defcap RELEASE_ALLOCATION
//     ( account:string
//       amount:decimal
//     )
//     @doc "Event for allocation release, can be used for sig scoping."
//     @event true
//   )

function method RELEASE_ALLOCATION(account:string, amount:real): Capability
{
  Token("RELEASE_ALLOCATION", [String(account), Decimal(amount)], Unit)
}

//   ; --------------------------------------------------------------------------
//   ; Constants

//   (defconst COIN_CHARSET CHARSET_LATIN1
//     "The default coin contract character set")

// const COIN_CHARSET : string;

//   (defconst MINIMUM_PRECISION 12
//     "Minimum allowed precision for coin transactions")

const MINIMUM_PRECISION : int := 12;

//   (defconst MINIMUM_ACCOUNT_LENGTH 3
//     "Minimum account length admissible for coin accounts")

const MINIMUM_ACCOUNT_LENGTH : int := 3;

//   (defconst MAXIMUM_ACCOUNT_LENGTH 256
//     "Maximum account name length admissible for coin accounts")

const MAXIMUM_ACCOUNT_LENGTH : int := 256;

//   (defconst VALID_CHAIN_IDS (map (int-to-str 10) (enumerate 0 19))
//     "List of all valid Chainweb chain ids")

const VALID_CHAIN_IDS : seq<string> := [
  "0000000000",
  "0000000001",
  "0000000002",
  "0000000003",
  "0000000004",
  "0000000005",
  "0000000006",
  "0000000007",
  "0000000008",
  "0000000009",
  "0000000010",
  "0000000011",
  "0000000012",
  "0000000013",
  "0000000014",
  "0000000015",
  "0000000016",
  "0000000017",
  "0000000018",
  "0000000019"
  ];

//   ; --------------------------------------------------------------------------
//   ; Utilities

//   (defun enforce-unit:bool (amount:decimal)
//     @doc "Enforce minimum precision allowed for coin transactions"

//     (enforce
//       (= (floor amount MINIMUM_PRECISION)
//          amount)
//       (format "Amount violates minimum precision: {}" [amount]))
//     )

function method floored(amount: real, prec: real): real
  requires prec > 0.0
{
  (amount * prec).Floor as real / prec
}

function method enforce_unit(amount:real): (r: Status)
  ensures r == Success ==>
    floored(amount, MINIMUM_PRECISION as real) == amount
{
  enforce(floored(amount, MINIMUM_PRECISION as real) == amount,
    "Amount violates minimum precision")
}

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

method validate_account(account:string) returns (r: Status)
  ensures r == Success ==> valid_account(account)
{
  var account_length := |account|;
  :- enforce(
       account_length >= MINIMUM_ACCOUNT_LENGTH,
       "Account name does not conform to the min length requirement");
  :- enforce(
       account_length <= MAXIMUM_ACCOUNT_LENGTH,
       "Account name does not conform to the max length requirement");
  return Success;
}

//   ; --------------------------------------------------------------------------
//   ; Coin Contract

//   (defun gas-only ()
//     "Predicate for gas-only user guards."
//     (require-capability (GAS)))

function method gas_only(): Status
  reads this
{
  require_capability(GAS())
}

//   (defun gas-guard (guard:guard)
//     "Predicate for gas + single key user guards"
//     (enforce-one
//       "Enforce either the presence of a GAS cap or keyset"
//       [ (gas-only)
//         (enforce-guard guard)
//       ]))

function method gas_guard(guard:guard): Status
  reads this
{
  enforce_one(
    "Enforce either the presence of a GAS cap or keyset",
    [ gas_only()// ,
      // enforce_guard(guard)
    ])
}

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

method buy_gas(sender:string, total:real) returns (r: Status)
  modifies this

  requires sender in coin_table_balance
  requires Valid()
{
  :- validate_account(sender);
  :- enforce_unit(total);
  :- enforce(total > 0.0, "gas supply must be a positive quantity");
  :- require_capability(GAS());

  var caps := capabilities;
  capabilities := capabilities + { DEBIT(sender) };
  var res1 := debit(sender, total);
  if res1.IsFailure() {
    capabilities := caps;
    return res1;
  } else {
    capabilities := caps;
  }

  return Success;
}

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

// method redeem_gas(miner:string, miner_guard:guard, sender:string, total:real) returns (r:Status)
// {
//   jww (2022-08-08): TODO
// }

//   (defun create-account:string (account:string guard:guard)
//     @model [ (property (valid-account account)) ]

//     (validate-account account)
//     (enforce-reserved account guard)

//     (insert coin-table account
//       { "balance" : 0.0
//       , "guard"   : guard
//       })
//     )

// method create_account(account:string, guard:guard) returns (r:Status)
// {
//   jww (2022-08-08): TODO
// }

//   (defun get-balance:decimal (account:string)
//     (with-read coin-table account
//       { "balance" := balance }
//       balance
//       )
//     )

function method get_balance(account:string): real
  reads this
  requires account in coin_table_balance
{
  var balance := coin_table_balance[account];
  balance
}

//   (defun details:object{fungible-v2.account-details}
//     ( account:string )
//     (with-read coin-table account
//       { "balance" := bal
//       , "guard" := g }
//       { "account" : account
//       , "balance" : bal
//       , "guard": g })
//     )

// method details(account:string) returns (r:Object)
// {
//   jww (2022-08-08): TODO
// }

//   (defun rotate:string (account:string new-guard:guard)
//     (with-capability (ROTATE account)
//       (with-read coin-table account
//         { "guard" := old-guard }

//         (enforce-guard old-guard)

//         (update coin-table account
//           { "guard" : new-guard }
//           )))
//     )

// method rotate(account:string, new_guard:guard) returns (r:Status)
// {
//   jww (2022-08-08): TODO
// }

//   (defun precision:integer
//     ()
//     MINIMUM_PRECISION)

function method precision(): int
{
  MINIMUM_PRECISION
}

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

method transfer(sender:string, receiver:string, amount:real) returns (r:Status)
  modifies this;

  // no accounts with negative balance before or after
  requires Valid()
  ensures Valid()

  // sender and receiver are present before and after
  requires sender in coin_table_balance
  requires receiver in coin_table_balance
  ensures coin_table_balance.Keys == old(coin_table_balance.Keys)

  // a simple implication of the transfer
  requires coin_table_balance[sender] >= amount
  ensures r == Success ==> coin_table_balance[receiver] >= amount

  ensures r == Success ==>
    conserves_mass(old(coin_table_balance), coin_table_balance, [sender, receiver])
{
  :- enforce(sender != receiver, "sender cannot be the receiver of a transfer");
  :- validate_account(sender);
  :- validate_account(receiver);
  :- enforce(amount > 0.0, "transfer amount must be positive");
  :- enforce_unit(amount);

  account_balances_n(coin_table_balance, [sender, receiver]);

  var caps := capabilities;

  // This is the logic of "with-capability", but since Dafny is not
  // higher-order we cannot use such a special form here.
  capabilities := capabilities + { DEBIT(sender) };
  {
    var res := debit(sender, amount);
    if res.IsFailure() {
      capabilities := caps;
      return res;
    } else {
      capabilities := caps;
    }
  }

  capabilities := capabilities + { CREDIT(receiver) };
  {
    var g : guard := "";
    var res := credit(receiver, g, amount);
    if res.IsFailure() {
      capabilities := caps;
      return res;
    } else {
      capabilities := caps;
    }
  }

  account_balances_n(coin_table_balance, [sender, receiver]);

  return Success;
}

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

// method transfer_create(sender:string, receiver:string, receiver_guard:guard, amount:real) returns (r:Status)
// {
//   jww (2022-08-08): TODO
// }

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

// method coinbase(account:string, account_guard:guard, amount:real) returns (r:Status)
// {
//   jww (2022-08-08): TODO
// }

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

// method remediate(account:string, amount:real) returns (r:Status)
// {
//   jww (2022-08-08): TODO
// }

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

// method fund_tx(sender:string, miner:string, miner_guard:guard, total:real) returns (r:Status)
// {
//   jww (2022-08-08): TODO
// }

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

method debit(account:string, amount:real) returns (r: Status)
  modifies this

  requires Valid()
  ensures Valid()

  requires account in coin_table_balance
  ensures coin_table_balance.Keys == old(coin_table_balance.Keys)

  ensures r == Success ==>
    coin_table_balance ==
      old(coin_table_balance[account := coin_table_balance[account] - amount])
{
  :- validate_account(account);
  :- enforce(amount > 0.0, "debit amount must be positive");
  :- enforce_unit(amount);
  :- require_capability(DEBIT(account));
  :- enforce(amount <= coin_table_balance[account], "Insufficient funds");

  var balance := coin_table_balance[account];
  coin_table_balance := coin_table_balance[account := balance - amount];

  return Success;
}

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

method credit(account:string, guard:guard, amount:real) returns (r: Status)
  modifies this

  requires Valid()
  ensures Valid()

  requires account in coin_table_balance
  ensures coin_table_balance.Keys == old(coin_table_balance.Keys)

  ensures r == Success ==> coin_table_balance[account] >= amount
  ensures r == Success ==>
    coin_table_balance ==
      old(coin_table_balance[account := coin_table_balance[account] + amount])
{
  :- validate_account(account);
  :- enforce(amount > 0.0, "credit amount must be positive");
  :- enforce_unit(amount);
  :- require_capability(CREDIT(account));

  var balance := coin_table_balance[account];
  coin_table_balance := coin_table_balance[account := balance + amount];

  return Success;
}

//   (defun check-reserved:string (account:string)
//     " Checks ACCOUNT for reserved name and returns type if \
//     \ found or empty string. Reserved names start with a \
//     \ single char and colon, e.g. 'c:foo', which would return 'c' as type."
//     (let ((pfx (take 2 account)))
//       (if (= ":" (take -1 pfx)) (take 1 pfx) "")))

function method check_reserved(account:string): string
{
  if |account| >= 2 && account[1] == ':' then
    account[0..1]
  else
    ""
}

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

function method validate_principal(g:guard, acct:string): bool
{
  true
}

function method enforce_reserved(account:string, guard:guard): Status
{
  if validate_principal(guard, account)
  then Success
  else
    var r := check_reserved(account);
    if r == ""
    then Success
    else
      if r == "k"
      then enforce(false, "Single-key account protocol violation")
      else enforce(false, "Reserved protocol guard violation")
}

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

// method create_allocated_account(account:string, date:time, keyset_ref:string, amount:real) returns (r:Status)
// {
//   jww (2022-08-08): TODO
// }

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

// method release_allocation(account:string) returns (r:Status)
// {
//   jww (2022-08-08): TODO
// }

// )

}
