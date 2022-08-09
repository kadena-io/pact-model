type guard = string

class coin
{
  var balance : real;
  var guard : guard;

  static predicate Valid(c: coin) reads c {
    c.balance >= 0.0
  }
}

predicate valid_account(account:string) {
  |account| >= 3 && |account| <= 256
}

predicate valid_coin_table_rows(c: map<string, coin>)
  reads set k | k in c :: c[k]
{
  forall k :: k in c ==>
    && valid_account(k)
    && coin.Valid(c[k])
}

class coin_schema
{
  var rows: map<string, coin>;

  constructor(rows_prev:map<string, coin>)
    requires valid_coin_table_rows(rows_prev)
    ensures valid_coin_table_rows(rows)
    ensures rows == rows_prev
  {
    rows := rows_prev;
  }

  function method read(account: string): (r: coin)
    requires account in rows
    requires valid_coin_table_rows(rows)
    ensures rows[account] == r
    ensures valid_coin_table_rows(rows)
    reads this, set k | k in rows :: rows[k], rows[account]
  {
    rows[account]
  }

  method update(account: string, c: coin)
    requires account in rows
    requires valid_account(account)
    requires valid_coin_table_rows(rows)
    requires c.balance >= 0.0
    ensures forall k :: k in old(rows) ==> k in rows
    ensures rows[account] == c
    ensures valid_coin_table_rows(rows)
    modifies this, rows[account]
  {
    rows := rows[account := c];
  }

  function account_balances(keys: seq<string>): real
    decreases keys
    reads this, set k | k in keys && k in rows :: rows[k]
  {
    if keys == []
    then
      0.0
    else
      var k := keys[0];
      var bal := if k in rows then rows[k].balance else 0.0;
      bal + account_balances(keys[1..])
  }

  // An induction principal about account_balances that is needed whenever
  // conserves_mass is used, both before and after any modifications.
  lemma account_balances_n()
    ensures forall keys: seq<string> :: |keys| > 0 ==>
      (forall k :: k in keys ==> k in rows) ==>
        account_balances(keys)
          == rows[keys[0]].balance + account_balances(keys[1..])
  {
  }
}

method accounts_valid(coins: coin_schema, account: string, c: coin)
  requires account in coins.rows
  requires valid_account(account)
  requires c.balance >= 0.0
  requires valid_coin_table_rows(coins.rows)
  ensures valid_coin_table_rows(coins.rows)
  modifies coins, coins.rows[account]
{
  // coins.rows := coins.rows[account := c];
  coins.update(account, c);
}

// conserves-mass says that given a set of account keys, the net balance of
// those accounts before and after must be zero. All other accounts must
// remain unchanged.
predicate conserves_mass(
  before: coin_schema, after: coin_schema, keys: seq<string>)
  reads
    before, set k | k in before.rows :: before.rows[k],
    after, set k | k in after.rows :: after.rows[k]
{
  && (forall k :: k !in keys && k in before.rows && k in after.rows ==>
       before.rows[k].balance == after.rows[k].balance)
  && before.account_balances(keys) == after.account_balances(keys)
}
