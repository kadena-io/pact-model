include "sym.dfy"

function method add(x: (string,real), y: real) : real { x.1 + y }

class coin {

var coins : map<string, real>;

constructor(db:map<string, real>)
{
  coins := db;
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

function method SumSet(s: set<(string,real)>) : (sum: real)
  ensures sum == Seq.Fold(Set.SeqOfSet(s), add, 0.0)
{
  Set.Fold(s, add, 0.0)
}

lemma Sum_SumSet(s: set<(string,real)>)
  decreases s
  ensures Sum(s) == SumSet(s)
{
  if s == {} {
    assert Sum({}) == SumSet({});
  } else {
    var item := Pick(s);
    assert Sum({item}) == SumSet({item});
    Sum_SumSet(s - { item });
    assert Sum(s - { item }) == SumSet(s - { item });
  }
}

twostate predicate conserves_mass()
  reads this
{
  SumSet(old(coins.Items)) == SumSet(coins.Items)
}

method sample_transfer(sender:string, receiver:string, amount:real)
  // this table is updated
  modifies this;

  // inputs arguments are valid
  requires amount >= 0.0;
  requires sender != receiver

  // no accounts with negative balance before or after
  requires forall k:string :: k in coins ==> coins[k] >= 0.0
  ensures forall k:string :: k in coins ==> coins[k] >= 0.0

  // sender and receiver are present before and after
  requires sender in coins
  ensures sender in coins
  requires receiver in coins
  ensures receiver in coins

  // a simple implication of the transfer
  requires coins[sender] >= amount
  ensures coins[receiver] >= amount

  // no accounts created or destroyed
  ensures forall k:string :: k in old(coins) <==> k in coins

  // conserves mass: all other account balances are unchanged
  ensures forall k:string :: k in coins && k != sender && k != receiver ==>
    old(coins[k]) == coins[k]
  // conserves mass: delta of sender + receiver is zero
  ensures old(coins[sender]) + old(coins[receiver]) ==
    coins[sender] + coins[receiver]

  ensures conserves_mass()      // equivalent to the two postconditions above
{
  coins := coins[sender   := coins[sender]   - amount];
  coins := coins[receiver := coins[receiver] + amount];
}

}
