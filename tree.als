module bintree

var abstract sig AbsNode
{
  var left: lone AbsNode,
  var right: lone AbsNode
}

var one sig Root extends AbsNode{}
var sig Leaf extends AbsNode {}
var sig Node extends AbsNode {}

// fact that we have more than one node
fact
{
  always // hint for me: temporal operator,- certain properties will always be set in each step
  {
    #AbsNode > 1
  }
}

// set of all the "children"
fun children: set AbsNode
{
  AbsNode.(left + right)
}

// root has no parents: rot is not a child
fact
{
  always
  {
    Root not in children
  }
}

// set of "parents"
fun parents: set AbsNode
{
  (left + right).AbsNode
}

fun all_children_of[n: AbsNode]: set AbsNode
{
  n.^(left + right)
}

/*
// nods should have only one parent
fun parent_of[n: AbsNode] : set AbsNode
{
  (left + right).n
  // left.n + right.n
  // the string above is incorrect too because it was like joining sets
}
*/

pred valid
{
  // say no to circles
  all n: AbsNode | n not in n.all_children_of
  // in total, we have one parent from left and right
  // all n: AbsNode | add[#left.n, #right.n] <= 1
  all n: AbsNode
  {
    one left.n implies no right.n
    one right.n implies no left.n
    lone (left + right).n
  }
}

fact
{
  always
  {
    Root not in children
    all l: Leaf
    {
      l in children
      l not in parents
    }
    all n: Node
    {
      n in children
      n in parents
    }
  }
}
// operations --------------insert------------

fun all_new_nodes: set AbsNode'
{
  AbsNode' - AbsNode
}
// new node
pred new[n: AbsNode'] // refer to the AbsNode signature but from the next moment of time
{
  n in all_new_nodes
}

pred may_add_children[n: AbsNode]
{
  no n.left or no n.right
}

// adding child
pred add_children[n: AbsNode, c: AbsNode']
{
  c.new
  n.may_add_children
  no n.left implies
  {
    right' = right
    left' = left + (n -> c) // changing "parent - child" raltions
  }
  else
  {
    left' = left;
    right' = right + (n -> c)
  }
}

// checking conditions under operation
pred add_some_child
{
  {
    one all_new_nodes
    some n: AbsNode // such that
    {
      n.may_add_children
      n.add_children[all_new_nodes]
    }
  }
  or
  {
    AbsNode' = AbsNode
    left' = left
    right' = right
  }
}

// check the correctness of the operation
// validity before and after
pred valid_and_add_implies_valid
{
  // system was valid, we added something
  // and got a valid system again
  valid implies add_some_child
}

example: run
{
  valid
  one Root
  #Leaf > 1
  #Node > 1
  valid_and_add_implies_valid
} for 5 but 2 steps