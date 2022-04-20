module bintree

var abstract sig AbsNode
{
  var left: lone AbsNode,
  var right: lone AbsNode
}

var one sig Root extends AbsNode{}
var sig Leaf extends AbsNode {}
var sig Node extends AbsNode {}

// нодов больше одного
fact
{
  always//темпоральный оператор, что всегда в каждом шаге будут задаваться определенные свойства
  {
    #AbsNode > 1
  }
}

// множество всех детей
fun children: set AbsNode
{
  AbsNode.(left + right)
}

// рут не является потомком
fact
{
  always
  {
    //Root not in AbsNode.left + AbsNode.right
    Root not in children
  }
}

// множество всех родителей
fun parents: set AbsNode
{
  (left + right).AbsNode
}

fun all_children_of[n: AbsNode]: set AbsNode
{
  n.^(left + right)
}

/*
// узлы должны иметь только одного родителя
fun parent_of[n: AbsNode] : set AbsNode
{
  (left + right).n
  // left.n + right.n тоже неверно, потому что это будет как объединение множеств

}
*/

pred valid
{
  // нет циклам!!
  all n: AbsNode | n not in n.all_children_of
  // слева и справа в сумме один родитель
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
// моделирование операций --------------insert------------

fun all_new_nodes: set AbsNode'
{
  AbsNode' - AbsNode
}
// узел новый
pred new[n: AbsNode'] // относится к сигнатуре AbsNode, но из будущего момента времени
{
  n in all_new_nodes
}

pred may_add_children[n: AbsNode]
{
  no n.left or no n.right
}

//операция добавления потомка
pred add_children[n: AbsNode, c: AbsNode']
{
  c.new
  n.may_add_children
  no n.left implies
  {
    right' = right
    left' = left + (n -> c) // меняются отношения родитель - потомок
  }
  else
  {
    left' = left;
    right' = right + (n -> c)
  }
}

// проверяет условия над операцией и проверяет ее
pred add_some_child
{
  {
    one all_new_nodes
    some n: AbsNode // такой, что
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

// проверяем корректность операции
// валидность до и после
pred valid_and_add_implies_valid
{
  // система была валидная, мы что-то добавили
  // и получили снова валидную систему
  valid implies add_some_child
  // (valid and add_some_child) implies after valid //если валидное состояние, и мы смогли добавить
}

example: run
{
  valid
  one Root
  #Leaf > 1
  #Node > 1
  valid_and_add_implies_valid
} for 5 but 2 steps