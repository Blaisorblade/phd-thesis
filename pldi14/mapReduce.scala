// Hidden code
//
// If you change the length of the hidden code, you have to
// adjust "firstline=..." in fig-primitives.tex accordingly.
//
// It should point to the first line that is not hidden.

// End of hidden code

// Abelian groups
abstract class Group[A] {
  def merge(value1: A, value2: A): A
  def inverse(value: A): A
  def zero: A
}

// Bags
type Bag[A] = collection.immutable.HashMap[A, Int]

def groupOnBags[A] = new Group[Bag[A]] {
  def merge(bag1: Bag[A], bag2: Bag[A]) = ???
  def inverse(bag: Bag[A]) = bag.map({
    case (value, count) => (value, -count)
  })
  def zero = collection.immutable.HashMap()
}

def foldBag[A, B](group: Group[B], f: A => B, bag: Bag[A]): B =
  bag.flatMap({
    case (x, c) if c >= 0 => Seq.fill(c)(f(x))
    case (x, c) if c < 0 => Seq.fill(-c)(group.inverse(f(x)))
  }).fold(group.zero)(group.merge)

// Maps
type Map[K, A] = collection.immutable.HashMap[K, A]

def groupOnMaps[K, A](group: Group[A]) = new Group[Map[K, A]] {
  def merge(dict1: Map[K, A], dict2: Map[K, A]): Map[K, A] =
    dict1.merged(dict2)({
      case ((k, v1), (_, v2)) => (k, group.merge(v1, v2))
    }).filter({
      case (k, v) => v != group.zero
    })

  def inverse(dict: Map[K, A]): Map[K, A] = dict.map({
    case (k, v) => (k, group.inverse(v))
  })

  def zero = collection.immutable.HashMap()
}

// The general map fold
def foldMapGen[K, A, B](zero: B, merge: (B, B) => B)
  (f: (K, A) => B, dict: Map[K, A]): B =
    dict.map(Function.tupled(f)).fold(zero)(merge)

// By using |\texttt{foldMap}| instead of |\texttt{foldMapGen}|, the user promises that
// |\texttt{f k}| is a homomorphism from |\texttt{groupA}| to |\texttt{groupB}| for each |\texttt{k : K}|.
def foldMap[K, A, B](groupA: Group[A], groupB: Group[B])
  (f: (K, A) => B, dict: Map[K, A]): B =
    foldMapGen(groupB.zero, groupB.merge)(f, dict)
