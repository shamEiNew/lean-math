/-
INDUCTIVE TYPES

It is remarkable that it is possible to construct a substantial edifice of
mathematics based on nothing more than the type universes, dependent arrow types,
and inductive types; everything else follows from those.
-/

#check List

#check List.cons 1 [3, 4]

#check Nat

#eval Nat.succ 3 == 3 + 1 --Underlying equality is decided by computation by evaluator

#check Nat.add

#check HAdd.hAdd -- Heterogeneous addition

--Example of a simple inductive type: weekday
--A type with several no-argument constructors behaves like an enum.

inductive Weekday where
  | monday : Weekday
  | tuesday : Weekday
  | wednesday : Weekday
  | thursday : Weekday
  | friday : Weekday
  | saturday : Weekday
  | sunday : Weekday

-- Pattern match on each constructor of Weekday and map it to its Nat position.
def numberOfDay (day : Weekday) : Nat :=
  match day with
  | Weekday.monday => 1
  | Weekday.tuesday => 2
  | Weekday.wednesday => 3
  | Weekday.thursday => 4
  | Weekday.friday => 5
  | Weekday.saturday => 6
  | Weekday.sunday => 7

#eval numberOfDay Weekday.friday

#print numberOfDay

set_option pp.all true

-- Nat.rec is the recursor auto-generated for the Nat inductive type.
-- Its `motive` argument plays the role of "the property/type we want, as a function of n"
-- (i.e. the predicate/goal we are building or proving, indexed by the Nat).
#print Nat.rec --predicat acting on natural numbers motive is like Predicar
#print numberOfDay

-- Ordinary pattern-matching definition of factorial (elaborates to Nat.rec under the hood).
def factorial : Nat → Nat
  | 0 => 1
  | n+1 => (n+1) * factorial n

  -- Same factorial written directly in terms of Nat.rec:
  -- base case 1 for zero, and (n+1) * ih for succ, where ih is the recursive result on n.
  def fact : Nat → Nat :=
    Nat.rec 1 (fun n ih => (n+1) * ih)

#eval fact 1


namespace Weekday

-- Cyclic successor function over the days of the week.
def next (day : Weekday): Weekday :=
  match day with
  | monday => tuesday
  | tuesday => wednesday
  | wednesday => thursday
  | thursday => friday
  | friday => saturday
  | saturday => sunday
  | sunday => monday

-- Cyclic predecessor function over the days of the week.
def previous (day : Weekday): Weekday :=
  match day with
  | monday => sunday
  | tuesday => monday
  | wednesday => tuesday
  | thursday => wednesday
  | friday => thursday
  | saturday => friday
  | sunday => saturday

-- next and previous are inverse; each case reduces to rfl by computation.
theorem nextprevious (day : Weekday) : next (previous day) = day := by
  cases day <;> rfl

-- next and previous also commute with each other.
theorem nextprevious_same (day : Weekday) : next (previous day) = previous (next day) := by
  cases day <;> rfl

end Weekday

/-
Constructors with Arguments.
The argument motive in `prod_example`is used to specify the type of the object you want to construct,
and it is a function because it may depend on the pair.
that a type with multiple constructors is disjunctive: an element of `Sum α β`
is either of the form `inl a` or of the form `inl b`.
-/

namespace Hidden

-- Single Constructor with multiple arguments : Conjunctive
-- A Prod value always carries both an α and a β together (logical AND, structurally).
inductive Prod (α : Type u) (β : Type v)
  | mk : α → β → Prod α β

-- Multiple constructors ``inl` and `inr`: Disjunctive
-- A Sum value is either an α or a β, never both (logical OR, structurally).
inductive Sum (α : Type u) (β : Type v) where
  | inl : α → Sum α β
  | inr : β → Sum α β

#check Prod.casesOn

--Extracts the first element from (a, b)
def fst_element (p : Prod α β):α :=
  match p with
  | Prod.mk a b => a

#eval fst_element (Prod.mk "s" "m")
#eval fst_element (Prod.mk 1 2)
#eval fst_element (Prod.mk (-0.5) 1)


-- casesOn version of extracting/combining fields from a Prod, motive fixed to Nat here.
def prod_example (p : Prod Bool Nat) : Nat :=
  Prod.casesOn (motive := fun _ => Nat) p
    (fun b n => cond b (2 * n) (2 * n + 1))

#eval prod_example (Prod.mk true 3)

#check (true, 3)
#check Prod.mk true 3

#check Sum.casesOn

-- casesOn over Sum: one branch per constructor (inl, inr), each returning Nat.
def sum_example (s : Sum Nat Nat) : Nat :=
  Sum.casesOn (motive := fun _ => Nat) s
    (fun n => 2 * n)
    (fun n => 2 * n + 1)

--Note that motive is implict and can be infered from the types
def sum_example_1 (s : Sum Nat Nat) : Nat :=
  Sum.casesOn s
    (fun n => 2 * n)
    (fun n => 2 * n + 1)

#eval sum_example (Sum.inl 3)
#eval sum_example_1 (Sum.inr 3)

/-
An arbitrary inductive type can include both features, by having any number of constructors,
each of which takes any number of arguments.
-/
-- Same idea as Prod, but with named constructor arguments (fst, snd).
inductive Prod1 (α : Type u) (β : Type v) where
  | mk (fst : α) (snd : β) : Prod1 α β

#check Prod1.mk
/-
structures are special case of inductive types as it
allows to construct named arguments and infers the constructor
-/

-- `structure` sugar: single-constructor inductive type with named projection functions.
structure Prod2 (α : Type u) (β : Type v) where
  mk ::
  fst : α
  snd : β
/-
If we don't name the constructor lean default name is mk
-/

-- Same as Prod2 but constructor explicitly named `mb` instead of the default `mk`.
structure Prod3 (α : Type u) (β : Type v) where
  mb ::
  fst : α
  snd : β

#check Prod3.mb
#check Prod3.casesOn

#check Nat.casesOn
#check Sum.casesOn
#check Nat.rec
set_option pp.universes false
set_option pp.fullNames false
set_option pp.explicit false

-- Sanity check: `induction` on Nat splits into zero/succ, and in the succ branch
-- the goal is stated at `n + 1` (i.e. Nat.succ n), matching Nat.rec's succ case type
-- `motive n → motive (Nat.succ n)`.
example (n : Nat) : n + 0 = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      -- try `show n + 1 + 0 = n + 1` here — it will succeed,
      -- confirming the goal really is stated at Nat.succ n
      rfl

--Example of Nat as in above using motive.
-- But note that casesOn differs here slightly
-- as in inductive type `zero:Nat` has no arguments.
-- motive is constant (fun _ => Nat), so it ignores whatever Nat it's applied to;
-- that's why the succ branch can return `n` (the predecessor) directly, of type Nat.
def nat_to_bool (n : Nat) : Nat :=
    Nat.casesOn (motive := fun _ => Nat) n
      (6)
      (fun n => n)

-- Vector α n : a list of exactly n elements of type α
-- (Lean 4 core has this, roughly: Vector.nil : Vector α 0, Vector.cons : α → Vector α n → Vector α (n+1))

-- Commented-out example of a *dependent* motive: here the succ branch is forced to
-- produce a Vector Bool (n+1), not Vector Bool n, because the motive's index actually
-- matters (unlike the constant-motive nat_to_bool example above).
-- def makeVec (n : Nat) : Vector Bool n :=
--   Nat.casesOn (motive := fun k => Vector Bool k) n
--     (Vector.nil)                              -- zero case
--     (fun n => Vector.cons true (makeVec n))   -- succ case, recursion for illustration

--Note that when we eval the above argument passed to
-- function is the argument of succ which is the previous natural
-- to increment we want `n+2` and to get the same `n+1`
#eval nat_to_bool 3
#eval nat_to_bool 0

-- Same function as nat_to_bool but written with pattern matching instead of casesOn;
-- Lean desugars this to the same underlying recursor call.
def nat_to_bool1 (n : Nat) : Nat :=
  match n with
  | .zero => 1
  | .succ k => k

#eval nat_to_bool 3

-- A Group packaged as a structure: carrier type, identity, binary op, and the group axioms
-- (associativity, left/right identity, existence of inverses) all bundled together.
structure Group where
  element : Type u
  identity : element
  binop : element → element → element
  binop_assoc : ∀ a b c, binop (binop a b) c = binop a (binop b c)
  left_identity : ∀ a, binop identity a = a
  right_identity : ∀ a, binop a identity = a
  exists_inverse : ∀ a, ∃ b, (binop a b = identity) ∧ (binop b a = identity)

#check Group

--Defining integers group
-- Witness that (Int, +, 0) satisfies the Group axioms.
def integersGroup : Group :=
  {
    element := Int
    identity := 0
    binop a b := a + b
    binop_assoc := by omega
    left_identity := by intro a; exact Int.zero_add a
    right_identity := by intro a; exact Int.add_zero a
    exists_inverse := fun a => ⟨-a, by omega, by omega⟩
  }

end Hidden

#check Or.elim


-- Hand-rolled version of logical AND as a single-constructor Prop-valued structure.
structure MyAnd (a b : Prop) : Prop where
  intro ::
  left :  a
  right : b

-- MyAnd is commutative: swap left/right fields in each direction.
theorem MyAnd_commutes (p q : Prop) : MyAnd p q ↔ MyAnd q p :=
  Iff.intro
  (fun h : MyAnd p q => MyAnd.intro (h.right) (h.left))
  (fun h : MyAnd q p => MyAnd.intro (h.right) (h.left))


-- Hand-written addition on Nat via pattern matching, recursing on the second argument.
def add (m n : Nat) : Nat :=
  match n with
  | Nat.zero   => m
  | Nat.succ n => Nat.succ (add m n)

#eval add 3 4

open Nat

#check Nat.recOn
#check Nat.casesOn
--recOn as induction principle
-- Nat.recOn is Nat.rec with the major premise (the Nat being eliminated) moved
-- to be the first explicit argument, so it reads like an induction tactic.
-- zero case: 0 + 0 = 0 (by rfl/computation).
-- succ case: given ih : 0 + n = n, show 0 + (n+1) = n+1 by unfolding + and rewriting with ih.
theorem zero_add (n : Nat) : 0 + n = n :=
  Nat.recOn (motive := fun x => 0 + x = x)
   n
   (show 0 + 0 = 0 from rfl)
   (fun (n : Nat) (ih : 0 + n = n) =>
    show 0 + (n + 1) = n + 1 from
    calc 0 + (n + 1)
      _ = (0 + n) + 1 := rfl
      _ = n + 1       := by rw [ih])

-- Same theorem, succ case closed automatically with simp instead of a manual calc block.
theorem zero_add_simp (n : Nat) : 0 + n = n :=
  Nat.recOn (motive := fun x => 0 + x = x)
   n
   (show 0 + 0 = 0 from rfl)
   (fun (n : Nat) (ih : 0 + n = n) => by simp only [succ_eq_add_one, Nat.zero_add])


-- Addition is associative using recOn
-- Induction on k (the third argument), with motive expressing associativity for that k.
theorem add_assoc (m n k : Nat) : m + n + k = m + (n + k) :=
  Nat.recOn (motive := fun k => m + n + k = m + (n + k)) k
    (show m + n + 0 = m + (n + 0) from rfl)
    (fun k (ih : m + n + k = m + (n + k)) =>
      show m + n + (k + 1) = m + (n + (k + 1)) from
      calc m + n + (k + 1)
        _ = (m + n + k) + 1   := by rw [<- Nat.add_assoc]
        _ = (m + (n + k)) + 1 := by rw [ih]
        _ = m + ((n + k) + 1) := by rw [Nat.add_assoc]
        _ = m + (n + (k + 1)) := by rw [Nat.add_assoc])

-- Same associativity proof, succ case discharged by simp using the inductive hypothesis.
theorem add_assoc_simp (m n k : Nat) : m + n + k = m + (n + k) :=
  Nat.recOn (motive := fun k => m + n + k = m + (n + k)) k
    rfl
    (fun k ih => by simp [add_succ (m + n) k, ih]; rfl)

#check Nat.succ_add

--filling sorry as exercise

-- Addition is commutative, proved by induction on n (motive: m + n = n + m).
theorem add_comm (m n : Nat) : m + n = n + m :=
  Nat.recOn (motive := fun x => m + x = x + m) n
   (show m + 0 = 0 + m by rw [Nat.zero_add, Nat.add_zero])
   (fun (n : Nat) (ih : m + n = n + m) =>
    show m + succ n = succ n + m from
    calc m + succ n
      _ = succ (m + n) := rfl
      _ = succ (n + m) := by rw [ih]
      _ = succ n + m   := by rw [Nat.succ_add])

/-
As exercises, we encourage you to develop a notion of composition for partial functions
from α to β and β to γ, and show that it behaves as expected. We also encourage you to
show that Bool and Nat are inhabited, that the product of two inhabited types is inhabited,
and that the type of functions to an inhabited type is inhabited.
-/

#check Function.comp
-- Composition of a partial function (α → Option β) with a total function on Option β
-- is just ordinary function application/composition, verified by rfl.
theorem partial_function_composition {α β γ a} (f : α → Option β) (g : Option β →  γ) :
  (g ∘ f) a = g (f a) := by rfl

--shows Bool is inhabited
#check (inferInstance : Inhabited Bool)
#check (inferInstance : Inhabited (Prod Bool Nat))


--Other Recursive types
#eval List.cons 1 (List.cons 2 (List.cons 3 List.nil)) == [1, 2, 3]


namespace Hidden
-- Reimplementation of List as a plain two-constructor inductive type: nil and cons.
inductive List (α : Type u) where
  | nil  : List α
  | cons (h : α) (t : List α) : List α

namespace List

-- Concatenate two lists by recursing on the first one.
def append (as bs : List α) : List α :=
  match as with
  | nil       => bs
  | cons a as => cons a (append as bs)

-- Appending nil on the left is the identity, by definitional unfolding.
theorem nil_append (as : List α) : append nil as = as := by rfl

-- append unfolds one cons at a time — this is essentially the defining equation of append.
theorem cons_append (a : α) (as bs : List α) :
    append (cons a as) bs = cons a (append as bs) :=
  rfl

set_option pp.universes false
set_option pp.fullNames false
set_option pp.explicit false

-- Appending nil on the right is the identity too, proved by induction on as.
theorem append_nil (as : List α) :
    append as nil = as := by
    induction as with
    | nil => rfl
    | cons x xs ih => simp [cons_append, ih]

-- append is associative, proved by induction on the first list.
theorem append_assoc (as bs cs : List α) :
    append (append as bs) cs = append as (append bs cs) := by
    induction as with
    | nil => simp [nil_append]
    | cons x xs ih => simp [cons_append, ih]

--length definition
-- Structural recursion computing the length of a list.
def mylength {α : Type u} (as : List α) : Nat :=
  match as with
  | nil => 0
  | cons x ax => 1 + (mylength ax)


end List
end Hidden
--length definition

-- Same length function, but for Lean core's built-in List rather than the Hidden.List above.
def mylength {α : Type u} (as : List α) : Nat :=
  match as with
  | List.nil => 0
  | List.cons x ax => 1 + (mylength ax)

#eval mylength ([] : List Nat)
#eval mylength ["1", "a"]


--countable branching tree
-- CBTree: an infinitely-branching tree — `sup` takes a whole function Nat → CBTree,
-- i.e. countably many children indexed by Nat, plus a `leaf` base case.
inductive CBTree where
  | leaf : CBTree
  | sup : (Nat → CBTree) → CBTree

namespace CBTree

-- Successor: a node whose every child (indexed by any Nat) is the same tree t.
def succ (t : CBTree) : CBTree :=
  sup (fun _ => t)

-- Build the tree representing the Nat n by repeated succ starting from leaf.
def toCBTree : Nat → CBTree
  | 0 => leaf
  | n+1 => succ (toCBTree n)

-- omega: the tree whose n-th child is toCBTree n, i.e. one branch for every finite stage —
-- a standard way to represent "the limit ordinal ω" as a CBTree.
def omega : CBTree :=
  sup toCBTree

end CBTree

--Bin Tree definition
-- Polymorphic binary tree: leaves carry a value of type α, nodes have two subtrees.
inductive BinaryTree (α : Type u) where
  | leaf : α → BinaryTree α
  | node : BinaryTree α  → BinaryTree α → BinaryTree α

#check BinaryTree Nat

def t : BinaryTree Nat := .node (.leaf 1) (.leaf 2)

-- NOTE: `u` here is NOT a universe — it's an unbound lowercase identifier, so Lean's
-- autoBound feature silently inserts an implicit type variable for it, i.e. this
-- elaborates as `{u : Type u_1} (as : List u)`, an ordinary polymorphic list parameter.
-- (Contrast with writing `List Type` explicitly, which really would mean "a list of types".)
inductive BinaryTreeList (as : List u) where
  | leaf : α → BinaryTreeList as
  | node : BinaryTreeList as  → BinaryTreeList as → BinaryTreeList as

#check BinaryTreeList [1, 2, 3]


-- Tactics for Inductive Types

-- `cases n` on a Nat splits the goal into a zero case and a succ case, mirroring
-- Nat.casesOn: no inductive hypothesis is introduced here (that's `induction`, not `cases`).
example (p : Nat → Prop)
    (hz : p 0) (hs : ∀ n, p (Nat.succ n)) :
    ∀ n, p n := by
  intro n
  cases n
  . exact hz
  . apply hs

-- Notice that cases can be used to produce data as well as prove propositions.
def f (n : Nat) : Nat := by
  cases n; exact 3; exact 7;

example : f 0 = 3 := rfl
example : f 5 = 7 := rfl

-- Weak induction on Nat: zero case is rfl; succ case rewrites using Nat.add_succ and ih.
theorem zero_add1 (n : Nat) : 0 + n = n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Nat.add_succ, ih]

-- Strong/well-founded induction principle for Nat (for reference/comparison with
-- the weak induction used via Nat.rec/Nat.recOn throughout this file).

set_option pp.all false
#check Nat.mod.inductionOn

/-
`cases`: It breaks down the hypothesis based on all constructors
`inductionOn` : strong induction
`injection`: As the name suggests if two values are same by constructor then their
arguments are same
The injection tactic also
detects contradictions that arise when different constructors are set equal to one another

-/

example (m n k : Nat) (h : succ (succ m) = succ (succ n))
        : n + k = m + k := by
  injection h with h'
  injection h' with h''
  rw [h'']

/-
Exercises
-/

namespace exercises

/-
(1)
Try defining other operations on the natural numbers, such as multiplication, the predecessor function (with pred 0 = 0), truncated subtraction (with n - m = 0 when m is greater than or equal to n), and exponentiation. Then try proving some of their basic properties, building on the theorems we have already proved.

Since many of these are already defined in Lean's core library, you should work within a namespace named Hidden, or something like that, in order to avoid name clashes.
-/

def add (m n : Nat) : Nat :=
  match n with
  | Nat.zero   => m
  | Nat.succ n => Nat.succ (add m n)


def multiply (m n : Nat) : Nat :=
  match n with
  | 0 => 0
  | .succ n => add m (multiply m n)

def pred (n : Nat) : Nat :=
  match n with
  | 0 => 0
  | .succ x => x

def subtract (n m : Nat) : Nat :=
  match m with
  | 0        => n
  | .succ x  => pred (subtract n x)

#eval multiply 1 1
#eval multiply 1 0
#eval multiply 2 4

#eval pred 5
#eval subtract 4 0
#eval subtract 4 1

end exercises
