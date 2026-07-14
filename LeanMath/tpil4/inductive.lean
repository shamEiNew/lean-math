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

inductive Weekday where
  | monday : Weekday
  | tuesday : Weekday
  | wednesday : Weekday
  | thursday : Weekday
  | friday : Weekday
  | saturday : Weekday
  | sunday : Weekday

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

#print Nat.rec --predicat acting on natural numbers motive is like Predicar
#print numberOfDay

def factorial : Nat → Nat
  | 0 => 1
  | n+1 => (n+1) * factorial n

  def fact : Nat → Nat :=
    Nat.rec 1 (fun n ih => (n+1) * ih)

#eval fact 1


namespace Weekday

def next (day : Weekday): Weekday :=
  match day with
  | monday => tuesday
  | tuesday => wednesday
  | wednesday => thursday
  | thursday => friday
  | friday => saturday
  | saturday => sunday
  | sunday => monday

def previous (day : Weekday): Weekday :=
  match day with
  | monday => sunday
  | tuesday => monday
  | wednesday => tuesday
  | thursday => wednesday
  | friday => thursday
  | saturday => friday
  | sunday => saturday

theorem nextprevious (day : Weekday) : next (previous day) = day := by
  cases day <;> rfl

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
inductive Prod (α : Type u) (β : Type v)
  | mk : α → β → Prod α β

-- Multiple constructors ``inl` and `inr`: Disjunctive
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


def prod_example (p : Prod Bool Nat) : Nat :=
  Prod.casesOn (motive := fun _ => Nat) p
    (fun b n => cond b (2 * n) (2 * n + 1))

#eval prod_example (Prod.mk true 3)

#check (true, 3)
#check Prod.mk true 3

#check Sum.casesOn

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
inductive Prod1 (α : Type u) (β : Type v) where
  | mk (fst : α) (snd : β) : Prod1 α β

#check Prod1.mk
/-
structures are special case of inductive types as it
allows to construct named arguments and infers the constructor
-/

structure Prod2 (α : Type u) (β : Type v) where
  mk ::
  fst : α
  snd : β
/-
If we don't name the constructor lean default name is mk
-/

structure Prod3 (α : Type u) (β : Type v) where
  mb ::
  fst : α
  snd : β

#check Prod3.mb
#check Prod3.casesOn

#check Nat.casesOn
#check Sum.casesOn

--Example of Nat as in above using motive.
-- But note that casesOn differs here slightly
-- as in inductive type `zero:Nat` has no arguments.
def nat_to_bool (n : Nat) : Nat :=
    Nat.casesOn (motive := fun _ => Nat) n
      (6)
      (fun n => n)

--Note that when we eval the above argument passed to
-- function is the argument of succ which is the previous natural
-- to increment we want `n+2` and to get the same `n+1`
#eval nat_to_bool 3
#eval nat_to_bool 0

end Hidden
