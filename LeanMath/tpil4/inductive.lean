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
