
set_option linter.unusedVariables false
open Nat

def sub1 : Nat → Nat
  | zero   => zero
  | succ x => x

def isZero : Nat → Bool
  | zero   => true
  | succ x => false

#info_trees in --tree info
#eval sub1 3
#eval isZero 3

#check Nat.below

inductive color where
| red : color
| blue : color
| green : color

#check color.rec

def bar : Option Nat → Nat
  | some n => n + 1
  | none   => 0

#eval bar none

namespace Hidden
def not : Bool → Bool
  | true  => false
  | false => true

theorem not_not : ∀ (b : Bool), not (not b) = b
  | true  => show not (not true) = true from rfl
  | false => show not (not false) = false from rfl
end Hidden

def sub2 : Nat → Nat
  | 0     => 0
  | 1     => 0
  | x + 2 => x

#info_trees in
#eval sub2 2

#print sub2

example : sub2 (x + 2) = x := rfl

def foo_1 : Nat → Nat → Nat
  | 0, n => 0
  | m, 0 => 1
  | m, n => 2

def foo_2 : Nat → Nat → Nat
  | 0, _ => 0
  | _, 0 => 1
  | _, _ => 2

example : foo_1 0       0       = foo_2 0       0 := rfl
example : foo_1 0       (n + 1) = foo_2 0 (n+1) := rfl
example : foo_1 (m + 1) 0       = foo_2 (m+1) 0 := rfl
example : foo_1 (m + 1) (n + 1) = foo_2 (m+1) (n+1) := rfl

def fib : Nat → Nat
  | 0   => 1
  | 1   => 1
  | n+2 => fib (n+1) + fib n

#eval fib 10

--#reduce fib <n> is efficient because it uses the
-- definition sent to the kernel that is based on the brecOn construction.
#reduce fib 100

def fibFast (n : Nat) : Nat :=
  (loop n).2
where
  loop : Nat → Nat × Nat
    | 0   => (0, 1)
    | n+1 => let p := loop n; (p.2, p.1 + p.2)

#eval fibFast 100

def factAcc (n : Nat) : Nat :=
  let rec loop : Nat → Nat → Nat
    | 0,   acc => acc
    | m+1, acc => loop m (acc * (m+1))
  loop n 1

#eval factAcc 4

def factCapped (n limit : Nat) : Nat × Bool :=
  loop n limit
  where
    loop : Nat → Nat → Nat × Bool
      | 0,   acc => (acc, true)
      | m+1, acc =>
        let acc' := acc * (m+1)
        if acc' > limit then (acc', false) else loop m acc'

#eval factCapped 5 100


def replicate (n : Nat) (a : α) : List α :=
  let rec loop : Nat → List α → List α
    | 0,   as => as
    | n+1, as => loop n (a::as)
  loop n []

#eval replicate 5 "Sham"

#check @replicate.loop
