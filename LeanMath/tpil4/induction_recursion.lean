
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
