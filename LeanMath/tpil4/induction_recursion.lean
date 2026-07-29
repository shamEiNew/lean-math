
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
