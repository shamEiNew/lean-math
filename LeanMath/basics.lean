/-1 Propositions & Proofs in lean -/

variable (p q r : Prop)

#check And p q

#check Or

structure Proof (p : Prop) : Type where
  proof : p


def Implies (p q : Prop) := p → q

#check Proof

axiom and_commut (p q : Prop) : Proof (Implies (And p q) (And q p))

#check and_commut

--------------
set_option linter.unusedVariables false
---
variable {p : Prop}
variable {q : Prop}

theorem t1 : p → q → p := fun hp : p => fun hq : q => show p from hp

#print t1

-- use of theorems as functions

variable (p q r s : Prop)

theorem t2 (h₁ : q → r) (h₂ : p → q) : p → r :=
  fun h₃ : p =>
  show r from h₁ (h₂ h₃)



variable (p q : Prop)

example (h : p ∧ q) : p := And.left h
example (h : p ∧ q) : q := And.right h



-- use of And.Intro to construct conjunctions.
example (h : p ∧ q) : q ∧ p :=
  And.intro (And.right h) (And.left h)

variable (p q r : Prop)

-- Syntactic gadgets in lean
variable (xs : List Nat)

#check List.length xs

#check xs.length
/-instead of calling the length function using List can be called with
with the object of that class -/



--- use of Or.elim to reason by cases on disjunctions.
-- Or.intro_left q hp creates a proof of p v q from a proof of hp : p. Similary for Or.intro_right.
-- Note the difference between And.intro and Or.intro_left / Or.intro_right
-- And introduces a conjunction, while Or.intro_left / Or.intro_right introduces a disjunction.

variable (p q : Prop)
example (hp : p) : p ∨ q := Or.intro_left q hp
example (hq : q) : p ∨ q := Or.intro_right p hq

example (h : p ∨ q) : q ∨ p :=
  Or.elim h
    (fun hp : p =>
      show q ∨ p from Or.intro_right q hp)
    (fun hq : q =>
      show q ∨ p from Or.intro_left p hq)

--
