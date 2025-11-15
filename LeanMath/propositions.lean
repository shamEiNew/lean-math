variable {p q r : Prop}

-- IMPLICATION
theorem ex1 : p → q → r →  p :=
fun hp : p =>
fun hq : q =>
fun hr : r =>
show p from hp

-- CONJUNCTIONS
theorem ex2 : (p ∧ q) → p :=
fun hnd : p ∧ q =>
show p from And.left hnd

-- SWAP CONJUNCTIONS
theorem ex3 :(p ∧ q) ↔ (q ∧ p) :=
Iff.intro
  (fun h₁ : p ∧ q => And.intro (And.right h₁) (And.left h₁))
  (fun h₂ : q ∧ p => And.intro (And.right h₂) (And.left h₂))

-- DISJUNCTIONS
theorem ex4 (h : p ∨ q) : q ∨ p :=
  Or.elim h
  (fun hp :p=>
      show q ∨ p from Or.intro_right q hp)
  (fun hq :q=>
      show q ∨ p from Or.intro_left p hq)

--NEGATION
theorem ex5 (hpq : p -> q) (hnq : ¬q): ¬p := by sorry
