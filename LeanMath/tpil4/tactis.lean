theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro
  exact hp
  apply And.intro
  exact hq
  exact hp


theorem test_short (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
 apply And.intro hp
 exact And.intro hq hp


example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
apply Iff.intro
. intro h
  apply Or.elim (And.right h)
  . intro hq
    apply Or.inl
    apply And.intro
    . exact h.1
    . exact hq
  . intro hr
    apply Or.inr
    apply And.intro
    . exact h.1
    . exact hr
. intro h
  apply Or.elim h
  . intro hpq
    apply And.intro
    . exact hpq.1
    . apply  Or.inl
      exact  hpq.2
  . intro hpr
    apply And.intro
    . exact hpr.1
    . apply Or.inr
      exact hpr.2

-- example
example : ∀ a b c : Nat , a = b → a = c → c = b := by
  intros
  apply Eq.trans
  apply Eq.symm
  assumption
  assumption
