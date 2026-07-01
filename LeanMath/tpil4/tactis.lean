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

--use of unhygienic
example : ∀ a b c : Nat , a = b → a = c → c = b := by unhygienic
  intros
  apply Eq.trans
  apply Eq.symm
  exact a_2
  exact a_1

example : ∀ a b c : Nat , a = b → a = c → c = b :=
  (fun a b c => fun h1 : a = b => fun h2 : a = c => Eq.trans (Eq.symm h2) h1)

example (p q : α → Prop) : (∃ x, p x ∧ q x) → ∃ x, q x ∧ p x := by
  intro ⟨w, hpw, hqw⟩
  exact ⟨w, hqw, hpw⟩

example (p q : α → Prop) : (∃ x, p x ∨ q x) → ∃ x, q x ∨ p x := by
  intro
  | ⟨w, Or.inl h⟩ => exact ⟨w, Or.inr h⟩
  | ⟨w, Or.inr h⟩ => exact ⟨w, Or.inl h⟩

theorem test1 (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro
  case left => exact hp
  case right =>
    apply And.intro
    case left => exact hq
    case right => exact hp


example : ∀ a b c d : Nat, a = b → a = d → a = c → c = b := by
  intros
  rename_i h1 _ h2
  apply Eq.trans
  apply Eq.symm
  exact h2
  exact h1

example (x : Nat) : x = x := by
  revert x
  intro y
  rfl

example (x y : Nat) (h : x = y) : y = x := by
  revert x
  intros
  apply Eq.symm
  assumption
