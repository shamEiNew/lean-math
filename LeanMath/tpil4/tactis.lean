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

--rename the last few variables
example : ∀ a b c d : Nat, a = b → a = d → a = c → c = b := by
  intros
  rename_i h1 _ h2
  apply Eq.trans
  apply Eq.symm
  exact h2
  exact h1

--revert is intro opposite includes the hypothesis in goal
example (x : Nat) : x = x := by
  revert x
  intro y
  rfl

example (x y : Nat) (h : x = y) : y = x := by
  revert x
  intros
  apply Eq.symm
  assumption

--generalizes the hypothesis and replaces the main goal
example : 3 = 3 := by
  generalize 3 = x
  revert x
  intro y
  rfl


open Nat
example (P : Nat → Prop)
    (h₀ : P 0) (h₁ : ∀ n, P (succ n))
    (m : Nat) : P m := by
  cases m with
  | zero    => exact h₀
  | succ m' => exact h₁ m'

--Rewriting all proofs using tactics
open Classical

variable (p q r : Prop)

example : (p → q ∨ r) → ((p → q) ∨ (p → r)) := by
  intro hp
  by_cases hq : p → q
  · exact Or.inl hq
  · right
    intro hp'
    have hqr : q ∨ r := hp hp'
    cases hqr with
    | inl hq' =>
        exfalso
        apply hq
        intro _
        exact hq'
    | inr hr =>
        exact hr

variable (p q r : Prop)

example (p q : Prop) : ¬(p → q) → p ∧ ¬q := by
  intro h
  by_cases hpq : p ∧ ¬q
  · exact hpq
  · have pq : p → q := by
      intro hp
      by_cases hq :q
      · exact hq
      · exact False.elim (hpq (And.intro hp hq))
    exact False.elim (h pq)


example : (p → q) → (¬p ∨ q) := by
  intro h
  by_cases hp:p
  · exact Or.inr (h hp)
  · exact Or.inl hp


example : (¬q → ¬p) → (p → q) := sorry

example : p ∨ ¬p := by
  by_cases hp:p
  · exact Or.inl hp
  · exact Or.inr hp

example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := by
  apply Iff.intro
  · intro h ;apply And.intro;intro hp;exact h (Or.inl hp);intro hq;exact h (Or.inr hq)
  · intro h;intro hpq;apply Or.elim hpq;intro hp;exact False.elim (h.1 hp);intro hq;exact False.elim (h.2 hq)

example : (((p → q) → p) → p) := sorry
