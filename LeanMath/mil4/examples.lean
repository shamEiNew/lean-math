import Mathlib

--EVEN umber
namespace evenexample

def Even (n : Nat) : Prop  := ∃ (k : Nat),  (n = k + k)


example : ∀ m n : Nat, Even n → Even (m * n) := fun m n ⟨k, (hk : n = k + k)⟩ ↦
  have hmn : m * n = m * k + m * k := by rw [hk, Nat.mul_add]
  show ∃ l, m * n = l + l from ⟨_, hmn⟩

example : ∀ m n : Nat, Even n → Even (m * n) := by
  rintro m n ⟨k, hk⟩
  refine ⟨m * k, ?_⟩
  rw [hk]
  rw [Nat.mul_add]


example (hyp : c = d * a + b) (hyp' : b = a * d) : c = 2 * a * d := by
  rw [hyp, hyp']
  rw [Nat.mul_comm a d]
  ring

end evenexample


example (a b c : ℝ) : a * b * c = b * (a * c) := by
  rw [mul_comm a b]
  rw [mul_assoc b a c]

example (a b c : ℝ) : c * b * a = b * (a * c) := by
  rw [mul_comm c b]
  rw [mul_assoc b c a]
  rw [mul_comm c a]

example (a b c : ℝ) : a * (b * c) = b * (a * c) := by
  rw [<- mul_assoc a b c]
  rw [mul_comm a b]
  rw [mul_assoc b a c]


open Algebra

#check ZMod 5
#check Field

theorem zmodn_field_iff_n_is_prime {n : Nat} (h : n ≠ 0) (h2 : n ≥ 2) :
  IsField (ZMod n) ↔ Nat.Prime n := by
  apply Iff.intro

  · intro h1
    by_cases hp : Nat.Prime n
    · exact hp
    · have hf : ¬ IsField (ZMod n) := by
        obtain ⟨m, hm_dvd, hm_ne1, hm_neN⟩ := Nat.exists_dvd_of_not_prime h2 hp
        obtain ⟨q, hq⟩ := hm_dvd
        have hmq : (m : ZMod n) * (q : ZMod n) = 0 := by
          rw [← Nat.cast_mul, ← hq, ZMod.natCast_self]
        -- derive m, q bounds
        intro h1
        have hm0 : m ≠ 0 := by intro rfl; simp at hq; exact h hq
        have hq0 : q ≠ 0 := by intro rfl; simp at hq; exact h hq
        have hq_ne1 : q ≠ 1 := by rintro rfl; simp at hq; exact hm_neN hq.symm
        have hm2 : 2 ≤ m := by omega
        have hq2 : 2 ≤ q := by omega
        have hmltn : m < n := by
          rw [hq]; exact (Nat.lt_mul_iff_one_lt_right (by omega)).mpr (by omega)
        have hqltn : q < n := by
          rw [hq, Nat.mul_comm]; exact (Nat.lt_mul_iff_one_lt_right (by omega)).mpr (by omega)
        haveI : NeZero n := ⟨h⟩
        have hmcast : (m : ZMod n) ≠ 0 := by
          rw [Ne, ZMod.natCast_eq_zero_iff]
          intro hdvd
          have := Nat.le_of_dvd (by omega) hdvd
          omega
        have hqcast : (q : ZMod n) ≠ 0 := by
          rw [Ne, ZMod.natCast_eq_zero_iff]
          intro hdvd
          have := Nat.le_of_dvd (by omega) hdvd
          omega
        letI : Field (ZMod n) := h1.toField
        rcases mul_eq_zero.mp hmq with h0 | h0
        · exact hmcast h0
        · exact hqcast h0
      exact False.elim (hf h1)
  · intro h1
    have he_pair : ∃ (x : ZMod n), ∃ (y : ZMod n), x ≠ y := by
      haveI : Fact (1 < n) := ⟨by omega⟩
      exact ⟨0, 1, zero_ne_one⟩
    have hmc : ∀ x y : ZMod n, x * y = y * x := fun x y => mul_comm x y
    have inverse_exists {a : ZMod n} : a ≠ 0 → ∃ (b : ZMod n), a * b = 1 := by
      intro ha
      have ha' : a.val ≠ 0 := by
        intro h0
        apply ha
        rw [ZMod.val_cast_of_lt (a := (0:ℕ))] -- not quite; see note below
        sorry
      have coprime : Nat.gcd n a.val = 1 := (Nat.coprime_primes ...).mpr -- see below
      sorry


--IsBezout.gcd_eq_sum
