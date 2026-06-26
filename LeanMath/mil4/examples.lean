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
