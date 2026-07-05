/--
error: Type mismatch
  "Not a number"
has type
  String
but is expected to have type
  Nat
-/
#guard_msgs in
def x : Nat := "Not a number"

--gaurd_msgs just checks the error and if it matches the expected error it just "gaurds" it
--doesn't pop up in lean infoview.

#check And.intro


--SECTION
section
variable (x y : Nat)

def double := x + x

#check double y
#check double (2 * x)

#eval double 2

--writes a simp tactic for this theorem/definitions
attribute [local simp] Nat.add_assoc Nat.add_comm Nat.add_left_comm

theorem t1 : double (x + y) = double x + double y := by
  simp [double]

#check t1 y
#check t1 (2 * x)
theorem t2 : double (x * y) = double x * y := by
  simp [double, Nat.add_mul]

export Nat (succ add sub)

end
