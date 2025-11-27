example (α : Type) (p q : α → Prop) :
    (∀ x : α, p x ∧ q x) → ∀ y : α, p y :=
  fun h : ∀ x : α, p x ∧ q x =>
  fun y : α =>
  show p y from (h y).left


variable (α : Type) (r : α → α → Prop)
variable (trans_r : ∀ x y z, r x y → r y z → r x z)

variable (a b c : α)
variable (hab : r a b) (hbc : r b c)

#check trans_r
#check trans_r a b c
#check trans_r a b c hab
#check trans_r a b c hab hbc

#check Eq.refl

variable (α β : Type)


/- Two expressions are considered definitionally
equal if they reduce (by computation)
to the same normal form.-/
example (f: α → β) (a:α) : (fun x => f x) a = f a := Eq.refl _

example : 2 + 3 = 5 := rfl


--Subsitution
example (α : Type) (a b : α) (p:α → Prop)
        (h1 : a = b) (h2 : p a) : p b := Eq.subst h1 h2


-- congrArg, congrFun, and congr

variable (α : Type)
variable (a b : α)
variable (f g : α → Nat)
variable (h₁ : a = b)
variable (h₂ : f = g)

-- so the order is [function argument]
-- congrArg replaces arguments over a fixed function
-- congreFun replaces functions over a fixed argument
-- congr does both

example : f a = f b := congrArg f h₁
example : f a = g a := congrFun h₂ a
example : f a = g b := congr h₂ h₁


-- identities

variable (a b c : Nat)

example : a + 0 = a := Nat.add_zero a
example : 0 + a = a := Nat.zero_add a
example : a * 1 = a := Nat.mul_one a
example : 1*a = a := Nat.one_mul a
example : a + b = b + a := Nat.add_comm a b
example : a + b + c = a + (b + c) := Nat.add_assoc a b c
example : a * b = b * a := Nat.mul_comm a b --commutative *
example : a * b * c = a * (b * c) := Nat.mul_assoc a b c --associative *
example : a * (b + c) = a * b + a * c := Nat.mul_add a b c --left distributive
example : (a + b) * c = a * c + b * c := Nat.add_mul a b c --right distributive


--example to implement above

example (x y : Nat) :
    (x + y) * (x + y) =
    x * x + y * x + x * y + y * y :=

    have h1: (x + y)*(x+y) = (x + y) * x + (x + y) * y :=
    Nat.mul_add (x+y) x y
    have h2 : (x + y) * (x + y) = x * x + y * x + (x * y + y * y) :=
    Nat.add_mul x y x ▸ Nat.add_mul x y y ▸ h1
    h2.trans (Nat.add_assoc (x * x + y * x) (x * y) (y * y)).symm
