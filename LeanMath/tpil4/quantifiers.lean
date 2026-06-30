-- Universal Quantifier
/-
Intro rule: given an aribbitrary element for which p x holds
we say that it holds for all x

Elimination rule: given a proof ∀ x : α  p x, and any term t:α
we have a proof of p t
-/

#check ∀ n : Nat, n + 0 = n


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

example : 3 + 3 = 6 := rfl


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



--use of calc , simp rw
variable (a b c d e : Nat)

theorem T
    (h1 : a = b)
    (h2 : b = c + 1)
    (h3 : c = d)
    (h4 : e = 1 + d) :
    a = e :=
  calc
    a = b      := h1
    _ = c + 1  := h2
    _ = d + 1  := congrArg Nat.succ h3
    _ = 1 + d  := Nat.add_comm d 1
    _ = e      := h4.symm



theorem T1
    (h1 : a = b)
    (h2 : b = c + 1)
    (h3 : c = d)
    (h4 : e = 1 + d) :
    a = e := by rw [h1, h2, h3, Nat.add_comm, h4]


variable (x y : Nat)

example : (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
  calc
    (x + y) * (x + y) = (x + y) * x + (x + y) * y  :=
      by rw [Nat.mul_add]
    _ = x * x + y * x + (x + y) * y                :=
      by rw [Nat.add_mul]
    _ = x * x + y * x + (x * y + y * y)            :=
      by rw [Nat.add_mul]
    _ = x * x + y * x + x * y + y * y              :=
      by rw [← Nat.add_assoc ]


--Existence

example : ∃ n : Nat, n = 1 :=
  have h : 1 = 1 := rfl
  Exists.intro 1 h

#check Exists.intro



example : ∃ x : Nat, x + 1 = 4 :=
  have h : 3 + 1 = 4 := by
    calc
      3 + 1 = 2 + 1 + 1 :=  by rw [<- Nat.succ_eq_add_one 2]
       _     = 2 + (1 + 1) := by rw [Nat.add_assoc]
       _     = 2 + 2 := by rw [Nat.add_comm 1 1]
        _     = 4 := rfl
  Exists.intro 3 h


/-
In the above we prove there exists x such that
x + 1 = 4
we use `calc` keyword for calculation proof
In the first step we set our hypothesis h
and then move on to prove further points.
first rewrite is `[<- Nat.succ_eq_add_one 2]` which
substitutes `Nat.succ 2 = 2 + 1` the `rw` tries to match
`Nat.succ 2` so we use it.
Next we use `Nat.add_assoc` (`a + b + c = a + (b + c)`)
Next `Nat.add_comm` and `rfl` finally.
Note that `rfl` is powerful. If two expressions compute to same,
however complicated it treats them the same.
Also `rfl` is at the core of leans kernel and not in meta layer.
Finally, `Exists.intro` gives a proof of `Exists p` where `p:α → Prop`
is predicate given witness `w:α` sucht that `p w` holds.

A very simple way to do this below:


-/
example : ∃ x : Nat, x + 1 = 4 := Exists.intro 3 rfl

#check Nat.succ_eq_add_one 2


def IsEven (a : Nat) := ∃ b , a = 2 * b


#check @Exists.elim


variable (α : Type) (p q : α → Prop)

example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  Exists.elim h
    (fun w =>
     fun hw : p w ∧ q w =>
     show ∃ x, q x ∧ p x from ⟨w, hw.right, hw.left⟩)


theorem even_plus_even (h1 : IsEven a) (h2 : IsEven b) : IsEven (a + b) :=
  Exists.elim h1 (fun w1 (hw1 : a = 2 * w1) =>
  Exists.elim h2 (fun w2 (hw2 : b = 2 * w2) =>
  Exists.intro (w1 + w2)
    (calc a + b
    _ = 2 * w1 + 2 * w2 := by rw [hw1, hw2]
    _ = 2 * (w1 + w2) := by rw [Nat.mul_add]

    )))

/-The above shows the addition of two even numbers is even.
First, we take `h1` our first hypothesis and we use `Exists.elim` with `h1` with
arbitrary witness `w1`. And we further make use similarly `h2` .
Finally, we use `Exists.intro` to construct our goal from the witness
`w1 + w2` and `IsEven` (implicit).
-/


def IsOdd (a: Nat) := ∃ k , a = 2 * k + 1


theorem odd_plus_odd (h1 : IsOdd a) (h2 : IsOdd b) : IsEven (a + b) :=
  Exists.elim h1 (fun w1 (hw1 : a = 2 * w1 + 1) =>
  Exists.elim h2 (fun w2 (hw2 : b = 2 * w2 + 1) =>
  Exists.intro (w1 + 1 + w2)
    (calc a + b
    _ = 2 * w1 + 1 + 1 + 2 * w2:= by rw [hw1, hw2, Nat.add_comm (2*w2) 1, ← Nat.add_assoc]
    _ = 2 * w1 + 2 + 2 * w2 := by simp
    _ = 2 * (w1 + 1 ) + 2*w2 := by rw [Nat.mul_add]
    _ = 2 * ((w1 + 1) + w2) := by rw [← Nat.mul_add]

    )))


#check Nat.succ

----- Proving Identities -----
open Classical

variable (α : Type) ( p q : α → Prop)
variable (r : Prop)


example : (∃ x : α, r) → r :=
  fun h : (∃ x : α, r) =>
    Exists.elim h (
      fun w (hr:r )=> hr

    )

example (a : α) : r → (∃ x : α, r) :=
fun hr : r => Exists.intro a hr


example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r :=
Iff.intro
  (fun h : (∃ x, p x ∧ r) =>
  Exists.elim h (fun w => fun hpr : p w ∧ r =>
  And.intro (Exists.intro w hpr.left) hpr.right))
  (fun h : (∃ x, p x) ∧ r =>
  Exists.elim h.left (fun w => fun hp : p w =>
  Exists.intro w (And.intro hp h.right)))

example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) :=
Iff.intro
  (fun h : (∃ x, p x ∨ q x) =>
    Exists.elim h ( fun w => fun hpw : p w ∨ q w =>
    Or.elim hpw
      (fun hp : p w => Or.inl (Exists.intro w  hp))
      (fun hq : q w => Or.inr (Exists.intro w  hq))
  ))
  (
    fun h : (∃ x, p x) ∨ (∃ x, q x) =>
      Or.elim h
        (fun h1 : (∃ x, p x) =>
        Exists.elim h1 (fun w => fun hw : p w => Exists.intro w (Or.inl hw)))
        (fun h2 : (∃ x, q x) =>
        Exists.elim h2 (fun w => fun hw : q w => Exists.intro w (Or.inr hw)))
  )


example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) :=
  Iff.intro
  (fun h : (∀ x, p x) =>
   fun h1 : (∃ x, ¬ p x) =>
    Exists.elim h1 (fun w => fun h2 : ¬ p w => show False from h2 (h w))
    )

   (fun h : ¬ (∃ x, ¬ p x) => fun x =>
     byContradiction (fun hpx =>  h ⟨x, hpx⟩))


/-In the above only one direction is constructive
The firs side is constructive as you can prove it directly with using DNE
i.e double negation.

On the other side we require double negation. As `¬¬p ≃ p`-/

#check byContradiction

example (t : Prop): ¬¬t → t :=
fun h : ¬¬t => byContradiction (fun ht : ¬t => h ht)

example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) :=
Iff.intro
  (fun h : (∃ x, p x) => fun h1 :  (∀ x, ¬ p x) =>
  Exists.elim h (fun w => fun hpw : p w => show False from (h1 w) hpw))

  (fun hn : ¬ (∀ x, ¬ p x) => byContradiction (fun h : ¬ (∃ x, p x) =>
   hn (fun x (hx:p x )=> h ⟨x, hx⟩)))

example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) :=
Iff.intro
  (fun h : ¬ (∃ x, p x) => fun x (hx: p x) => h ⟨x, hx ⟩)
  (fun h :(∀ x, ¬ p x) => fun hex : ∃ x, p x =>
  Exists.elim hex (fun w => fun hw : p w => show False from (h w) hw))


example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) :=
Iff.intro
(fun h : ¬ (∀ x, p x) =>
  byContradiction (fun hn : ¬ (∃ x, ¬ p x) =>
  h (fun x => byContradiction (fun hpx => hn ⟨x, hpx ⟩))
))
(fun h : (∃ x, ¬ p x) => fun hn :  (∀ x, p x) =>
Exists.elim h (fun x => fun hpx : ¬ p x => show False from hpx (hn x))

)


example : (∀ x, p x → r) ↔ (∃ x, p x) → r :=
Iff.intro
(fun h: (∀ x, p x → r) => fun hp : (∃ x, p x) =>
Exists.elim hp (fun w => fun hw : p w => (h w) hw))

(fun h : (∃ x, p x) → r =>
fun w => fun hp : p w => h ⟨w, hp ⟩)


-- example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r :=
-- Iff.intro
-- (fun h : (∃ x, p x → r) => fun hp : (∀ x, p x) =>
-- Exists.elim h (fun w => fun hpw : p w → r => hpw (hp w))
-- )
-- (fun h : (∀ x, p x) → r =>
-- Exists.intro (a,  fun hp : p a => (h hp)))

variable (men : Type) (barber : men)
variable (shaves : men → men → Prop)

#check Iff.elim


-- Russells Paradox
example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : False :=
have hf := h barber
have n_shaves : ¬ shaves barber barber :=
    λ s => (hf.mp s) s
n_shaves (hf.mpr n_shaves)


--EXERCISES

variable (α : Type) (p q : α → Prop)

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) :=
  Iff.intro
    (
      fun h : ∀ x, p x ∧ q x =>
      And.intro (fun y => (h y).left) (fun y => (h y).right)
    )
    (
      fun h : (∀ x, p x) ∧ (∀ x, q x) =>
        fun y => And.intro (h.left y) (h.right y)
    )



example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) :=
  fun h : (∀ x, p x → q x) =>
    fun hp : ∀ x, p x => fun y => h y (hp y)



example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x :=
  fun h =>
    Or.elim h
      ( fun hp : (∀ x, p x) => fun y => Or.inl (hp y)
      )
      (
        fun hq : (∀ x, q x) => fun y => Or.inr (hq y)
      )


variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : α → ((∀ x : α, r) ↔ r) :=
  fun y : α =>
  Iff.intro
  (fun h  => h y)
  (fun hr => fun _ => hr)


-- Requires classical and can't be proven in intuition logic
example : (∀ x, p x ∨ r) → ((∀ x, p x) ∨ r) :=
  fun h =>
    byContradiction (
      fun hn =>
        hn (
          Or.inl (
            fun x =>
              Or.elim (h x)
                (fun hp => hp)
                (fun hr =>
                  False.elim (
                    hn (Or.inr hr)
                  )
                )
          )
        )
    )


example :  ((∀ x, p x) ∨ r) → (∀ x, p x ∨ r) :=
  fun h : ((∀ x, p x) ∨ r) => fun y =>
    Or.elim h
      (fun hp : ∀ x, p x => Or.inl (hp y))
      (fun hr : r => Or.inr hr)


example : (∀ x, r → p x) →  (r → ∀ x, p x) :=
  fun h : (∀ x, r → p x) =>
    fun hr : r =>
      fun y =>
        (h y) hr

example :(r → ∀ x, p x) → (∀ x, r → p x) :=
  fun h : (r → ∀ x, p x) =>
    fun y =>
      fun hr : r => (h hr) y


def even (n : Nat) : Prop := ∃ b, n = 2*b

def prime (n: Nat) : Prop := ∀ x, n % x = 0 → (x = 1 ∨ x = n)

def infinitely_many_primes : Prop := ∀ n : Nat, ∃ p : Nat, p > n ∧ prime p

def Fermat_prime (n : Nat) : Prop := prime n ∧ (∃ k : Nat, n = 2^(2^k) + 1)

def infinitely_many_Fermat_primes : Prop := ∀ n : Nat, ∃ p : Nat, p > n ∧ Fermat_prime p

def goldbach_conjecture : Prop :=
  ∀ n : Nat,
    n > 2 ∧ n % 2 = 0 →
    ∃ a b : Nat,
      prime a ∧
      prime b ∧
      n = a + b

def Fermats_last_theorem : Prop :=
  ∀ n : Nat,
    n > 2 →
    ¬ ∃ a b c : Nat,
      a > 0 ∧
      b > 0 ∧
      c > 0 ∧
      a^n + b^n = c^n
