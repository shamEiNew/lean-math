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
/-
The or-elimination rule is slightly more complicated.
The idea is that we can prove r from p ∨ q, by showing
that r follows from p and that r follows from q.
In other words, it is a proof by cases.
In the expression Or.elim hpq hpr hqr,
Or.elim takes three arguments, hpq : p ∨ q, hpr : p → r and hqr : q → r,
and produces a proof of r.
In the following example, we use Or.elim to prove p ∨ q → q ∨ p.

-/
theorem ex4 (h : p ∨ q) : q ∨ p :=
  Or.elim h
  (fun hp :p=>
      show q ∨ p from Or.intro_right q hp)
  (fun hq :q=>
      show q ∨ p from Or.intro_left p hq)

--NEGATION
theorem ex5 (hpq : p -> q) (hnq : ¬q): ¬p :=
  fun hp : p =>
    show False from hnq (hpq hp)

-- EXERCISES --

variable (p q r : Prop)

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p :=
  Iff.intro
    (fun h1 : p ∧ q =>
      show q ∧ p from And.intro (h1.right) (h1.left))
    (fun h1 : q ∧ p =>
      show p ∧ q from And.intro (h1.right) (h1.left))


example : p ∨ q ↔ q ∨ p :=
  Iff.intro
    (fun h1 : p ∨ q =>
      Or.elim h1
        (fun hp : p =>
          show q ∨ p from Or.intro_right q hp)
        (fun hq : q =>
          show q ∨ p from Or.intro_left p hq))
    (fun h1 : q ∨ p =>
      Or.elim h1
        (fun hq : q =>
          show p ∨ q from Or.intro_right p hq)
        (fun hp : p =>
          show p ∨ q from Or.intro_left q hp))

-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
  Iff.intro
    (fun h1 : (p ∧ q) ∧ r =>
      show p ∧ (q ∧ r) from
        And.intro
          (h1.left.left)
          (And.intro h1.left.right h1.right))
    (fun h2 : p ∧ (q ∧ r) =>
      show (p ∧ q) ∧ r from
        And.intro
          (And.intro h2.left h2.right.left)
          h2.right.right)



example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
  Iff.intro
    (fun h1 : (p ∨ q) ∨ r =>
      Or.elim h1
        (fun hpq : p ∨ q =>
          Or.elim hpq
            (fun hp : p =>
              show p ∨ (q ∨ r) from Or.intro_left (q ∨ r) hp)
            (fun hq : q =>
              show p ∨ (q ∨ r) from Or.intro_right p (Or.intro_left r hq)))
        (fun hr : r =>
          show p ∨ (q ∨ r) from Or.intro_right p (Or.intro_right q hr)))
    (fun h2 : p ∨ (q ∨ r) =>
      Or.elim h2
        (fun hp : p =>
          show (p ∨ q) ∨ r from Or.intro_left r (Or.intro_left q hp))
        (fun hqr : q ∨ r =>
          Or.elim hqr
            (fun hq : q =>
              show (p ∨ q) ∨ r from Or.intro_left r (Or.intro_right p hq))
            (fun hr : r =>
              show (p ∨ q) ∨ r from Or.intro_right (p ∨ q) hr)))

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
Iff.intro
  (λ h : p ∧ (q ∨ r)=>
    Or.elim h.2
      (λ hq:q => Or.inl (And.intro h.1 hq))
      (λ hr:r => Or.inr (And.intro h.1 hr)))
  (λ h : (p ∧ q) ∨ (p ∧ r)=>
    Or.elim h
      (λ hpq:p ∧ q => And.intro hpq.1 (Or.inl hpq.2))
      (λ hpr:p ∧ r => And.intro hpr.1 (Or.inr hpr.2)))



example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) :=
Iff.intro
  (λ h : p ∨ (q ∧ r) =>
    Or.elim h
      (λ hp: p => And.intro (Or.intro_left q hp) (Or.intro_left r hp))
      (λ hqr : q ∧ r => And.intro (Or.intro_right p hqr.1) (Or.intro_right p hqr.2))
  )
  (λ h : (p ∨ q) ∧ (p ∨ r) =>
    Or.elim h.1
      (λ hp : p => Or.intro_left (q ∧ r) hp)
      (λ hq : q =>
        Or.elim h.2
          (λ hp : p => Or.intro_left (q ∧ r) hp)
          (λ hr : r => Or.intro_right p (And.intro hq hr)))

  )

/-In the above there are two cases in forward direction;
Case 1: If I have a proof of p and then I construct proof of (p ∨ q) ∧ (p ∨ r)
without having to worry about q r
Case 2: If I have a proof of q ∧ r then I have proof of both q and r without assuming p

Two nested cases in backward direction
Since its an And statment it will go in one direction
but part of And's are Or so we have two cases which get used
so when I have proof (p ∨ q) ∧ (p ∨ r) that means I have both side proof, with left side
I have proof of p this means we have a proof p ∨ (q ∧ r)
but in case we have a proof of q that means p may be anything and to show p ∨ (q ∧ r) I
must assure that we have a proof of r or p too, therefore
we use the second part of And as that also is True, and assuming p is true then
p ∨ (q ∧ r) as usual, and if r holds using q and r we construct p ∨ (q ∧ r).

-/

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) :=
Iff.intro
(fun h: (p → (q → r)) =>
  fun hpq : p ∧ q =>
    h hpq.1 hpq.2
)
(
  fun h : (p ∧ q → r) =>
    fun hp : p =>
      fun hq : q =>
        h (And.intro hp hq)
)
example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) :=
Iff.intro

  (fun h : (p ∨ q) → r =>
  And.intro (fun hp: p => h (Or.intro_left q hp))
            (fun hq : q => h (Or.intro_right p hq))

  )
  (fun h : (p → r) ∧ (q → r) =>
    fun hpq : (p ∨ q) =>
      Or.elim hpq
        (fun hp: p => h.1 hp)
          (fun hq : q => h.2 hq)
  )
example : ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
Iff.intro
(fun h : ¬(p ∨ q) =>
  And.intro
  (fun hp : p => h (Or.intro_left q hp))
  (fun hq : q => h (Or.intro_right p hq))
)

(λ ⟨hnp, hnq⟩ hpq =>              -- assume ¬p ∧ ¬q and hpq : p ∨ q
    Or.elim hpq
      (λ hp:p=> hnp hp)                 -- if p then contradiction via hnp
      (λ hq:q =>  hnq hq)                 -- if q then contradiction via hnq
)


example : ¬p ∨ ¬q → ¬(p ∧ q) :=
fun h : ¬p ∨ ¬q =>
fun hpq : p ∧ q =>
Or.elim h
 (fun hp: ¬p => hp hpq.1)
 (fun hq: ¬ q => hq hpq.2)


example : ¬(p ∧ ¬p) := fun h : p ∧ ¬p => h.2 h.1


example : p ∧ ¬q → ¬(p → q) :=
fun h : p ∧ ¬q =>
  fun hpq : (p → q) =>
    absurd (hpq h.1) (h.2)

example : ¬p → (p → q) :=
fun h : ¬p =>
  fun hp : p => False.elim (h hp)


example : (¬p ∨ q) → (p → q) :=
fun h : (¬p ∨ q) =>
  fun hp : p =>
    Or.elim h
      (fun hnp: ¬p => False.elim (hnp hp))
      (fun hq : q => hq)

example : p ∨ False ↔ p :=
Iff.intro
  (fun h : p ∨ False =>
    Or.elim h
      (fun hp : p => hp)
      (fun hF: False => hF.elim)
      )
    (fun hp : p => Or.intro_left (False) (hp))


example : p ∧ False ↔ False :=
Iff.intro
  (fun h : p ∧ False => h.2)
  (fun hf : False => hf.elim)


example : (p → q) → (¬q → ¬p) :=
fun h : p → q =>
  fun hnq : ¬q =>
    fun hp : p => False.elim (hnq (h hp))


example : p ∧ (p → q) → q :=
  fun h : p ∧ (p → q) => h.2 h.1
