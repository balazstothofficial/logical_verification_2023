/- Copyright © 2018–2023 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVelib


/- # LoVe Exercise 4: Forward Proofs -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## Question 1: Connectives and Quantifiers

1.1. Supply structured proofs of the following theorems. -/

theorem I (a : Prop) :
  a → a :=
  assume ha : a
  show a from
    ha

theorem K (a b : Prop) :
  a → b → b :=
  assume ha : a
  assume hb : b
  show b from hb


theorem C (a b c : Prop) :
  (a → b → c) → b → a → c :=
  assume habc : a → b → c
  assume hb : b
  assume ha : a
  show c from
    habc ha hb

theorem proj_fst (a : Prop) :
  a → a → a :=
  assume ha : a
  assume ha' : a
  show a from ha

/- Please give a different answer than for `proj_fst`. -/

theorem proj_snd (a : Prop) :
  a → a → a :=
  assume ha : a
  assume ha' : a
  show a from ha'

theorem some_nonsense (a b c : Prop) :
  (a → b → c) → a → (a → c) → b → c :=
  assume habc : a → b → c
  assume ha : a
  assume hac : a → c
  assume hb : b
  show c from
    hac ha

/- 1.2. Supply a structured proof of the contraposition rule. -/

theorem contrapositive (a b : Prop) :
  (a → b) → ¬ b → ¬ a :=
  assume hab : a → b
  assume hnb : ¬ b
  assume ha : a
  show False from
    hnb $ hab ha

/- 1.3. Supply a structured proof of the distributivity of `∀` over `∧`. -/

theorem forall_and {α : Type} (p q : α → Prop) :
  (∀x, p x ∧ q x) ↔ (∀x, p x) ∧ (∀x, q x) :=
  Iff.intro
    (
      assume hall : ∀x, p x ∧ q x

      have hpx : ∀x, p x :=
        fix x : α
        show p x from
          And.left $ hall x

      have hqx : ∀x, q x :=
        fix x : α
        show q x from
          And.right $ hall x

      show (∀x, p x) ∧ (∀x, q x) from
       And.intro (hpx) (hqx)
    )
    (
      assume hall : (∀x, p x) ∧ (∀x, q x)
      fix x : α

      have hp: p x :=
        And.left hall x

      have hq: q x :=
        And.right hall x

      show p x ∧ q x from
        And.intro hp hq
    )

/- 1.4 (**optional**). Supply a structured proof of the following property,
which can be used to pull a `∀` quantifier past an `∃` quantifier. -/

theorem forall_exists_of_exists_forall {α : Type} (p : α → α → Prop) :
  (∃x, ∀y, p x y) → (∀y, ∃x, p x y) :=
  assume hex : ∃x, ∀y, p x y
  fix y : α

  show ∃x, p x y from
    Exists.elim hex
    (
      fix x : α
      assume h : ∀ y, p x y

      have hp: p x y :=
        h y

      show ∃ x, p x y from
        Exists.intro x hp
    )



/- ## Question 2: Chain of Equalities

2.1. Write the following proof using `calc`.

      (a + b) * (a + b)
    = a * (a + b) + b * (a + b)
    = a * a + a * b + b * a + b * b
    = a * a + a * b + a * b + b * b
    = a * a + 2 * a * b + b * b

Hint: This is a difficult question. You might need the tactics `simp` and
`ac_rfl` and some of the theorems `mul_add`, `add_mul`, `add_comm`, `add_assoc`,
`mul_comm`, `mul_assoc`, , and `Nat.two_mul`. -/

theorem binomial_square (a b : ℕ) :
  (a + b) * (a + b) = a * a + 2 * a * b + b * b :=
  calc
    (a + b) * (a + b) = a * (a + b) + b * (a + b) :=
      by simp[mul_add, mul_comm]
    _ = a * a + a * b + b * a + b * b :=
      by simp[mul_add, add_assoc]
    _ = a * a + a * b + a * b + b * b :=
      by ac_rfl
    _ = a * a + 2 * a * b + b * b :=
      by simp[Nat.two_mul, add_mul, add_assoc]

/- 2.2 (**optional**). Prove the same argument again, this time as a structured
proof, with `have` steps corresponding to the `calc` equations. Try to reuse as
much of the above proof idea as possible, proceeding mechanically. -/

theorem binomial_square₂ (a b : ℕ) :
  (a + b) * (a + b) = a * a + 2 * a * b + b * b :=

  have h1: (a + b) * (a + b) = a * (a + b) + b * (a + b) :=
     by simp[mul_add, mul_comm]

  have h2: a * (a + b) + b * (a + b) = a * a + a * b + b * a + b * b :=
    by simp[mul_add, add_assoc]

  have h3: a * a + a * b + b * a + b * b = a * a + a * b + a * b + b * b :=
    by ac_rfl

  have h4: a * a + a * b + a * b + b * b = a * a + 2 * a * b + b * b :=
    by simp[Nat.two_mul, add_mul, add_assoc]

  show (a + b) * (a + b) = a * a + 2 * a * b + b * b from
    Eq.trans (Eq.trans (Eq.trans h1 h2) h3) h4


/- ## Question 3 (**optional**): One-Point Rules

3.1 (**optional**). Prove that the following wrong formulation of the one-point
rule for `∀` is inconsistent, using a structured proof. -/

axiom All.one_point_wrong {α : Type} (t : α) (P : α → Prop) :
  (∀x : α, x = t ∧ P x) ↔ P t

#check All.one_point_wrong True (fun x ↦ x = True)

theorem All.proof_of_False :
  False :=
  have h1: (∀ x, x = True ∧ x = True) ↔ True = True :=
     All.one_point_wrong True (fun x ↦ x = True)

  have h2: True = True → (∀ x, x = True ∧ x = True) :=
    Iff.mpr h1

  have h3: True → (∀ x, x = True ∧ x = True) :=
    by simp[h2, refl]

  have h4: ∀ x, x = True ∧ x = True :=
    by simp[h3]

  have h5: False = True ∧ False = True :=
    h4 False

  have h6: False = True :=
    And.left h5

  show False from
    by simp[h6]

/- 3.2 (**optional**). Prove that the following wrong formulation of the
one-point rule for `∃` is inconsistent, using a structured proof. -/

axiom Exists.one_point_wrong {α : Type} (t : α) (P : α → Prop) :
  (∃x : α, x = t → P x) ↔ P t

#check Exists.one_point_wrong False (fun x ↦ x = True)

theorem Exists.proof_of_False :
  False :=
  have h1: (∃ x, x = False → x = True) ↔ False = True :=
    Exists.one_point_wrong False (fun x ↦ x = True)

  have h2: (∃x, x = False → x = True) → False = True :=
    Iff.mp h1

  have h3: False = True :=
    have h3': True = False → True = True :=
      by simp

    have h3'': (∃x, x = False → x = True) :=
       Exists.intro True h3'

    show False = True from
      h2 h3''

  show False from
    by simp[h3]

end LoVe
