import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.ModEq
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Tactic

-- Solution to Exercise 1.8.

-- Based on a class project by Aleksander Fedorynski.

theorem obvious_fact_1 (n : ℤ) (h: n ≥ 1) (x : ℤ) : x + n ≠ x := by linarith

theorem helper_fact {a b n x y: ℤ}
    (h: a * x + b * y = n): n = a * (x - b) + b * (y + a) := by linarith


theorem helper_fact_2 {a b n x y : ℤ}
    (h: a ≥ 1 ∧ b ≥ 1 ∧ a * x + b * y = n ∧ n > 2 * a * b - a - b):
        x ≥ b ∨ y ≥ a :=
by_contradiction
(
  λ hc: ¬ (x ≥ b ∨ y ≥ a) ↦
  have hc1: ¬ x ≥ b ∧ ¬ y ≥ a := not_or.mp hc
  have h_xb1: x ≤ b - 1 := by linarith
  have h_ya1: y ≤ a - 1 := by linarith
  have a_pos: a ≥ 0 := by linarith
  have h_ax_ab1: a * x ≤ a * (b - 1) := Int.mul_le_mul_of_nonneg_left h_xb1 a_pos
  have b_pos: b ≥ 0 := by linarith
  have h_by_ba1: b * y ≤ b * (a - 1) := Int.mul_le_mul_of_nonneg_left h_ya1 b_pos
  by
    linarith
)


theorem Lemma_1_61 (a b n x y : ℤ)
(h_sol_xy: a * x + b * y = n)
(a_pos: a ≥ 1)
(b_pos: b ≥ 1)
(x_nneg: x ≥ 0)
(y_nneg: y ≥ 0)
(n_geq: n > 2 * a * b - a - b)
:
∃ (x1 : ℤ), ∃ (y1 : ℤ),
    (x1 ≥ 0 ∧ y1 ≥ 0 ∧ a * x1 + b * y1 = n ∧ (x1 ≠ x ∨ y1 ≠ y)) :=
have h_alt1: a * (x - b) + b * (y + a) = n := (helper_fact h_sol_xy).symm
have h_alt2: a * (x + b) + b * (y - a) = n :=
(
  have h_comm: b * y + a * x = a * x + b * y := add_comm (b * y) (a * x)
  have h_sol_comm: b * y + a * x = n := Eq.trans h_comm h_sol_xy
  have hsymm: b * (y - a) + a * (x + b) = n := (helper_fact h_sol_comm).symm
  have h_comm_2: b * (y - a) + a * (x + b) = a * (x + b) + b * (y - a) := add_comm (b * (y - a)) (a * (x + b))
  show a * (x + b) + b * (y - a) = n from Eq.trans h_comm_2.symm hsymm
)
have h_xgeqb_or_ygeq_a: x ≥ b ∨ y ≥ a := (helper_fact_2
            (And.intro a_pos (And.intro b_pos (And.intro h_sol_xy n_geq))))
have h_xb_neq_x: x + b ≠ x := obvious_fact_1 b b_pos x
have h_ya_neq_y: y + a ≠ y := obvious_fact_1 a a_pos y
Or.elim h_xgeqb_or_ygeq_a
(
  λ h_xgeqb: x ≥ b ↦
  show ∃ (x1 : ℤ), ∃ (y1 : ℤ),
      (x1 ≥ 0 ∧ y1 ≥ 0 ∧ a * x1 + b * y1 = n ∧ (x1 ≠ x ∨ y1 ≠ y)) from
  Exists.intro (x - b)
  (
    Exists.intro (y + a)
    (
      have hxb: x - b ≥ 0 := Int.sub_nonneg_of_le h_xgeqb
      have hya: y + a ≥ 0 :=
      (
        have h0a: 0 ≤ a := Int.le_of_lt a_pos
        have hhhh: a ≤ y + a := Int.le_add_of_nonneg_left y_nneg
        show 0 ≤ y + a from le_trans h0a hhhh
      )
      have h_different: x - b ≠ x ∨ y + a ≠ y :=
        Or.intro_right (x - b ≠ x) h_ya_neq_y
      And.intro hxb (And.intro hya (And.intro h_alt1 h_different))
    )
  )
)
(
  λ h_ygeqa: y ≥ a ↦
  show ∃ (x1 : ℤ), ∃ (y1 : ℤ),
      (x1 ≥ 0 ∧ y1 ≥ 0 ∧ a * x1 + b * y1 = n ∧ (x1 ≠ x ∨ y1 ≠ y)) from
  Exists.intro (x + b)
  (
    Exists.intro (y - a)
    (
      have hxb: x + b ≥ 0 :=
      (
        have h0b: 0 ≤ b := Int.le_of_lt b_pos
        have hhhh: b ≤ x + b := by {
          simp [*] at *
        }
        show 0 ≤ x + b from le_trans h0b hhhh
      )
      have hya: y - a ≥ 0 := by {
        simp [*] at *
      }
      have h_different: x + b ≠ x ∨ y - a ≠ y :=
        Or.intro_left (y - a ≠ y) h_xb_neq_x
      And.intro hxb (And.intro hya (And.intro h_alt2 h_different))
    )
  )
)
