import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.ModEq
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Tactic

-- Solution to Exercise 1.8.

-- Based on a class project by Aleksander Fedorynski.

theorem obvious_fact_1 (n : ℤ) (h: n ≥ 1) (x : ℤ) : x + n ≠ x := by
  intro hc
  have hn0: n = 0 := by linarith
  subst hn0
  simp only [ge_iff_le, Int.reduceLE] at h

theorem helper_fact {a b n x y: ℤ}
    (h: a * x + b * y = n): n = a * (x - b) + b * (y + a) :=
have h1: a * x + b * y = b * y + a * x := add_comm (a * x) (b * y)
have h2: - (a * b) + b * a + b * y + a * x = - (a * b) + b * a + (b * y + a * x) := add_assoc (- (a * b) + b * a) (b * y) (a * x)
have h3: - (a * b) + b * a + b * y = - (a * b) + (b * a + b * y) := add_assoc (- (a * b)) (b * a) (b * y)
have h4: - (a * b) + (b * a + b * y) = (b * a + b * y) + (- (a * b)) := add_comm (- (a * b)) (b * a + b * y)
have h5: - (a * b) + a * x = a * x + (- (a * b)) := add_comm (- (a * b)) (a * x)
have h6: a + y = y + a := add_comm a y
have h7: a * x + (- (a * b)) = a * x - a * b := sub_eq_add_neg (a * x) (a * b)
have h8: a * (x - b) = a * x - a * b :=
(
    have hh1: a * (x + (-b)) = a * x + a * (-b) := left_distrib a x (-b)
    have hh2: x + (-b) = x - b := sub_eq_add_neg x b
    show a * (x - b) = a * x - a * b by {
      simp [*] at *
      exact hh1
    }
)
calc
n   = a * x + b * y  := by rw [h]
_ = 0 + a * x + b * y  := by rw [zero_add]
_ = (- (a * b) + a * b) + a * x + b * y  := by rw [add_left_neg]
_ = (- (a * b) + b * a) + a * x + b * y  := by rw [mul_comm]
_ = (- (a * b) + b * a) + (a * x + b * y) := by rw [add_assoc]
_ = (- (a * b) + b * a) + (b * y + a * x)  := by rw [h1]
_ = - (a * b) + b * a + (b * y + a * x)  := by rw [add_assoc]
_ = - (a * b) + b * a + b * y + a * x  := by rw [h2]
_ = - (a * b) + (b * a + b * y) + a * x  := by rw [h3]
_ = (b * a + b * y) + (- (a * b)) + a * x  := by rw [h4]
_ = (b * a + b * y) + (- (a * b) + a * x)  := by rw [add_assoc]
_ = b * (a + y) + (- (a * b) + a * x)  := by rw [left_distrib]
_ = b * (a + y) + (a * x + (- (a * b)))  := by rw [h5]
_ = b * (y + a) + (a * x + (- (a * b)))  := by rw [h6]
_ = b * (y + a) + (a * x - a * b)  := by rw [h7]
_ = b * (y + a) + a * (x - b)  := by rw [h8]
_ = a * (x - b) + b * (y + a)  := by rw [add_comm]


theorem helper_fact_2 {a b n x y : ℤ}
    (h: a ≥ 1 ∧ b ≥ 1 ∧ a * x + b * y = n ∧ n > 2 * a * b - a - b):
        x ≥ b ∨ y ≥ a :=
by_contradiction
(
  λ hc: ¬ (x ≥ b ∨ y ≥ a) ↦
  have hc1: ¬ x ≥ b ∧ ¬ y ≥ a := not_or.mp hc
  have h_xb: x < b := by {
    simp [*] at *
    exact hc1.1
  }
  have h_ya: y < a := by {
    simp [*] at *
    exact hc1
  }
  have h_xb1: x ≤ b - 1 := Int.le_sub_one_of_lt h_xb
  have h_ya1: y ≤ a - 1 := Int.le_sub_one_of_lt h_ya
  have a_pos: a ≥ 0 := (calc 0 ≤ 1 := Int.le.intro_sub (1 + 0) rfl
  _ ≤ a := h.1)
  have h_ax_ab1: a * x ≤ a * (b - 1) := Int.mul_le_mul_of_nonneg_left h_xb1 a_pos
  have b_pos: b ≥ 0 := (calc 0 ≤ 1 := Int.le.intro_sub (1 + 0) rfl
  _ ≤ b := h.2.1)
  have h_by_ba1: b * y ≤ b * (a - 1) := Int.mul_le_mul_of_nonneg_left h_ya1 b_pos
  have h_leq: a * x + b * y ≤ a * (b - 1) + b * (a - 1) := Int.add_le_add h_ax_ab1 h_by_ba1
  have h_2ab_ab: a * (b - 1) + b * (a - 1) = 2 * a * b - a - b :=
  (
    have hhh1: a * (b - 1) = a * b - a := by exact mul_sub_one a b
    have hhh2: b * (a - 1) = b * a - b := by exact mul_sub_one b a
    have hhh3: b * a = a * b := mul_comm b a
    have hhh4: b * a - b = a * b - b := by rw [hhh3]
    have hhh5: b * (a - 1) = a * b - b := Eq.trans hhh2 hhh4
    have hhh7: a * b + a * b = 2 * (a * b) := by ring
    have hhh8: 2 * a * b = 2 * (a * b) := by rw [mul_assoc]
    have hhh9: a * b + a * b = 2 * a * b := Eq.trans hhh7 hhh8.symm
    have hhh10: a * b + (a * b - b) = a * b + a * b - b := by exact add_sub (a * b) (a * b) b
    (calc
    a * (b - 1) + b * (a - 1) = a * b - a + b * (a - 1)  := by rw [hhh1]
    _ = a * b - a + (a * b - b)  := by rw [hhh5]
    _ = a * b + (a * b - b) - a  := by exact sub_add_eq_add_sub (a * b) a (a * b - b)
    _ = a * b + a * b - b - a  := by rw [hhh10]
    _ = a * b + a * b - a - b  := by exact sub_right_comm (a * b + a * b) b a
    _ = 2 * a * b - a - b  := by rw [hhh9])
  )
  have h_leq2: a * x + b * y ≤ 2 * a * b - a - b := by {
    simp [*] at *
    exact h_leq
  }
  have h_nleq: n ≤ 2 * a * b - a - b := by {
    simp [*] at *
    exact h_leq
  }
  have h_not_n_ge: ¬ n > 2 * a * b - a - b :=
  (
    λ hhc: n > 2 * a * b - a - b ↦
    have hh1: n ≥ 2 * a * b - a - b := Int.le_of_lt hhc
    have hh2: n = 2 * a * b - a - b := Int.le_antisymm h_nleq hh1
    have hh3: 2 * a * b - a - b ≠ n := Int.ne_of_lt hhc
    absurd hh2.symm hh3
  )
  absurd h.2.2.2 h_not_n_ge
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
