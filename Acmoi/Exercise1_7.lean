import Mathlib.Data.Int.ModEq
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Tactic.Linarith
-- Solution to Exercise 1.7.

-- Based on class project by Rukiyah Walker

--lemma 1.64: Let x₀, y₀, a, b be positive integers with a and b relatively prime, x₀ < b, and y₀ < a.
--Then the equation
--ax + by = ax₀ + by₀
--has a unique solution (x,y) in nonnegative integers.


theorem congr_args {x₀ y₀ a b x y: Int} : (x,y) = (x₀,y₀) → a*x + b*y = a*x₀ + b*y₀ :=
  λ h0 ↦
  have hxy1: x = x₀ := congrArg (λ p:Int×Int↦ p.1) h0
  have hxy2: y = y₀ := congrArg (λ p:Int×Int↦ p.2) h0
  calc _ = a*x₀ + b*y := by rw [← hxy1]
       _ = _ := by rw [hxy2]

theorem lemma_1_64 (x₀ y₀ a b x y: ℤ )
  (h1:a > 0)(h2:b > 0)
--  (h3:x₀ > 0)
--  (h4: y₀ > 0)
  (h5:IsCoprime a b)
  (h6:x₀ < b)(h7:y₀ < a)
  (h8:x ≥ 0)(h9:y ≥ 0):
  a*x + b*y = a*x₀ + b*y₀ ↔ (x,y) = (x₀, y₀) :=
--second direction (→):
have hab: a*x + b*y = a*x₀ + b*y₀ → (x,y) = (x₀,y₀) :=
    λ hab0: a*x + b*y = a*x₀ + b*y₀ ↦
    have hab1: a*x - a*x₀ + b*y = b*y₀ := calc
                              _ = a*x + b*y - a*x₀ := by rw [add_sub_right_comm]
                            _ = _ := sub_eq_of_eq_add' hab0
    have hab2: b*(y₀-y)=a*(x - x₀) := calc
                      _ = b*y₀-b*y  := mul_sub _ _ _
                    _ = a*x-a*x₀  := (eq_sub_of_add_eq hab1).symm
                    _ = a*(x-x₀)  := (mul_sub _ _ _).symm
    have hab3:  b ∣ (a*(x - x₀)) := Dvd.intro (y₀ - y) hab2
    have hab4: IsCoprime b a := isCoprime_comm.mp h5
    have hx:  b ∣ (x - x₀) := IsCoprime.dvd_of_dvd_mul_left hab4 hab3
    have hx2: ∃ n, (x - x₀) = n*b := exists_eq_mul_left_of_dvd hx
    Exists.elim hx2
      (
        λ n ↦
        λ hn: (x - x₀) = n*b ↦
        have hn1: x = x₀ + n*b := eq_add_of_sub_eq' hn
        Or.elim (Classical.em (n < 0))
        (
          λ hn2: n < 0 ↦
            have hnx: n ≤ -1 := sub_nonpos.mp hn2
            have hnx1: n*b ≤ (-1)*b := (mul_le_mul_right h2).mpr hnx
            have hnx2: x < 0 := calc
                       _ = x₀ + n*b   := hn1
                     _ ≤ x₀ + (-1)*b  := add_le_add_left hnx1 x₀
                     _ = x₀ - b       := by ring
                     _ < 0            := sub_neg.mpr h6
            absurd h8 (not_le.mpr hnx2)
        )
        (λ hn3: ¬ n < 0 ↦
          Or.elim (em' (n = 0))
          (
            λ hnn0: ¬ n = 0 ↦
            have hnn1: n < 0 ∨ n > 0 := Ne.lt_or_lt hnn0
            Or.elim (hnn1)
            (
              λ hnn2: n < 0 ↦
              absurd hnn2 hn3
            )
            (
              λ hnn3: n > 0 ↦
              have hnn4: n*b ≥ (1)*b := (mul_le_mul_right h2).mpr hnn3
              have hnn5:  x ≥ x₀ + b := calc
                          _ = x₀ + n*b  := hn1
                          _ ≥ x₀ + 1*b  := add_le_add_left hnn4 x₀
                          _ = _         := by ring

              have hnn6: a*x ≥ a*(x₀ + b) := (mul_le_mul_left h1).mpr hnn5
              have hnn7: b*y ≥ b*0 := (mul_le_mul_left h2).mpr h9

              have hnn8: b*a > b*y₀ := (mul_lt_mul_left h2).mpr h7
              have hnn9: a*x + b*y > a*x₀ + b*y₀ := calc
                                 _ ≥ a*(x₀ + b) + b*0 := add_le_add hnn6 hnn7
                                 _ = a*(x₀+b)         := by ring
                                 _ = a*x₀+a*b         := mul_add a x₀ b
                                 _ = a*x₀+b*a         := by rw [mul_comm a b]
                                 _ > _                := add_lt_add_left hnn8 (a * x₀)
              absurd hab0 (ne_of_gt hnn9)
            )
          )
          (
           λ hhhn0: n = 0 ↦
              have hhhn1: x = x₀ := calc
                          x = x₀ + n*b := hn1
                        _ = x₀ + 0*b   := by rw [hhhn0]
                        _ = x₀         := by ring
             have hhhn2: a*x + b*y = a*x + b*y₀ := calc
                                 _ = a*x₀+b*y₀ := hab0
                               _ = _           := by rw [hhhn1]
             have hhhn3: b*y = b*y₀ := (add_right_inj (a * x)).mp hhhn2
             have hbzero: b≠ 0 := ne_of_gt h2
             have invalid_pattern: (b≠ 0) → (b*y=b*y₀) → (y=y₀) :=
              λ (ha : b ≠ 0)↦ (mul_right_inj' ha).mp
             have hhhn4: y = y₀ := invalid_pattern hbzero hhhn3
            show (x, y) = (x₀, y₀) from congr (congr_arg Prod.mk hhhn1) hhhn4
          )
        )
      )
show a*x + b*y = a*x₀ + b*y₀ ↔ (x,y) = (x₀, y₀) from {mp := hab, mpr := congr_args}
