import Mathlib.Tactic.Ring
import Mathlib.Data.Real.Basic

theorem SW_15_induction (x:ℝ) (k:ℕ) (h0: 0 ≤ x) (h1: x ≤ 1):
  1 - (k:ℝ) * x ≤ (1 - x)^k := Nat.recOn k ( -- Base for induction
    calc 1 - (0:ℕ) * x = 1 - 0*x := by rw [Nat.cast_zero]
                _ = 1 - 0 := by rw [zero_mul]
                _ = 1 := by ring
                _ ≤ 1 := le_refl 1
                _ = (1-x)^0 := (pow_zero (1-x)).symm
  ) ( -- Inductive step 1 - ↑(nat.succ n) * x ≤ (1 - x) ^ nat.succ n
    λ n h ↦
    have H:   0 ≤ 1-x := le_sub_comm.mp (calc
              x ≤ 1 := h1
            _ = 1-0 := by ring)
    have hkk:(1-x)≤ 1 := by {simp;exact h0}
    have hn: (1-x)^n ≤ 1 := (calc
    (1-x)^n ≤ 1^n := pow_le_pow_of_le_left H hkk n
    _ = 1   := one_pow n)
    have hm: -(1*x) ≤ (-(1-x)^n)*x := (calc
    -(1*x) ≤ -((1-x)^n*x) := neg_le_neg (mul_le_mul_of_nonneg_right hn h0)
    _ = (-(1-x)^n)*x := by ring)
    (calc  1 - ↑(Nat.succ n) * x
        = 1 - ↑ (n+1) * x  := by rw [Nat.succ_eq_add_one]
    _ = 1 - (↑n + ↑1) * x         := by norm_cast
    _ = 1 - (↑n * x + ↑1*x)       := by rw [right_distrib (↑ n) (↑ 1) x]
    _ = 1 - (↑n * x + 1*x)        := by norm_cast
    _ = 1 - ↑n * x - 1*x          := by ring
    _ ≤ (1-x)^n    - 1*x          := sub_le_sub h (le_refl (1*x))
    _ = (1-x)^n   + (- (1*x))     := by ring_nf
    _ ≤ (1-x)^n   + (- (1-x)^n)*x := add_le_add (le_refl _) hm
    _ = (1-x) * (1-x)^n           := by ring)
  )
