import data.real.basic

theorem SW_15_induction (x:ℝ) (k:ℕ) (h0: 0 < x) (h1: x < 1) (hk: 1 ≤ k):
  1 - (k:ℝ) * x ≤ (1 - x)^k := nat.rec_on k ( -- Base for induction
    calc 1 - ↑0 * x = 1 - 0*x: by rw nat.cast_zero
                ... = 1 - 0: by rw zero_mul
                ... = 1: by ring
                ... ≤ 1: le_refl 1
                ... = (1-x)^0: pow_zero (1-x)
  ) ( -- Inductive step 1 - ↑(nat.succ n) * x ≤ (1 - x) ^ nat.succ n
    λ n, λ h,
    have H:   0 ≤ 1-x, from le_sub.mp (calc
              x ≤ 1: le_of_lt h1
            ... = 1-0: by ring),
    have hkk:(1-x)≤ 1, from by {simp,exact (le_of_lt h0),},
    have hn: (1-x)^n ≤ 1, from calc
             (1-x)^n ≤ 1^n : pow_le_pow_of_le_left H hkk n
                 ... = 1   : one_pow n,
    have hm: -(1*x) ≤ (-(1-x)^n)*x, from calc
             -(1*x) ≤ -((1-x)^n*x): neg_le_neg (mul_le_mul_of_nonneg_right hn (le_of_lt h0))
                ... = (-(1-x)^n)*x: by ring,
    calc  1 - ↑(nat.succ n) * x
        = 1 - ↑ (n+1) * x  : by rw nat.succ_eq_add_one
    ... = 1 - (↑n + ↑1) * x         : by norm_cast
    ... = 1 - (↑n * x + ↑1*x)       : by rw right_distrib (↑ n) (↑ 1) x
    ... = 1 - (↑n * x + 1*x)        : by norm_cast
    ... = 1 - ↑n * x - 1*x          : by ring
    ... ≤ (1-x)^n    - 1*x          : sub_le_sub h (le_refl (1*x))
    ... ≤ (1-x)^n   + (- (1*x))     : by ring_nf
    ... ≤ (1-x)^n   + (- (1-x)^n)*x : add_le_add (le_refl _) hm
    ... = (1-x) * (1-x)^n           : by ring
  )