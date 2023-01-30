import data.int.basic
import data.int.modeq
import tactic.ring
import ring_theory.coprime.basic
import init.data.nat.gcd
import init.meta.tactic
import init.core
import data.int.basic
import data.num.basic
import logic.basic
-- Based on class project by Rukiyah Walker
open classical
--lemma 1.64: Let x₀, y₀, a, b be positive integers with a and b relatively prime, x₀ < b, and y₀ < a. 
--Then the equation 
--ax + by = ax₀ + by₀ 
--has a unique solution (x,y) in nonnegative integers.

lemma congr_args {x₀ y₀ a b x y: ℤ} : (x,y) = (x₀,y₀) → a*x + b*y = a*x₀ + b*y₀ :=
  λ h0,
  have hxy1: x = x₀, from congr_arg (λ p:ℤ×ℤ, p.1) h0,
  have hxy2: y = y₀, from congr_arg (λ p:ℤ×ℤ, p.2) h0,
  calc _ = a*x₀ + b*y: by rw ← hxy1
    ... = _: by rw hxy2

lemma lemma_1_64 (x₀ y₀ a b x y: ℤ )
  (h1:a > 0)(h2:b > 0)
--  (h3:x₀ > 0)
--  (h4: y₀ > 0)
  (h5:is_coprime a b)
  (h6:x₀ < b)(h7:y₀ < a)
  (h8:x ≥ 0)(h9:y ≥ 0):
  a*x + b*y = a*x₀ + b*y₀ ↔ (x,y) = (x₀, y₀) :=

--second direction (→):
have hab: a*x + b*y = a*x₀ + b*y₀ → (x,y) = (x₀,y₀), from
    λ hab0: a*x + b*y = a*x₀ + b*y₀,
    have hab1: a*x - a*x₀ + b*y = b*y₀, from calc
                              _ = a*x + b*y - a*x₀: by rw add_sub_right_comm
                            ... = _: sub_eq_of_eq_add' hab0,
    have hab2: b*(y₀-y)=a*(x - x₀), from calc
                      _ = b*y₀-b*y  : mul_sub _ _ _
                    ... = a*x-a*x₀  : (eq_sub_of_add_eq hab1).symm
                    ... = a*(x-x₀)  : (mul_sub _ _ _).symm,
    have hab3: b ∣ a*(x - x₀), from dvd.intro (y₀ - y) hab2,
    have hab4: is_coprime b a, from is_coprime_comm.mp h5,
    have hx: b ∣ (x - x₀), from is_coprime.dvd_of_dvd_mul_left hab4 hab3,
    have hx1: (x - x₀) ≡ 0 [ZMOD b], from int.modeq_zero_iff_dvd.mpr hx,
    have hx2: ∃ n, (x - x₀) = n*b, from exists_eq_mul_left_of_dvd hx,
    exists.elim hx2
      (
        λ n,
        λ hn: (x - x₀) = n*b,
        have hn1: x = x₀ + n*b, from eq_add_of_sub_eq' hn,
        or.elim (classical.em (n < 0))
        (
          λ hn2: n < 0,
            have hnx: n ≤ -1, from sub_nonpos.mp hn2,
            have hnx1: n*b ≤ (-1)*b, from (mul_le_mul_right h2).mpr hnx,
            have hnx2: x < 0, from calc
                       _ = x₀ + n*b: hn1
                     ... ≤ x₀ + (-1)*b: add_le_add_left hnx1 x₀
                     ... = x₀ - b: by ring
                     ... < 0: sub_neg.mpr h6,
            absurd h8 (not_le.mpr hnx2)
        )
        (λ hn3: ¬ n < 0,
          or.elim (em' (n = 0))
          (
            λ hnn0: ¬ n = 0,
            have hnn1: n < 0 ∨ n > 0, from ne.lt_or_lt hnn0,
            or.elim (hnn1)
            (
              λ hnn2: n < 0,
              absurd hnn2 hn3
            )
            (
              λ hnn3: n > 0,
              have hnn4: n*b ≥ (1)*b, from (mul_le_mul_right h2).mpr hnn3,
              have hnn5:  x ≥ x₀ + b, from calc
                          _ = x₀ + n*b: hn1
                        ... ≥ x₀ + 1*b: add_le_add_left hnn4 x₀
                        ... = _: by ring,

              have hnn6: a*x ≥ a*(x₀ + b), from (mul_le_mul_left h1).mpr hnn5,
              have hnn7: b*y ≥ b*0, from (mul_le_mul_left h2).mpr h9,

              have hnn8: b*a > b*y₀, from (mul_lt_mul_left h2).mpr h7,
              have hnn9: a*x + b*y > a*x₀ + b*y₀, from calc
                                  _ ≥ a*(x₀ + b) + b*0: add_le_add hnn6 hnn7
                                ... = a*(x₀+b) : by ring
                                ... = a*x₀+a*b: mul_add a x₀ b
                                ... = a*x₀+b*a: by rw (mul_comm a b)
                                ... > _: add_lt_add_left hnn8 (a * x₀),
              absurd hab0 (ne_of_gt hnn9)
            )
          )
          (
           λ hhhn0: n = 0,
              have hhhn1: x = x₀, from calc
                          x = x₀ + n*b: hn1
                        ... = x₀ + 0*b: by rw hhhn0
                        ... = x₀ : by ring,
             have hhhn2: a*x + b*y = a*x + b*y₀, from calc
                                 _ = a*x₀+b*y₀: hab0
                               ... = _: by rw hhhn1,
             have hhhn3: b*y = b*y₀, from (add_right_inj (a * x)).mp hhhn2,
             have hbzero: b≠ 0, from ne_of_gt h2,
             have b≠ 0 → b*y=b*y₀ → y=y₀, from
              λ (ha : b ≠ 0), (mul_right_inj' ha).mp,
             have hhhn4: y = y₀, from this hbzero hhhn3,
            show (x, y) = (x₀, y₀), from congr (congr_arg prod.mk hhhn1) hhhn4
          )
        )
      ),
show a*x + b*y = a*x₀ + b*y₀ ↔ (x,y) = (x₀, y₀), from {mp := hab, mpr := congr_args}
