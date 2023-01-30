import data.int.basic
import algebra.ring.boolean_ring

lemma obvious_fact_1 (n : ℤ): n ≥ 1 → ∀ (x : ℤ), x + n ≠ x :=
assume h: n ≥ 1,
assume x,
show x + n ≠ x, from
(
  assume hc: x + n = x,
  have hn0: n = 0, from
  (
    calc
    n   = 0 + n : by rw zero_add
    ... = (-x + x) + n : by rw add_left_neg
    ... = -x + (x + n) : by rw add_assoc
    ... = -x + x : by rw hc
    ... = 0 : by rw add_left_neg
  ),
  have h1leq0Z: ↑1 ≤ ↑0, by from @eq.subst _ ((≤) 1) _ _ hn0 h,
  have h1leq0: 1 ≤ 0, from iff.elim_left int.coe_nat_lt h1leq0Z,
  have h1geq0: 1 ≥ 0, from zero_le_one,
  have h1eq0: 1 = 0, from ge_antisymm h1geq0 h1leq0,
  absurd h1eq0 one_ne_zero
)

lemma helper_fact (a : ℤ) (b : ℤ) (n : ℤ) (x : ℤ) (y: ℤ)
    (h: a * x + b * y = n): n = a * (x - b) + b * (y + a) :=
have h1: a * x + b * y = b * y + a * x,
    from add_comm (a * x) (b * y),
have h2: - (a * b) + b * a + b * y + a * x = - (a * b) + b * a + (b * y + a * x), 
    from add_assoc (- (a * b) + b * a) (b * y) (a * x),
have h3: - (a * b) + b * a + b * y = - (a * b) + (b * a + b * y),
    from add_assoc (- (a * b)) (b * a) (b * y),
have h4: - (a * b) + (b * a + b * y) = (b * a + b * y) + (- (a * b)),
    from add_comm (- (a * b)) (b * a + b * y),
have h5: - (a * b) + a * x = a * x + (- (a * b)),
    from add_comm (- (a * b)) (a * x),
have h6: a + y = y + a, from add_comm a y,
have h7: a * x + (- (a * b)) = a * x - a * b,
    from sub_eq_add_neg (a * x) (a * b),
have h8: a * (x - b) = a * x - a * b, from
(
    have hh1: a * (x + (-b)) = a * x + a * (-b), from left_distrib a x (-b),
    have hh2: x + (-b) = x - b, from sub_eq_add_neg x b,
    show a * (x - b) = a * x - a * b, by simp * at *
),
calc
n   = a * x + b * y : by rw h
... = 0 + a * x + b * y : by rw zero_add
... = (- (a * b) + a * b) + a * x + b * y : by rw add_left_neg
... = (- (a * b) + b * a) + a * x + b * y : by rw mul_comm
... = (- (a * b) + b * a) + (a * x + b * y): by rw add_assoc
... = (- (a * b) + b * a) + (b * y + a * x) : by rw h1
... = - (a * b) + b * a + (b * y + a * x) : by rw add_assoc
... = - (a * b) + b * a + b * y + a * x : by rw h2
... = - (a * b) + (b * a + b * y) + a * x : by rw h3
... = (b * a + b * y) + (- (a * b)) + a * x : by rw h4
... = (b * a + b * y) + (- (a * b) + a * x) : by rw add_assoc
... = b * (a + y) + (- (a * b) + a * x) : by rw left_distrib
... = b * (a + y) + (a * x + (- (a * b))) : by rw h5
... = b * (y + a) + (a * x + (- (a * b))) : by rw h6
... = b * (y + a) + (a * x - a * b) : by rw h7
... = b * (y + a) + a * (x - b) : by rw h8
... = a * (x - b) + b * (y + a) : by rw add_comm

lemma obvious_fact_2 (c : ℤ): c + c = 2 * c :=
calc
c + c = 1 * c + 1 * c : by rw one_mul
    ... = (1 + 1) * c   : by rw right_distrib
    ... = 2 * c         : rfl

lemma obvious_fact_3 (c b a : ℤ):
(c - b) - a = c - b - a :=
by exact rfl

lemma helper_fact_2 (a : ℤ) (b : ℤ) (n : ℤ) (x : ℤ) (y : ℤ)
    (h: a ≥ 1 ∧ b ≥ 1 ∧ a * x + b * y = n ∧ n > 2 * a * b - a - b):
        x ≥ b ∨ y ≥ a :=
by_contradiction
(
  assume hc: ¬ (x ≥ b ∨ y ≥ a),
  have hc1: ¬ x ≥ b ∧ ¬ y ≥ a,
      from iff.elim_left (decidable.not_or_iff_and_not (x ≥ b) (y ≥ a)) hc,
  have h_xb: x < b, by simp * at *,
  have h_ya: y < a, by simp * at *,
  have h_xb1: x ≤ b - 1, from int.le_sub_one_of_lt h_xb,
  have h_ya1: y ≤ a - 1, from int.le_sub_one_of_lt h_ya,
  have a_pos: a ≥ 0, from int.le_trans zero_le_one h.1,
  have h_ax_ab1: a * x ≤ a * (b - 1),
      from mul_le_mul_of_nonneg_left h_xb1 a_pos,
  have b_pos: b ≥ 0, from int.le_trans zero_le_one h.2.1,
  have h_by_ba1: b * y ≤ b * (a - 1),
      from mul_le_mul_of_nonneg_left h_ya1 b_pos,
  have h_leq: a * x + b * y ≤ a * (b - 1) + b * (a - 1),
      from int.add_le_add h_ax_ab1 h_by_ba1,
  have h_2ab_ab: a * (b - 1) + b * (a - 1) = 2 * a * b - a - b,
      from
  (
    have hhh1: a * (b - 1) = a * b - a, by exact mul_sub_one a b,
    have hhh2: b * (a - 1) = b * a - b, by exact mul_sub_one b a,
    have hhh3: b * a = a * b, from mul_comm b a,
    have hhh4: b * a - b = a * b - b, by rw hhh3,
    have hhh5: b * (a - 1) = a * b - b, from eq.trans hhh2 hhh4,
    have hhh6: (a * b - b) - a = a * b - b - a, from obvious_fact_3 (a * b) b a,
    have hhh7: a * b + a * b = 2 * (a * b), from obvious_fact_2 (a * b),
    have hhh8: 2 * a * b = 2 * (a * b), by rw mul_assoc,
    have hhh9: a * b + a * b = 2 * a * b, from eq.trans hhh7 hhh8.symm,
    have hhh10: a * b + (a * b - b) = a * b + a * b - b,
        by exact add_sub (a * b) (a * b) b,
    calc
    a * (b - 1) + b * (a - 1) = a * b - a + b * (a - 1) : by rw hhh1
    ... = a * b - a + (a * b - b) : by rw hhh5
    ... = a * b + (a * b - b) - a : by exact sub_add_eq_add_sub (a * b) a (a * b - b)
    ... = a * b + a * b - b - a : by rw hhh10
    ... = a * b + a * b - a - b : by exact sub_right_comm (a * b + a * b) b a
    ... = 2 * a * b - a - b : by rw hhh9
  ),
  have h_leq2: a * x + b * y ≤ 2 * a * b - a - b, by simp * at *,
  have h_nleq: n ≤ 2 * a * b - a - b, by simp * at *,
  have h_not_n_ge: ¬ n > 2 * a * b - a - b, from
  (
    assume hhc: n > 2 * a * b - a - b,
    have hh1: n ≥ 2 * a * b - a - b, from int.le_of_lt hhc,
    have hh2: n = 2 * a * b - a - b, from int.le_antisymm h_nleq hh1,
    have hh3: 2 * a * b - a - b ≠ n, from int.ne_of_lt hhc,
    absurd hh2.symm hh3
  ),
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
have h_alt1: a * (x - b) + b * (y + a) = n,
    from (helper_fact a b n x y h_sol_xy).symm,
have h_alt2: a * (x + b) + b * (y - a) = n, from
(
  have h_comm: b * y + a * x = a * x + b * y, from add_comm (b * y) (a * x),
  have h_sol_comm: b * y + a * x = n, from eq.trans h_comm h_sol_xy,
  have hsymm: b * (y - a) + a * (x + b) = n,
      from (helper_fact b a n y x h_sol_comm).symm,
  have h_comm_2: b * (y - a) + a * (x + b) = a * (x + b) + b * (y - a),
      from add_comm (b * (y - a)) (a * (x + b)),
  show a * (x + b) + b * (y - a) = n, from eq.trans h_comm_2.symm hsymm
),
have h_xgeqb_or_ygeq_a: x ≥ b ∨ y ≥ a,
    from (helper_fact_2 a b n x y
            (and.intro a_pos (and.intro b_pos (and.intro h_sol_xy n_geq)))),
have h_xb_neq_x: x + b ≠ x, from obvious_fact_1 b b_pos x,
have h_ya_neq_y: y + a ≠ y, from obvious_fact_1 a a_pos y,
or.elim h_xgeqb_or_ygeq_a
(
  assume h_xgeqb: x ≥ b,
  show ∃ (x1 : ℤ), ∃ (y1 : ℤ),
      (x1 ≥ 0 ∧ y1 ≥ 0 ∧ a * x1 + b * y1 = n ∧ (x1 ≠ x ∨ y1 ≠ y)), from
  exists.intro (x - b)
  (
    exists.intro (y + a)
    (
      have hxb: x - b ≥ 0, by simp * at *,
      have hya: y + a ≥ 0, from 
      (
        have h0a: 0 ≤ a, from le_trans zero_le_one a_pos,
        have h00a: a + 0 ≤ a + y, from add_le_add_left y_nneg a,
        have h_a_leq_a0: a ≤ a + 0, by simp * at *,
        have h_a_leq_ay: a ≤ a + y, from le_trans h_a_leq_a0 h00a,
        have hhhh: a ≤ y + a, by simp * at *,
        show 0 ≤ y + a, from le_trans h0a hhhh
      ),
      have h_different: x - b ≠ x ∨ y + a ≠ y, from
        or.intro_right (x - b ≠ x) h_ya_neq_y,
      and.intro hxb (and.intro hya (and.intro h_alt1 h_different))
    )
  )
)
(
  assume h_ygeqa: y ≥ a,
  show ∃ (x1 : ℤ), ∃ (y1 : ℤ),
      (x1 ≥ 0 ∧ y1 ≥ 0 ∧ a * x1 + b * y1 = n ∧ (x1 ≠ x ∨ y1 ≠ y)), from
  exists.intro (x + b)
  (
    exists.intro (y - a)
    (
      have hxb: x + b ≥ 0, from
      (
        have h0b: 0 ≤ b, from le_trans zero_le_one b_pos,
        have h00b: b + 0 ≤ b + x, from add_le_add_left x_nneg b,
        have h_b_leq_b0: b ≤ b + 0, by simp * at *,
        have h_b_leq_bx: b ≤ b + x, from le_trans h_b_leq_b0 h00b,
        have hhhh: b ≤ x + b, by simp * at *,
        show 0 ≤ x + b, from le_trans h0b hhhh
      ),
      have hya: y - a ≥ 0, by simp * at *,
      have h_different: x + b ≠ x ∨ y - a ≠ y, from
        or.intro_left (y - a ≠ y) h_xb_neq_x,
      and.intro hxb (and.intro hya (and.intro h_alt2 h_different))
    )
  )
)
