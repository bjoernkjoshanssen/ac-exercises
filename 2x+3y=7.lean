import algebra.ring.boolean_ring

theorem decide_diophantine2_1 (a b n x y : ℕ): a*x+b*y =n → 0 < a → x < n/a + 1 :=
  λ h, λ ha: 0 < a,
  have hh: x*a ≤ n, from
    calc _ = a*x + 0    : by ring
       ... ≤ a*x + (b*y) : add_le_add_left (nat.zero_le  _) (a*x)
       ... = _           : h,
  calc _ ≤ n/a           : (nat.le_div_iff_mul_le ha).mpr hh
     ... < _             : lt_add_one (n/a)

theorem decide_diophantine2_2 (a b n x y : ℕ):
  a*x+b*y =n → 0 < a → 0 < b → x < n/a + 1 ∧ y < n/b + 1 :=
  λ g1, λ ha hb,
  have g2:b*y+a*x =n, from calc _ = a*x+b*y : by ring
                              ... = _       : g1,
  have h1: x < n/a + 1, from decide_diophantine2_1 a b n x y g1 ha,
  have h2: y < n/b + 1, from decide_diophantine2_1 b a n y x g2 hb,
  and.intro h1 h2

instance example_1_59 :
  decidable (∀ x y : ℕ, 2*x+3*y=7 ∧ (x>0→ y>0) ↔ x=2∧  y=1) :=
  decidable_of_iff 
  (∀ x : fin (7/2+1), ∀ y: fin(7/3+1), 2*x.1+3*y.1=7 ∧ (x.1>0→ y.1>0) ↔ x.1=2∧  y.1=1)
  (
    iff.intro (
      λ h x y, iff.intro (
        λ h1,
        have H: 2 * x + 3 * y = 7 ∧ (x > 0 → y > 0) ↔ x = 2 ∧ y = 1, from
          h ⟨ x,
            (decide_diophantine2_2 2 3 7 x y h1.1 (two_pos) three_pos).1
          ⟩ ⟨y,
            (decide_diophantine2_2 2 3 7 x y h1.1 (two_pos) three_pos).2
          ⟩,
        H.mp h1
      )
      (
        λ hxy, and.intro (
          calc 2 * x + 3 * y = 2 * x + 3 * 1: by rw hxy.2
                         ... = 2 * 2 + 3 * 1: by rw hxy.1
                         ... = 7: dec_trivial
        ) (
          λ hx, calc y = 1: hxy.2
                   ... > 0: one_pos
        )
      )
    ) (
      λ h, λ x y, h x.val y.val
    )
  )

example : (∀ x y : ℕ, 2*x+3*y=7 ∧ (x>0→ y>0) ↔ x=2∧  y=1) := dec_trivial
