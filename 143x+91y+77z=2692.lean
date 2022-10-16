import algebra.ring.boolean_ring

def φ : Prop :=
  ∀ x : fin 19, ∀ y : fin 30, ∀ z : fin 35,
  143 * x.1 + 91 * y.1 + 77 * z.1 = 2692 ↔ x.1 = 6 ∧ y.1 = 10 ∧ z.1 = 12

def ψ : Prop :=
  ∀ x y z : ℕ, 143 * x + 91 * y + 77 * z = 2692 ↔ x = 6 ∧ y = 10 ∧ z = 12

instance myφ : decidable (φ) := decidable_of_iff (∀ x : fin 19, ∀ y : fin 30, ∀ z : fin 35,
    143 * x.1 + 91 * y.1 + 77 * z.1 = 2692 ↔ x.1 = 6 ∧ y.1 = 10 ∧ z.1 = 12) (by rw φ)

theorem decide_diophantine3_1 (a b c n x y z : ℕ):
a*x+b*y+c*z =n → 0 < a → x < n/a + 1
:=
λ h, λ ha: 0 < a,
have hh: x*a ≤ n, from calc x*a = a*x + 0     : by ring
                        ... ≤ a*x + (b*y+c*z) : add_le_add_left (nat.zero_le  _) (a*x)
                        ... = a*x + b*y + c*z : by ring
                        ... = n               : h,
  calc _ ≤ n/a           : (nat.le_div_iff_mul_le ha).mpr hh
     ... < _             : lt_add_one (n/a)

theorem decide_diophantine3_3 (a b c n x y z : ℕ):
a*x+b*y+c*z =n → 0 < a → 0 < b → 0 < c → x < n/a + 1 ∧ y < n/b + 1 ∧ z < n/c + 1
:=
λ g1, λ ha hb hc,
have g2:b*y+a*x+c*z =n, from calc _ = a*x+b*y+c*z: by ring
                                ... = _: g1,
have g3:c*z+a*x+b*y =n, from calc _ = a*x+b*y+c*z: by ring
                                ... = _: g1,
have h1: x < n/a + 1, from decide_diophantine3_1 a b c n x y z g1 ha,
have h2: y < n/b + 1, from decide_diophantine3_1 b a c n y x z g2 hb,
have h3: z < n/c + 1, from decide_diophantine3_1 c a b n z x y g3 hc,
and.intro h1 (and.intro h2 h3)

-- #eval 2692/143 -- 18
-- #eval 2692/91  -- 29
-- #eval 2692/77  -- 34
instance remark_2_15 :
  decidable ψ :=
  decidable_of_iff φ
  (
    iff.intro (
      λ h x y z, iff.intro
      -- sorry
      (
        λ h1,
        have H: 143 * x + 91 * y + 77 * z = 2692 ↔ x=6∧  y=10 ∧ z=12, from
          h ⟨ x,
            (decide_diophantine3_3
              143 91 77 2692 x y z h1 dec_trivial dec_trivial dec_trivial).1
          ⟩ ⟨y,
            (decide_diophantine3_3
              143 91 77 2692 x y z h1 dec_trivial dec_trivial dec_trivial).2.1
          ⟩ ⟨z,
            (decide_diophantine3_3
              143 91 77 2692 x y z h1 dec_trivial dec_trivial dec_trivial).2.2
          ⟩,
        H.mp h1
      )
      (
        λ hxyz,
          calc 143 * x + 91 *  y + 77 * z
             = 143 * x + 91 *  y + 77 * 12: by rw hxyz.2.2
         ... = 143 * x + 91 * 10 + 77 * 12: by rw hxyz.2.1
         ... = 143 * 6 + 91 * 10 + 77 * 12: by rw hxyz.1
         ... = 2692: dec_trivial
      )
    ) (
      λ h, λ x y z, h x.val y.val z.val
    )
  )

/- This: -/

--example : ψ := dec_trivial

/- does not terminate in a reasonable amount of time,
  but it is semi-formally verified by the #eval below
-/

#eval (φ : bool) -- tt
