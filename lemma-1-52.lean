import tactic.ring
-- Lemma 1.52, 2022-10-02 version, "Automatic complexity: a measure of irregularity"
lemma lemma_1_52 (r x y:ℤ)(hr:0<r)(hy:0 ≤ y)(hx:0 ≤ x) :
  2 * r^2 = (x+y)*r+(y+1) ↔ (x,y) = (r,r-1) :=
  -- General facts:
  have hyy: 0 < y+1, from calc
            0 ≤ y: hy
          ... < y+1: lt_add_one y,
  have hle: 0 ≤ y+1, from le_of_lt hyy,

  have hrn: r ≠ 0, from norm_num.ne_zero_of_pos r hr,
  have hlt1: 0 < r+1, from calc
        0 < r: hr
      ... < r+1: lt_add_one r,
  have hltr: 0 ≤ r, from le_of_lt hr,
  have hr1: 0 ≤ r+1, from le_of_lt hlt1,

  have h5:y ≤ x + y, from calc
          y = 0+y: by ring
        ... ≤ x+y: add_le_add hx (le_refl y),
  have hzxy: 0 ≤ x+y, from calc
             0 ≤ y: hy
            ...≤ x+y:h5, 
  have h6:y*r ≤ (x+y)*r, from mul_le_mul h5 (le_refl r) hltr hzxy,
  -- Easy direction, just plugging in:
  have h2: (x,y) = (r,r-1) → 2* r^2 = (x+y)*r+(y+1) , from λ h, 
    have hx: x=r,   from congr_arg (λ p:ℤ×ℤ, p.1) h,
    have hy: y=r-1, from congr_arg (λ p:ℤ×ℤ, p.2) h,
    calc 2*r^2 = (r+(r-1)) * r + ((r-1)+1): by ring
           ... = (x+y)     * r + (y+1): by {rw hx,rw hy},
  -- Hard direction:
  have h1: 2 * r^2 = (x+y)*r+(y+1) → (x,y) = (r,r-1), from
    λ h:2 * r^2 = (x+y)*r+(y+1),
    have hz3: 0  = y+1 - r * ((y+1)/r), from calc
              0 = ((2*r)*r) % r:(int.mul_mod_left (2*r) r).symm
            ... = (2 * r^2) % r:by ring_nf
            ... = ((x+y)*r+(y+1)) % r: by rw h
            ... = ((y+1)+(x+y)*r) % r: by ring_nf
            ... = (y+1)%r: int.add_mul_mod_self
            ... = y+1 - r * ((y+1)/r): int.mod_def (y+1) r,
    have hy1: y+1 = r * ((y+1)/r), from calc
              y+1 = (y+1-r*((y+1)/r)) + r*((y+1)/r): by ring
              ... = 0 + r*((y+1)/r): by rw hz3
              ... = r*((y+1)/r): by ring,
    have r ∣ (y+1), from exists.intro ((y+1)/r) hy1, -- note it's \ mid not just |
    have hQ: 0 < (y+1)/r, from int.div_pos_of_pos_of_dvd hyy hltr this,
    have h_Q:0 ≤ (y+1)/r, from le_of_lt hQ,
    have hone: 1 ≤ (y+1)/r, from int.add_one_le_of_lt hQ,
    have 1 = (y+1)/r ∨ 2 ≤ (y+1)/r, from eq_or_lt_of_le hone,
    -- First OR statement
    have r =  y+1    ∨ r*2 ≤ y+1, from or.elim this (
      λ h11: 1 = (y+1)/r,
      or.inl (calc r = r *     1    : by ring
                 ... = r * ((y+1)/r): congr_arg _ h11
                 ... = y+1: hy1.symm)) (
      λ h2: 2 ≤ (y+1)/r,
      or.inr (calc r*2 = 2*r: by ring
                  ...  ≤ ((y+1)/r) * r: mul_le_mul h2 (le_refl r) hltr h_Q
                  ...  = r * ((y+1)/r): by ring
                  ...  = y+1: hy1.symm)
    ),
    -- Second OR statement
    have y = r-1 ∨ 2*r-1 ≤ y, from or.elim this (
      λ H: r = y+1,   or.inl (calc y = (y+1)-1: by ring
                              ...    = r-1: by rw H)) (
      λ H: r*2 ≤ y+1, or.inr (calc
        2*r-1 = (r*2) + (-1): by ring
        ...   ≤ (y+1) + (-1): int.add_le_add_right H (-1)
        ...   = y: by ring)
    ), -- Now finish the proof
    or.elim this (-- Easy case
      λ hyr : y = r - 1,
      have hurr:  r*r = x*r, from calc
                  r*r = (2*r^2) - r*r : by ring
                  ... = x*r : by {rw h,rw hyr,ring,},
      have hrx: r = x, from (mul_left_inj' hrn).mp hurr,
      congr_arg2 (λ (x y : ℤ), (x, y)) hrx.symm hyr
    )
    (λ hry:2*r-1≤ y,-- Contradiction case
      have hok:(2*r-1)* (r+1) ≤ y*(r+1), from mul_le_mul hry (le_refl (r+1)) hr1 hy,
      have  2 * r^2 < 2 * r^2, from calc
            2 * r^2 < 2 * r^2 + r: lt_add_of_pos_right (2 * r^2) hr
                ... = (2*r-1)* (r+1)+1: by ring
                ... ≤ y      * (r+1)+1:  add_le_add hok (le_refl 1)
                ... = y  * r + (y + 1): by ring
                ... ≤ (x+y)*r+(y+1): add_le_add h6 (le_refl (y+1))
                ... = 2 * r^2: h.symm,
    false.elim ((lt_self_iff_false (2*r^2)).mp this)),
iff.intro h1 h2