import Mathlib.Tactic.Ring

-- Solution to Exercise 1.3 in "Automatic complexity: a measure of irregularity"

theorem lemma_1_52 (r x y:ℤ)(hr:0<r)(hy:0 ≤ y)(hx:0 ≤ x) :
  2 * r^2 = (x+y)*r+(y+1) ↔ (x,y) = (r,r-1) :=
  -- General facts:
  have hyy: 0 < y+1 := calc
            0 ≤ y   := hy
          _ < y+1 := lt_add_one y

  have hrn: r ≠ 0 := Int.ne_of_gt hr --norm_num.ne_zero_of_pos r hr
  have hlt1: 0 < r+1 := calc
        0 < r:= hr
      _ < r+1:= lt_add_one r
  have hltr: 0 ≤ r := le_of_lt hr
  have hr1: 0 ≤ r+1 := le_of_lt hlt1

  have h5:y ≤ x + y := calc
          y = 0+y := by ring
        _ ≤ x+y:= add_le_add hx (le_refl y)
  have hzxy: 0 ≤ x+y := calc
             0 ≤ y:= hy
            _≤ x+y:=h5
  have h6:y*r ≤ (x+y)*r := mul_le_mul h5 (le_refl r) hltr hzxy
  -- Easy direction, just plugging in:
  have h2: (x,y) = (r,r-1) → 2* r^2 = (x+y)*r+(y+1)  := λ h ↦
    have hx: x=r := congr_arg (λ p:ℤ×ℤ ↦ p.1) h
    have hy: y=r-1 := congr_arg (λ p:ℤ×ℤ ↦ p.2) h
    calc 2*r^2 = (r+(r-1)) * r + ((r-1)+1) := by ring
           _ = (x+y)     * r + (y+1):= by rw[hx,hy]
  -- Hard direction:
  have h1: 2 * r^2 = (x+y)*r+(y+1) → (x,y) = (r,r-1) :=
    λ h:2 * r^2 = (x+y)*r+(y+1) ↦
    have hz3: 0  = y+1 - r * ((y+1)/r) := calc
              0 = ((2*r)*r) % r := (Int.mul_emod_left (2 * r) r).symm -- (Int.mul_mod_left (2*r) r).symm
            _ = (2 * r^2) % r :=  by ring_nf
            _ = ((x+y)*r+(y+1)) % r := by rw [h]
            _ = ((y+1)+(x+y)*r) % r := by ring_nf
            _ = (y+1)%r := Int.add_mul_emod_self
            _ = y+1 - r * ((y+1)/r) := Int.emod_def (y + 1) r --Int.mod_def (y+1) r
    have hy1: y+1 = r * ((y+1)/r) := calc
              y+1 = (y+1-r*((y+1)/r)) + r*((y+1)/r) := by ring
              _ = 0 + r*((y+1)/r) := by rw [hz3]
              _ = r*((y+1)/r):= by ring
    have : r ∣ (y+1) := Exists.intro ((y+1)/r) hy1 -- note it's \ mid not just |
    have hQ: 0 < (y+1)/r := Int.ediv_pos_of_pos_of_dvd hyy hltr this
    have h_Q:0 ≤ (y+1)/r := le_of_lt hQ
    have hone: 1 ≤ (y+1)/r := Int.add_one_le_of_lt hQ
    have : 1 = (y+1)/r ∨ 2 ≤ (y+1)/r := eq_or_lt_of_le hone
    -- First OR statement
    have : r =  y+1    ∨ r*2 ≤ y+1 := Or.elim this (
      λ h11: 1 = (y+1)/r ↦
      Or.inl (calc r = r *     1    := by ring
                 _ = r * ((y+1)/r)  := congr_arg _ h11
                 _ = y+1  := hy1.symm)) (
      λ h2: 2 ≤ (y+1)/r ↦
      Or.inr (calc r*2 = 2*r  := by ring
                  _  ≤ ((y+1)/r) * r  := mul_le_mul h2 (le_refl r) hltr h_Q
                  _  = r * ((y+1)/r)  := by ring
                  _  = y+1            := hy1.symm)
    )
    -- Second OR statement
    have : y = r-1 ∨ 2*r-1 ≤ y := Or.elim this (
      λ H: r = y+1 ↦   Or.inl (calc y = (y+1)-1:= by ring
                              _    = r-1:= by rw [H])) (
      λ H: r*2 ≤ y+1 ↦ Or.inr (calc
        2*r-1 = (r*2) + (-1) := by ring
        _   ≤ (y+1) + (-1) := Int.add_le_add_right H (-1)
        _   = y := by ring)
    ) -- Now finish the proof
    Or.elim this (-- Easy case
      λ hyr : y = r - 1 ↦
      have hurr:  r*r = x*r := calc
                  r*r = (2*r^2) - r*r := by ring
                  _ = x*r := by rw [h,hyr];ring
      have hrx: r = x := (mul_left_inj' hrn).mp hurr
      Prod.ext (id hrx.symm) hyr
    )
    (λ hry:2*r-1≤ y ↦-- Contradiction case
      have hok:(2*r-1)* (r+1) ≤ y*(r+1) := mul_le_mul hry (le_refl (r+1)) hr1 hy
      have : 2 * r^2 < 2 * r^2 := calc
            2 * r^2 < 2 * r^2 + r     := lt_add_of_pos_right (2 * r^2) hr
            _ = (2*r-1)* (r+1)+1  := by ring
            _ ≤ y      * (r+1)+1  :=  add_le_add hok (le_refl 1)
            _ = y  * r + (y + 1)  := by ring
            _ ≤ (x+y)*r+(y+1)     := add_le_add h6 (le_refl (y+1))
            _ = 2 * r^2           := h.symm
    False.elim ((lt_self_iff_false (2*r^2)).mp this))
Iff.intro h1 h2
