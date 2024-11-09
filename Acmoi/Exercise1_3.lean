import Mathlib.Data.Int.ModEq
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
-- Solution to Exercise 1.3 in "Automatic complexity: a measure of irregularity"

theorem lemma_1_52 (r x y:ℤ)(hr:0<r)(hy:0 ≤ y)(hx:0 ≤ x) :
  2 * r^2 = (x+y)*r+(y+1) ↔ (x,y) = (r,r-1) :=

  have h₃ : y * r ≤ (x+y)*r := by aesop
  have g₀: 2 * r^2 = (x+y)*r+(y+1) → (x,y) = (r,r-1) :=
    fun h =>
    have : 0  = y+1 - r * ((y+1)/r) := calc
              0 = ((2*r)*r) % r := (Int.mul_emod_left (2 * r) r).symm -- (Int.mul_mod_left (2*r) r).symm
            _ = (2 * r^2) % r :=  by ring_nf
            _ = ((x+y)*r+(y+1)) % r := by rw [h]
            _ = ((y+1)+(x+y)*r) % r := by ring_nf
            _ = (y+1)%r := Int.add_mul_emod_self
            _ = y+1 - r * ((y+1)/r) := Int.emod_def (y + 1) r --Int.mod_def (y+1) r
    have h₄ : y+1 = r * ((y+1)/r) := by linarith
    have : r ∣ (y+1) := Exists.intro ((y+1)/r) h₄ -- note it's \ mid not just |
    have h₀: 0 < y+1 := by linarith
    have h₁: 0 ≤ r := by linarith
    have : 0 < (y+1)/r := Int.ediv_pos_of_pos_of_dvd h₀ h₁ this
    have h₅ : 0 ≤ (y+1)/r := by linarith
    have h₆ : 1 ≤ (y+1)/r := by linarith
    have : 1 = (y+1)/r ∨ 2 ≤ (y+1)/r := eq_or_lt_of_le h₆
    -- First OR statement
    have : r =  y+1    ∨ r*2 ≤ y+1 := Or.elim this (
      fun h =>
      Or.inl (calc r = r *     1    := by ring
                 _ = r * ((y+1)/r)  := congrArg _ h
                 _ = y+1  := h₄.symm)) (
      fun h =>
      Or.inr (calc r*2 = 2*r  := by ring
                  _  ≤ ((y+1)/r) * r  := mul_le_mul h (le_refl r) h₁ h₅
                  _  = r * ((y+1)/r)  := by ring
                  _  = y+1            := h₄.symm)
    )
    -- Second OR statement
    have : y = r-1 ∨ 2*r-1 ≤ y := Or.elim this
      (fun H => Or.inl (by linarith)) (fun H => Or.inr (by linarith))
    Or.elim this (-- Easy case
      fun hyr =>
      have h₇:  r*r = x*r := calc
                  r*r = (2*r^2) - r*r := by ring
                  _ = x*r := by rw [h,hyr];ring
      have hrx: r = x := (mul_left_inj' (ne_of_gt hr)).mp h₇
      Prod.ext hrx.symm hyr
    )
    (fun hry =>-- Contradiction case
      have h₂: 0 ≤ r+1 := by linarith
      have : (2*r-1)* (r+1) ≤ y*(r+1) := mul_le_mul hry (le_refl (r+1)) h₂ hy
      have : 2 * r^2 < 2 * r^2 := by linarith
    False.elim ((lt_self_iff_false (2*r^2)).mp this))
  have g₁ : (x,y) = (r,r-1) → 2* r^2 = (x+y)*r+(y+1)  := fun h =>
    have hx: x=r := congrArg Prod.fst h
    have hy: y=r-1 := congrArg Prod.snd h
    calc 2*r^2 = (r+(r-1)) * r + ((r-1)+1) := by ring
           _ = (x+y)     * r + (y+1):= by rw[hx,hy]
Iff.intro g₀ g₁
