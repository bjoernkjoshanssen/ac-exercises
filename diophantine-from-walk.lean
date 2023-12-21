import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.IndicatorFunction
import Mathlib.MeasureTheory.Constructions.Prod.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.ProbabilityMassFunction.Basic

set_option tactic.hygienic false

/- Connect the diophantine equation 2x+3y=n with a walk in a digraph that has a cycle of length 2 followed by a cycle of length 3. -/

theorem mod_up {n:ℕ} (h: n % 2 = 0) : n.succ % 2 = 1 := calc
  _ = ((n%2) + 1%2) %2  := Nat.add_mod _ _ _
  _ = (0 + 1%2) % 2     := congrFun (congrArg HMod.hMod (congrFun (congrArg HAdd.hAdd h) (1 % 2))) 2

theorem mod_down {n:ℕ} (h: n % 2 = 1) : n.succ % 2 = 0 := calc
  _ = ((n%2) + 1%2) %2  := Nat.add_mod _ _ _
  _ = (1 + 1%2) % 2     := congrFun (congrArg HMod.hMod (congrFun (congrArg HAdd.hAdd h) (1 % 2))) 2

theorem mod30 {n:ℕ} (h: n % 3 = 0) : n.succ % 3 = 1 := calc
  _ = ((n%3) + 1%3) %3  := Nat.add_mod _ _ _
  _ = (0 + 1%3) % 3     := congrFun (congrArg HMod.hMod (congrFun (congrArg HAdd.hAdd h) (1 % 3))) 3

theorem mod31 {n:ℕ} (h: n % 3 = 1) : n.succ % 3 = 2 := calc
  _ = ((n%3) + 1%3) %3  := Nat.add_mod _ _ _
  _ = (1 + 1%3) % 3     := congrFun (congrArg HMod.hMod (congrFun (congrArg HAdd.hAdd h) (1 % 3))) 3

theorem mod32 {n:ℕ} (h: n % 3 = 2) : n.succ % 3 = 0 := calc
  _ = ((n%3) + 1%3) %3  := Nat.add_mod _ _ _
  _ = (2 + 1%3) % 3     := congrFun (congrArg HMod.hMod (congrFun (congrArg HAdd.hAdd h) (1 % 3))) 3



theorem explicit_formula' {f:ℕ → ℕ}
-- Now we add the possibility of going to state 2... but also rule it out
(h00 : f 0 = 0)
(h0: ∀ t, f t = 0 → f t.succ = 1 ∨ f t.succ = 2)
(h1: ∀ t, f t = 1 → f t.succ = 0)
(t: ℕ)
:
(∀ s, s ≤ t → f s = 0 ∨ f s = 1) →
 f t = t % 2  := by {
  induction t
  rw [h00];
  intro
  rfl
  intro h
  have hfn : f n = n % 2 := n_ih (λ s hsn ↦ h s (Nat.le_step hsn))
  have : n % 2 = 0 ∨ n % 2 = 1 := by exact Nat.mod_two_eq_zero_or_one n
  cases this
  rw [h_1] at hfn
  let g := h0 n hfn
  cases g
  rw [h_2]
  exact (mod_up h_1).symm
  exfalso
  let g₀ := h n.succ (le_refl _)
  cases g₀
  have h02 : 0 = 2 := Eq.trans h_3.symm h_2
  have : ¬ 0 = 2 := by exact Nat.ne_of_beq_eq_false rfl
  exact this h02
  have h02 : 1 = 2 := Eq.trans h_3.symm h_2
  have : ¬ 1 = 2 := by exact Nat.ne_of_beq_eq_false rfl
  exact this h02
  rw [h_1] at hfn
  let g := h1 n hfn
  rw [g]
  exact (mod_down h_1).symm
  }

theorem get_even {f:ℕ → ℕ}
-- When do we first go to two:
(h00 : f 0 = 0)
(h0: ∀ t, f t = 0 → f t.succ = 1 ∨ f t.succ = 2)
(h1: ∀ t, f t = 1 → f t.succ = 0)
(t: ℕ)
(h : (∀ s, s ≤ t → f s = 0 ∨ f s = 1))
(h2: f t.succ = 2):
 t % 2 = 0 := by {
  have ftt : f t = t % 2 := explicit_formula' h00 h0 h1 _ h
  have : f t = 0 ∨ f t = 1 := h _ (le_refl _)
  cases this
  exact Eq.trans ftt.symm h_1
  exfalso
  let g := h1 t h_1
  have h02 : 0 = 2 := Eq.trans g.symm h2
  have : ¬ 0 = 2 := by exact Nat.ne_of_beq_eq_false rfl
  exact this h02

 }

theorem get_equation (a b n : ℕ) (hab: a ≤ b) (han : (b) % n = a % n):
  ∃ k, b = a + n * k := by {
    have : (b - a) % n = 0 := by exact Nat.sub_mod_eq_zero_of_mod_eq han
    have : ∃ k, b - a = n * k  := Nat.dvd_of_mod_eq_zero this
    rcases this with ⟨k,hk⟩
    exists k
    calc
    b = (b-a) + a := (Nat.sub_add_cancel hab).symm
    _ = n*k + a := by rw [hk]
    _ = a + n*k := by ring
  }

theorem get_add_mod_three (f:ℕ → ℕ)
  -- Going through the second cycle:
  (h2: ∀ t, f t = 2 → f t.succ = 3)
  (h3: ∀ t, f t = 3 → f t.succ = 4)
  (h4: ∀ t, f t = 4 → f t.succ = 2)
  (t: ℕ)
  (ht2: f t.succ = 2)
  (s:ℕ)
  : f (t.succ+s) = 2 + s%3 := by {
    induction s;exact ht2
    have : n%3 = 0 ∨ n%3 = 1 ∨ n%3 = 2 := by {
      by_cases (n%3 < 2);rename n%3 < 2 => hn
      by_cases (n%3 < 1);left;exact Nat.lt_one_iff.mp h
      right;left;exact Nat.eq_of_lt_succ_of_not_lt hn h
      right;right;have : n % 3 < 3 := Nat.mod_lt _ (Nat.succ_pos 2)
      exact Nat.eq_of_lt_succ_of_not_lt this h
    }
    cases this;rw [h] at n_ih;rw [add_zero] at n_ih;let g := h2 (t.succ+n) n_ih
    rw [mod30 h];exact g;cases h;rw [h_1] at n_ih;let g := h3 (t.succ+n) n_ih
    rw [mod31 h_1];exact g;rw [h_1] at n_ih;let g := h4 (t.succ+n) n_ih
    rw [mod32 h_1];exact g
  }

theorem get_add_mod_three' {three:ℕ} (f:ℕ → ℕ)
  -- A more general version of get_add_mod_three that doesn't use mod_up
  (h2s: ∀ i t, f t = 2 + (i%three) → f t.succ = 2 + (i.succ %three))
  (t: ℕ)
  (ht2: f t.succ = 2)
  (s:ℕ)
  : f (t.succ+s) = 2 + s%three := by {
    induction s;exact ht2
    let g := h2s n (t.succ+n) n_ih
    exact g
  }
theorem get_mod_three' {three:ℕ} {f:ℕ → ℕ}
-- Going through the second cycle:
  (h2s: ∀ i t, f t = 2 + (i%three) → f t.succ = 2 + (i.succ %three))
(u v: ℕ)
(hu: f u.succ = 2)
(hv: f v.succ = 2)
(huv: u ≤ v)
: u.succ % three = v.succ % three := by {
  have he : ∃ s, v = u + s := by exact Nat.exists_eq_add_of_le huv
  rcases he with ⟨s,hs⟩
  have : f (u.succ + s) = 2 + s%three := get_add_mod_three' _ h2s _ hu _
  rw [hs]
  rw [Nat.succ_add] at this
  rw [← hs] at this
  rw [hv] at this
  have hz : 0 = s % three := by exact Nat.add_left_cancel this
  have hN : Nat.succ (u + s) % three = (Nat.succ u + s) % three := by rw[Nat.succ_add]
  have : (Nat.succ u + s) % three = ((Nat.succ u % three) + s % three) % three:= Nat.add_mod _ _ _
  rw [hN]
  rw [this]
  rw [← hz]
  rw [Nat.add_zero]
  exact (Nat.mod_mod _ _).symm
}
theorem get_multiple_three' {three:ℕ} {f:ℕ → ℕ}
  -- Going through the second cycle:
  (h2s: ∀ i t, f t = 2 + (i%three) → f t.succ = 2 + (i.succ %three))
  (u v: ℕ)
  (hu: f u.succ = 2)
  (hv: f v.succ = 2)
  (huv: u ≤ v)
  : ∃ k, v.succ = u.succ + three * k := by {
    have han : (u.succ) % three = v.succ % three := get_mod_three' h2s _ _ hu hv huv
    have huv' : u.succ ≤ v.succ := Nat.succ_le_succ huv
    exact get_equation _ _ _ huv' han.symm
  }


theorem get_mod_three {f:ℕ → ℕ}
-- Going through the second cycle:
(h2: ∀ t, f t = 2 → f t.succ = 3)
(h3: ∀ t, f t = 3 → f t.succ = 4)
(h4: ∀ t, f t = 4 → f t.succ = 2)
(u v: ℕ)
(hu: f u.succ = 2)
(hv: f v.succ = 2)
(huv: u ≤ v)
: u.succ % 3 = v.succ % 3 := by {
  have he : ∃ s, v = u + s := by exact Nat.exists_eq_add_of_le huv
  rcases he with ⟨s,hs⟩
  have : f (u.succ + s) = 2 + s%3 := get_add_mod_three _ h2 h3 h4 _ hu _
  rw [hs]
  rw [Nat.succ_add] at this
  rw [← hs] at this
  rw [hv] at this
  have hz : 0 = s % 3 := by exact Nat.add_left_cancel this
  have hN : Nat.succ (u + s) % 3 = (Nat.succ u + s) % 3 := by rw[Nat.succ_add]
  have : (Nat.succ u + s) % 3 = ((Nat.succ u % 3) + s % 3) % 3:= Nat.add_mod _ _ _
  rw [hN]
  rw [this]
  rw [← hz]
  rw [Nat.add_zero]
  exact (Nat.mod_mod _ _).symm
}

theorem get_multiple_three {f:ℕ → ℕ}
  -- Going through the second cycle:
  (h2: ∀ t, f t = 2 → f t.succ = 3)
  (h3: ∀ t, f t = 3 → f t.succ = 4)
  (h4: ∀ t, f t = 4 → f t.succ = 2)
  (u v: ℕ)
  (hu: f u.succ = 2)
  (hv: f v.succ = 2)
  (huv: u ≤ v)
  : ∃ k, v.succ = u.succ + 3 * k := by {
    have han : (u.succ) % 3 = v.succ % 3 := get_mod_three h2 h3 h4 _ _ hu hv huv
    have huv' : u.succ ≤ v.succ := Nat.succ_le_succ huv
    exact get_equation _ _ _ huv' han.symm
  }

theorem get_mul_two {f:ℕ → ℕ}
  (h00 : f 0 = 0)
  (h0: ∀ t, f t = 0 → f t.succ = 1 ∨ f t.succ = 2)
  (h1: ∀ t, f t = 1 → f t.succ = 0)
  (t: ℕ)
  (h : (∀ s, s ≤ t → f s = 0 ∨ f s = 1))
  (h2: f t.succ = 2):
  ∃ k, t = 0 + 2 * k := by {
    have : t % 2 = 0 := (get_even h00 h0 h1 _ h h2)
    exact get_equation _ _ _ (zero_le _) this
  }
  -- Let's combine get_multiple_three and get_mul_two to have a diophantine equation:
  -- t₀ is auxiliary here; later we can argue such t₀ must exist


theorem least_number_principle
  (Z : ℕ → Prop)
  : (∃ u, Z u) → ∃ t₀:ℕ, Z t₀ ∧ ∀ v, Z v → t₀ ≤ v
  := by {
    intro h
    by_contra
    rename ¬∃ t₀, Z t₀ ∧ ∀ (v : ℕ), Z v → t₀ ≤ v => hcontra
    have : (∀ n, ((∀ m, m < n → ¬ Z m) → ¬ Z n)) := by {
      intro n
      intro hn
      by_contra
      have : ∃ t₀, Z t₀ ∧ ∀ (v : ℕ), Z v → t₀ ≤ v := by {
        exists n
        constructor
        exact a
        intro v hv
        have : n ≤ v ∨ v < n := by exact le_or_gt n v
        cases this
        exact h_1
        let g := hn v h_1
        exfalso
        exact g hv
      }
      exact hcontra this
    }
    have : ∀ n, ¬ Z n := λ n ↦  Nat.strong_induction_on n this
    rcases h with ⟨u,hu⟩
    exact this u hu
  }


theorem get_1st_two   (f:ℕ → ℕ)
  (u: ℕ)
  (hu : f u.succ = 2) : ∃ t₀:ℕ, f t₀.succ = 2 ∧ ∀ v, f v.succ = 2 → t₀ ≤ v
  := least_number_principle _ (by {exists u})


theorem two_of_01   (f:ℕ → ℕ)
  (h00 : f 0 = 0)
  (h0: ∀ t, f t = 0 → f t.succ = 1 ∨ f t.succ = 2)
  (h1: ∀ t, f t = 1 → f t.succ = 0)
  (u: ℕ)
  (hu : f u.succ = 2) : ∃ t₀, (∀ s, s ≤ t₀ → f s = 0 ∨ f s = 1) ∧ f t₀.succ = 2
  := by {
    have : ∃ t₀:ℕ, f t₀.succ = 2 ∧ ∀ v, f v.succ = 2 → t₀ ≤ v := get_1st_two _ u hu
    rcases this with ⟨t₀, ht₀⟩
    exists t₀
    constructor
    intro s
    induction s
    intro
    left
    exact h00
    intro hn
    have : n ≤ t₀ := by exact Nat.le_of_lt hn
    let g := n_ih this
    cases g
    right
    let gg := h0 n h
    cases gg
    exact h_1
    exfalso
    have : t₀ ≤ n := ht₀.2 _ h_1
    have : n.succ ≤ n := by exact Nat.le_trans hn this
    exact Nat.le_lt_antisymm this (by exact Nat.lt.base n)
    left
    exact h1 n h
    exact ht₀.1
  }

theorem get_diophantine'  (f:ℕ → ℕ)
-- And here we have the equation 2x+3y=7
  {three : ℕ} -- it works for any cycle length, not just three
  (h00 : f 0 = 0)
  (h0: ∀ t, f t = 0 → f t.succ = 1 ∨ f t.succ = 2)
  (h1: ∀ t, f t = 1 → f t.succ = 0)
  (h2s: ∀ i t, f t = 2 + (i%three) → f t.succ = 2 + (i.succ %three))
  (u: ℕ)
  (hu : f u.succ = 2)
  : ∃ k₀ k₁, u.succ = k₀ * 2 + 1 + k₁ * three  := by {
    have : ∃ t₀, (∀ s, s ≤ t₀ → f s = 0 ∨ f s = 1) ∧ f t₀.succ = 2 := two_of_01 _ h00 h0 h1 u hu
    rcases this with ⟨t₀,ht₀⟩
    let h := ht₀.1
    let ht2 := ht₀.2
    have ht₀u : t₀ ≤ u := by {
      have : t₀ ≤ u ∨ u < t₀ := by exact le_or_gt t₀ u
      cases this
      exact h_1
      have : u.succ ≤ t₀ := by exact h_1
      let g := h u.succ this
      cases g
      exfalso
      have h02 : 0 = 2 := Eq.trans h_2.symm hu
      have : ¬ 0 = 2 := by exact Nat.ne_of_beq_eq_false rfl
      exact this h02
      have h12 : 1 = 2 := Eq.trans h_2.symm hu
      have : ¬ 1 = 2 := by exact Nat.ne_of_beq_eq_false rfl
      exfalso
      exact this h12
      }
    have : ∃ k, t₀ = 0 + 2 * k := get_mul_two h00 h0 h1 _ h ht2
    rcases this with ⟨k₀,hk₀⟩
    exists k₀
    have : ∃ k, u.succ = t₀.succ + three * k := get_multiple_three' h2s _ _ ht2 hu ht₀u
    rcases this with ⟨k₁,hk₁⟩
    exists k₁
    rw [hk₁]
    rw [hk₀]
    rw [zero_add]
    linarith
  }


theorem get_diophantine  (f:ℕ → ℕ)
-- And here we have the equation 2x+3y=7
  (h00 : f 0 = 0)
  (h0: ∀ t, f t = 0 → f t.succ = 1 ∨ f t.succ = 2)
  (h1: ∀ t, f t = 1 → f t.succ = 0)
  (h2: ∀ t, f t = 2 → f t.succ = 3)
  (h3: ∀ t, f t = 3 → f t.succ = 4)
  (h4: ∀ t, f t = 4 → f t.succ = 2)
  (u: ℕ)
  (hu : f u.succ = 2)
  : ∃ k₀ k₁, u.succ = k₀ * 2 + 1 + k₁ * 3  := by {
    have : ∃ t₀, (∀ s, s ≤ t₀ → f s = 0 ∨ f s = 1) ∧ f t₀.succ = 2 := two_of_01 _ h00 h0 h1 u hu
    rcases this with ⟨t₀,ht₀⟩
    let h := ht₀.1
    let ht2 := ht₀.2
    have ht₀u : t₀ ≤ u := by {
      have : t₀ ≤ u ∨ u < t₀ := by exact le_or_gt t₀ u
      cases this
      exact h_1
      have : u.succ ≤ t₀ := by exact h_1
      let g := h u.succ this
      cases g
      exfalso
      have h02 : 0 = 2 := Eq.trans h_2.symm hu
      have : ¬ 0 = 2 := by exact Nat.ne_of_beq_eq_false rfl
      exact this h02
      have h12 : 1 = 2 := Eq.trans h_2.symm hu
      have : ¬ 1 = 2 := by exact Nat.ne_of_beq_eq_false rfl
      exfalso
      exact this h12
      }
    have : ∃ k, t₀ = 0 + 2 * k := get_mul_two h00 h0 h1 _ h ht2
    rcases this with ⟨k₀,hk₀⟩
    exists k₀
    have : ∃ k, u.succ = t₀.succ + 3 * k := get_multiple_three h2 h3 h4 _ _ ht2 hu ht₀u
    rcases this with ⟨k₁,hk₁⟩
    exists k₁
    rw [hk₁]
    rw [hk₀]
    rw [zero_add]
    linarith
  }
