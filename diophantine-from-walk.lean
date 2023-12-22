import Mathlib.Computability.NFA
import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.IndicatorFunction
import Mathlib.MeasureTheory.Constructions.Prod.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.ProbabilityMassFunction.Basic

set_option tactic.hygienic false



/- Connect the diophantine equation 2x+3y=n with a walk in a digraph that has a cycle of length 2 followed by a cycle of length 3. -/

theorem explicit_formula {two:ℕ}
(htwo: 1 < two)
{f:ℕ → ℕ}
-- like explicit_formula' but with two instead of 2
(h00 : f 0 = 0)
(h0: ∀ t, f t = 0 → f t.succ = 1 ∨ f t.succ = two)
(h1: ∀ i t : ℕ, i % two ≠ 0 → f t = i % two → f t.succ = (i.succ) % two)
(t: ℕ)
:
(∀ s, s ≤ t → f s < two) →
 f t = t % two  := by {
  induction t
  rw [h00];
  intro
  rfl
  intro h
  have hfn : f n = n % two := n_ih (λ s hsn ↦ h s (Nat.le_step hsn))
  rename ∀ (s : ℕ), s ≤ Nat.succ n → f s < two => hs
  by_cases (n % two = 0)
  rw [h] at hfn
  let g := h0 n hfn
  cases g
  rw [h_1]
  have : (n+1) % two = (n % two + 1 % two) % two := Nat.add_mod _ _ _
  rw [h,zero_add,Nat.mod_mod] at this
  have ht: 1 % two = 1 := Nat.mod_eq_of_lt htwo
  rw [ht] at this
  exact this.symm

  rw [h_1]
  exfalso
  let gg := hs n.succ (le_refl _)
  have : two < two := Eq.trans_lt (id h_1.symm) gg
  exact LT.lt.false this
  let g := h1 n n h hfn
  exact g
 }



theorem get_even' {two:ℕ}
-- like get_even but with two instead of 2
(htwo: 1 < two)
{f:ℕ → ℕ}
(h00 : f 0 = 0)
(h0: ∀ t, f t = 0 → f t.succ = 1 ∨ f t.succ = two)
(h1: ∀ i t : ℕ, i % two ≠ 0 → f t = i % two → f t.succ = (i.succ) % two)
(t: ℕ)
(h : (∀ s, s ≤ t → f s < two))
(h2: f t.succ = two):
 t % two = 0 := by {
  have ftt : f t = t % two := explicit_formula htwo h00 h0 h1 (by {
    exact t
  }) h
  by_contra
  rename ¬ (t % two = 0) => hcontra
  let g := h1 t t hcontra ftt
  have ht1: t.succ % two = two := Eq.trans g.symm h2
  have ht2: t.succ % two < two := Nat.mod_lt _ (Nat.zero_lt_of_lt htwo)
  have : two < two := Eq.trans_lt ht1.symm ht2
  exact LT.lt.false this
 }



theorem get_equation {a b n : ℕ} (hab: a ≤ b) (han : (b) % n = a % n):
  ∃ k, b = a + n * k := by {
    have : (b - a) % n = 0 := Nat.sub_mod_eq_zero_of_mod_eq han
    have : ∃ k, b - a = n * k  := Nat.dvd_of_mod_eq_zero this
    rcases this with ⟨k,hk⟩
    exists k
    calc
    b = (b-a) + a := (Nat.sub_add_cancel hab).symm
    _ = n*k + a := by rw [hk]
    _ = a + n*k := by ring
  }


theorem get_add_mod_three'' {two three:ℕ} (f:ℕ → ℕ)
  -- A more general version of get_add_mod_three that doesn't use mod_up
  (h2s: ∀ i t, f t = two + (i%three) → f t.succ = two + (i.succ %three))
  (t: ℕ)
  (ht2: f t.succ = two)
  (s:ℕ)
  : f (t.succ+s) = two + s%three := by {
    induction s;exact ht2
    let g := h2s n (t.succ+n) n_ih
    exact g
  }

theorem get_mod_three'' { two three:ℕ} {f:ℕ → ℕ}
  -- Going through the second cycle:
  (h2s: ∀ i t, f t = two + (i%three) → f t.succ = two + (i.succ %three))
  {u v: ℕ}
  (hu: f u.succ = two)
  (hv: f v.succ = two)
  (huv: u ≤ v)
  : u.succ % three = v.succ % three := by {
  have he : ∃ s, v = u + s := Nat.exists_eq_add_of_le huv
  rcases he with ⟨s,hs⟩
  have : f (u.succ + s) = two + s%three := get_add_mod_three'' _ h2s _ hu _
  rw [hs]
  rw [Nat.succ_add,← hs,hv] at this
  have hz : 0 = s % three := Nat.add_left_cancel this
  have hN : Nat.succ (u + s) % three = (Nat.succ u + s) % three := by rw[Nat.succ_add]
  have : (Nat.succ u + s) % three = ((Nat.succ u % three) + s % three) % three:= Nat.add_mod _ _ _
  rw [hN,this,← hz,Nat.add_zero]
  exact (Nat.mod_mod _ _).symm
}

theorem get_multiple_three'' {two three:ℕ} {f:ℕ → ℕ}
  -- Going through the second cycle:
  (h2s: ∀ i t, f t = two + (i%three) → f t.succ = two + (i.succ %three))
  {u v: ℕ}
  (hu: f u.succ = two)
  (hv: f v.succ = two)
  (huv: u ≤ v)
  : ∃ k, v.succ = u.succ + three * k := by {
    have han : (u.succ) % three = v.succ % three := get_mod_three'' h2s hu hv huv
    have huv' : u.succ ≤ v.succ := Nat.succ_le_succ huv
    exact get_equation huv' han.symm
  }

theorem get_mul_two'
 {two:ℕ}
-- like get_even but with two instead of 2
(htwo: 1 < two)
{f:ℕ → ℕ}
(h00 : f 0 = 0)
(h0: ∀ t, f t = 0 → f t.succ = 1 ∨ f t.succ = two)
(h1: ∀ i t : ℕ, i % two ≠ 0 → f t = i % two → f t.succ = (i.succ) % two)  (t: ℕ)
  (h : (∀ s, s ≤ t → f s < two))
  (h2: f t.succ = two):
  ∃ k, t = 0 + two * k := by {
    have : t % two = 0 := get_even' htwo h00 h0 h1 _ h h2
    exact get_equation (zero_le _) this
  }



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
        have : n ≤ v ∨ v < n := le_or_gt n v
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


theorem get_1st_two {two:ℕ}  {f:ℕ → ℕ}
  {u: ℕ}
  (hu : f u.succ = two) : ∃ t₀:ℕ, f t₀.succ = two ∧ ∀ v, f v.succ = two → t₀ ≤ v
  := least_number_principle _ (by {exists u})

theorem zero_of_mod (a n : ℕ) (hn: 1 ≤ n) (ha: a % n  = 0 ) (han: a < n) : a = 0 :=
  by {
    have : ∃ k, a = 0 + n * k := get_equation (zero_le _) ha
    rcases this with ⟨k,hk⟩
    cases k
    rw [hk]
    simp
    have : n < n := calc
      _ = 0 + n * 1 := by ring
      _ ≤ 0 + n * n_1.succ := by {field_simp;exact tsub_add_cancel_iff_le.mp rfl}
      _ = a := hk.symm
      _ < n := han
    exfalso
    exact LT.lt.false this
  }

theorem le_of_ne_two  {two:ℕ}
  -- to strengthen two_of_01' since the latter
  -- uses f s ≠ two instead of f s < 2 unfortunately
  (htwo: 1 < two)
  {f:ℕ → ℕ}
  (h00 : f 0 = 0)
  (h0: ∀ t, f t = 0 → f t.succ = 1 ∨ f t.succ = two)
  (h1: ∀ i t : ℕ, i % two ≠ 0 → f t = i % two → f t.succ = (i.succ) % two)  (t₀: ℕ)
  (ht₀ : (∀ s, s ≤ t₀ → f s ≠ two))
       :  ∀ s, s ≤ t₀ → f s < two := by {
    induction t₀
    intro s
    intro
    have : s = 0 := Nat.le_zero.mp a
    rw [this]
    rw [h00]
    exact Nat.zero_lt_of_lt htwo

    intro s hs
    cases hs

    let g := n_ih (by {
      intro s hsn
      exact ht₀ _ (Nat.le_step hsn)
    }) n (le_refl _)
    by_cases (f n = 0)
    let gg := h0 n h
    cases gg
    rw [h_1]
    exact htwo
    let ggg := ht₀ n.succ (le_refl _)
    exfalso
    exact ggg h_1

    let g1 := h1 (f n) n (by {
      contrapose h
      simp
      simp at h
      exact zero_of_mod (f n) (two) (Nat.one_le_iff_ne_zero.mpr (Nat.not_eq_zero_of_lt htwo)) h g
    }) (by {
      exact (Nat.mod_eq_of_lt g).symm
    })
    rw [g1]

    exact Nat.mod_lt _ (Nat.zero_lt_of_lt htwo)
    let g := n_ih (by {
      intro s hsn
      exact ht₀ _ (Nat.le_step hsn)
    }) s a
    exact g
  }


theorem two_of_01' {two:ℕ}
(htwo: 1 < two)
-- like two_of_01 but with two instead of 2
-- it uses f s ≠ two instead of f s < 2 unfortunately
   {f:ℕ → ℕ}
  (h00 : f 0 = 0)
  (h0: ∀ t, f t = 0 → f t.succ = 1 ∨ f t.succ = two)
  {u: ℕ}
  (hu : f u.succ = two) : ∃ t₀, (∀ s, s ≤ t₀ → f s ≠ two) ∧ f t₀.succ = two
  := by {
    have : ∃ t₀:ℕ, f t₀.succ = two ∧ ∀ v, f v.succ = two → t₀ ≤ v := get_1st_two hu
    rcases this with ⟨t₀, ht₀⟩
    exists t₀
    constructor
    intro s
    induction s
    intro
    rw [h00]
    exact Ne.symm (Nat.not_eq_zero_of_lt htwo)
    intro hn

    by_cases (f n = 0)
    let gg := h0 n h
    cases gg
    rw [h_1]
    exact Nat.ne_of_lt htwo
    exfalso
    have : t₀ ≤ n := ht₀.2 n h_1
    have : n.succ ≤ n := Nat.le_trans hn this
    exact Nat.le_lt_antisymm this (Nat.lt.base n)
    by_contra
    let gg := ht₀.2 n a
    exact Nat.le_lt_antisymm gg hn
    exact ht₀.1
  }

theorem two_of_01'' {two:ℕ}
  -- like two_of_01 but with two instead of 2
  (htwo: 1 < two)
   {f:ℕ → ℕ}
  (h00 : f 0 = 0)
  (h0: ∀ t, f t = 0 → f t.succ = 1 ∨ f t.succ = two)
  (h1: ∀ i t : ℕ, i % two ≠ 0 → f t = i % two → f t.succ = (i.succ) % two)
  {u: ℕ}
  (hu : f u.succ = two) : ∃ t₀, (∀ s, s ≤ t₀ → f s < two) ∧ f t₀.succ = two :=
  by {
    have : ∃ t₀, (∀ s, s ≤ t₀ → f s ≠ two) ∧ f t₀.succ = two := two_of_01' htwo h00 h0 hu
    rcases this with ⟨t₀,ht₀⟩
    exists t₀
    constructor
    exact le_of_ne_two htwo h00 h0 h1 _ ht₀.1
    exact ht₀.2
  }


theorem get_diophantine''  (f:ℕ → ℕ)
-- like get_diophantine' but with two and three instead of 2 and 3 [MAIN THEOREM]
  {two three : ℕ}
  (htwo : 1 < two)
  (h00 : f 0 = 0)
  (h0: ∀ t, f t = 0 → f t.succ = 1 ∨ f t.succ = two)
  (h1: ∀ i t : ℕ, i % two ≠ 0 → f t = i % two → f t.succ = (i.succ) % two)
  (h2s: ∀ i t, f t = two + (i%three) → f t.succ = two + (i.succ %three))
  (u: ℕ)
  (hu : f u.succ = two)
  : ∃ k₀ k₁, u.succ = k₀ * two + 1 + k₁ * three  := by {
    have : ∃ t₀, (∀ s, s ≤ t₀ → f s < two) ∧ f t₀.succ = two := two_of_01'' htwo h00 h0 h1 hu
    rcases this with ⟨t₀,ht₀⟩
    let h := ht₀.1
    let ht2 := ht₀.2
    have ht₀u : t₀ ≤ u := by {
      have : t₀ ≤ u ∨ u < t₀ := le_or_gt t₀ u
      cases this
      exact h_1
      exfalso
      have : two < two := Eq.trans_lt (id hu.symm) (h (Nat.succ u) h_1)
      exact LT.lt.false this
      }
    have : ∃ k, t₀ = 0 + two * k := get_mul_two' htwo h00 h0 h1 _ h ht2
    rcases this with ⟨k₀,hk₀⟩
    exists k₀
    have : ∃ k, u.succ = t₀.succ + three * k := get_multiple_three'' h2s ht2 hu ht₀u
    rcases this with ⟨k₁,hk₁⟩
    exists k₁
    rw [hk₁,hk₀,zero_add]
    linarith
  }

  theorem get_diophantine''' -- replace two by zero.succ.succ in order to synthesize 0 and 1 instances
    (zero three : ℕ)
  (F:ℕ → Fin ((zero+three).succ.succ))
  -- like get_diophantine'' but working with a Fin type
  (h00 : (λ k ↦ (F k).1) 0 = 0)
  (h0: ∀ t, (λ k ↦ (F k).1) t = 0 → (λ k ↦ (F k).1) t.succ = 1 ∨ (λ k ↦ (F k).1) t.succ = zero.succ.succ)
  (h1: ∀ i t : ℕ, i % zero.succ.succ ≠ 0 → (λ k ↦ (F k).1) t = i % zero.succ.succ → (λ k ↦ (F k).1) t.succ = (i.succ) % zero.succ.succ)
  (h2s: ∀ i t, (λ k ↦ (F k).1) t = zero.succ.succ + (i%three) → (λ k ↦ (F k).1) t.succ = zero.succ.succ + (i.succ %three))
  (u: ℕ)
  (hu : (λ k ↦ (F k).1) u.succ = zero.succ.succ)
  : ∃ k₀ k₁, u.succ = k₀ * zero.succ.succ + 1 + k₁ * three  :=
by {
  have htwo : 1 < zero.succ.succ := Nat.one_lt_succ_succ zero
  exact get_diophantine'' (λ k ↦ (F k).1) htwo h00 h0 h1 h2s _ hu
}


-- assume zero=0 and three=3 in the following
def mystep : Fin 5 → Set (Fin 5)
| 0 => {1,2}
| 1 => {0}
| 2 => {3}
| 3 => {4}
| 4 => {2}

def mystep' : Fin 5 → Fin 5
| 0 => 1
| 1 => 0
| 2 => 3
| 3 => 4
| 4 => 2


def myNFA : NFA (Fin 1) (Fin 5) := {
  step := λ q _ ↦ mystep q
  start := {0}
  accept := {2}
}
def walk_in_myNFA (f : ℕ → Fin 5)                     := f 0 ∈ myNFA.start ∧ ∀ k,         f k.succ ∈ myNFA.step (f k) 0
def fin_walk_in_myNFA {q:ℕ} (F : (Fin q.succ) → Fin 5) := F 0 ∈ myNFA.start ∧ ∀ k : Fin q, F (Fin.succ k) ∈ myNFA.step (F (Fin.castSucc k)) 0

def extender {q:ℕ} (F: Fin q.succ → Fin 5) (n : ℕ) : Fin 5 :=
by {
  induction n
  exact F 0
  by_cases (n_1 < q)
  exact F n_1.succ
  exact mystep' (n_ih )
}

def myF : Fin 4 → Fin 5
| 0 => 0
| 1 => 1
| 2 => 0
| 3 => 2


#eval extender myF 0
#eval extender myF 1
#eval extender myF 2
#eval extender myF 3
#eval extender myF 4
#eval extender myF 5
#eval extender myF 6
#eval extender myF 7

theorem extend_walk {q:ℕ}  (F: Fin q.succ → Fin 5) (hw : fin_walk_in_myNFA F) : walk_in_myNFA (extender F) := by {
  constructor
  unfold extender
  simp
  exact hw.1
  intro n_1
  by_cases (n_1 < q)
  have : extender F n_1.succ = F n_1.succ := if_pos h
  rw [this]
  unfold fin_walk_in_myNFA at hw
  let g := hw.2
  let N := (⟨n_1,h⟩ : Fin q)
  let g := hw.2 N

  -- simp at g
  -- unfold extender
  -- simp
  sorry
  sorry
  -- have : ({ val := n_1 + 1, isLt := (Nat.succ_lt_succ h) } : Fin q.succ) = (↑n_1 + 1) := sorry
  -- have : F { val := n_1 + 1, isLt := (Nat.succ_lt_succ h) } = F (↑n_1 + 1) := sorry
  -- rw [← this]
  -- have : NFA.step myNFA (F ↑n_1) 0 = NFA.step myNFA (Nat.rec (F 0) (fun n_1 n_ih ↦ if n_1 < q then F (↑n_1 + 1) else mystep' n_ih) n_1) 0
  --   := sorry
  -- rw [← this]
  -- rw [← Nat.succ_eq_add_one]
  -- sorry
  -- -- exact g
  -- -- have : NFA.step myNFA (Nat.rec (F 0) (fun n_1 n_ih ↦ if h : n_1 < q then F ↑(Nat.succ n_1) else mystep' n_ih) n_1) 0
  -- --      = NFA.step myNFA (Nat.rec (F 0) (fun n_1 n_ih ↦ F ↑(Nat.succ n_1)) n_1) 0 := sorry


  -- unfold extender
  -- have : extender F n_1.succ = mystep' (F n_1) := sorry --if_neg h
  -- sorry
}

theorem h00 (F : ℕ → Fin 5) (hw : walk_in_myNFA F) : (λ k ↦ (F k).1) 0 = 0 := by {
  have : F 0 = 0 := Set.eq_of_mem_singleton hw.1
  simp; rw [this]; simp
}

theorem h0 (F : ℕ → Fin 5) (hw : walk_in_myNFA F) :
  (∀ t, (λ k ↦ (F k).1) t = 0 → (λ k ↦ (F k).1) t.succ = 1 ∨ (λ k ↦ (F k).1) t.succ = 2)
:= by {
  intro t ht; let g := hw.2 t; have : F t = 0 := by {simp at ht;exact Fin.ext ht}
  rw [this] at g; cases g;left;simp;rw [h];exact rfl;right;simp;rw [h];exact rfl
}

theorem h1 (F : ℕ → Fin 5) (hw : walk_in_myNFA F) :
  (∀ i t : ℕ, i % 2 ≠ 0 → (λ k ↦ (F k).1) t = i % 2 → (λ k ↦ (F k).1) t.succ = (i.succ) % 2)
:= by {
  intro i t hi ht; have : i % 2 = 1 := Nat.mod_two_ne_zero.mp hi
  rw [this] at ht; have : i.succ % 2 = 0 := by {rw [Nat.succ_eq_add_one,Nat.add_mod,this];simp}
  rw [this]; let g := hw.2 t
  have : F t = 1 := Fin.ext ht
  rw [this] at g; simp; rw [Set.eq_of_mem_singleton g]; simp
}

theorem mod3_cases (i:ℕ) (hnz : ¬ i % 3 = 0) (h : ¬ i % 3 = 1) : i % 3 = 2 :=
by {
    by_contra
    rename ¬ i % 3 = 2 => hnt
    have : i % 3 < 2 ∨ i % 3 = 2 := Nat.lt_or_eq_of_le (Nat.lt_succ.mp (Nat.mod_lt _ (Nat.succ_pos 2)))
    cases this
    have : i % 3 < 1 ∨ i % 3 = 1 := Nat.lt_or_eq_of_le (Nat.lt_succ.mp h_1)
    cases this
    have : i % 3 = 0 := Nat.le_zero.mp (Nat.lt_succ.mp h_2)
    exact hnz this; exact h h_2; exact hnt h_1
  }

theorem h2s (F : ℕ → Fin 5) (hw : walk_in_myNFA F) :
  (∀ i t, (λ k ↦ (F k).1) t = 2 + (i%3) → (λ k ↦ (F k).1) t.succ = 2 + (i.succ %3))
:= by {
  intro i t hit
  by_cases (i%3 = 0)
  rename i % 3 = 0 => hz
  rw [hz] at hit
  simp at hit
  have : i.succ % 3 = 1 := by {
    rw [Nat.succ_eq_add_one,Nat.add_mod,hz];simp;
  }
  rw [this];simp; have : F t = 2 := Fin.ext hit
  rw [← Nat.succ_eq_add_one]; let g := hw.2 t; rw [this] at g; exact Fin.mk_eq_mk.mp g
  rename ¬ i % 3 = 0 => hnz; by_cases (i%3 = 1)
  rename i % 3 = 1 => ho; rw [ho] at hit; simp at hit; simp
  have : i.succ % 3 = 2 := by {
    rw [Nat.succ_eq_add_one,Nat.add_mod,ho];simp
  }
  rw [this]; have : F t = 3 := Fin.ext hit
  let g := hw.2 t; rw [this] at g; rw [Set.eq_of_mem_singleton g]; simp
  have : i % 3 = 2 := mod3_cases i hnz h; rw [this] at hit; rename i % 3 = 2 => hmt
  have : i.succ % 3 = 0 := by {
    rw [Nat.succ_eq_add_one,Nat.add_mod,hmt,];simp
  }
  rw [this]; simp; let g := hw.2 t; simp at hit
  have : F t = 4 := Fin.ext hit
  rw [this] at g; rw [Set.eq_of_mem_singleton g]; simp
}

theorem get_diophantine_NFA
  (F:ℕ → Fin 5) (hw : walk_in_myNFA F)
  -- A walk in myNFA that visits the state 2 must do so at a time of form 2k₀+1+3k₁
  (u: ℕ)
  (hu : (λ k ↦ (F k).1) u.succ = 2)
  : ∃ k₀ k₁, u.succ = k₀ * 2 + 1 + k₁ * 3  :=
by {
  have htwo : 1 < 2 := Nat.one_lt_succ_succ 0
  exact get_diophantine'' (λ k ↦ (F k).1) htwo (h00 _ hw) (h0 F hw) (h1 F hw) (h2s F hw) _ hu
}
