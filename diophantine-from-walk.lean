import Mathlib.Computability.NFA
import Mathlib.Data.Nat.Basic
import Mathlib.MeasureTheory.Constructions.Prod.Basic
import Std.Data.Nat.Lemmas

set_option tactic.hygienic false
set_option maxHeartbeats 10000000
/- Connect the diophantine equation 2x+3y=n with a walk in a digraph that has a cycle of length 2 followed by a cycle of length 3. -/
/- The numbers n₂ and n₃ are initially 2 and 3 but can be generalized. -/

-- rename tactics are useful while proving, but after the fact better to avoid
section general

theorem unique_iff_of_bijective {α β : Type}
{P:α → Prop} {Q:β → Prop}
{f:{a : α // P a}  → {b :β // Q b}}
(h : Function.Bijective f) :
(∃! a, P a) ↔ (∃! b, Q b) := by {
  constructor
  intro hQ
  rcases hQ with ⟨a,ha⟩
  exists f ⟨a,ha.1⟩
  constructor

  exact (f ⟨a,ha.1⟩).2

  intro b hQb
  let surj := h.2 ⟨b,hQb⟩
  rcases surj with ⟨a'pair,ha'pair⟩
  let a' := a'pair.1
  let heq := ha.2 a'pair a'pair.2

  have : a' = a'pair.1 := rfl
  rw [← this] at heq
  have hae: a'pair = ⟨a,ha.1⟩ := Subtype.coe_eq_of_eq_mk heq
  rw [hae] at ha'pair
  exact congr_arg (λ x ↦ x.1) ha'pair.symm

  intro hunique
  rcases hunique with ⟨b,hb⟩
  let surj := h.2 ⟨b,hb.1⟩
  rcases surj with ⟨apair,ha⟩
  exists apair
  constructor
  exact apair.2
  intro a' ha'
  let a'pair := (⟨a',ha'⟩ : { a // P a})
  have hqfa': Q (f a'pair) := by {
    exact (f a'pair).2
  }
  have h₁: f a'pair = b := by {
    exact hb.2 (f a'pair) hqfa'
  }
  have h₁': f a'pair = ⟨b,hb.1⟩ := Subtype.coe_eq_of_eq_mk h₁
  have h₃: f a'pair = f apair := Eq.trans h₁' ha.symm
  have : a'pair = apair := h.1 h₃
  exact congr_arg (λ x ↦ x.1) this
}

  def find_spec_le
    (Z : ℕ → Prop)  (u:ℕ) (hu: Z u) [DecidablePred Z] : {t₀ // Z t₀ ∧ ∀ v, Z v → t₀ ≤ v}
    := ⟨Nat.find (Exists.intro u hu),by {
      constructor
      exact Nat.find_spec _
      intro v hv
      exact Nat.find_le hv
    }⟩

  -- To eventually get uniqueness we want to turn ∃ results into functional results:
  theorem get_equation'' {a n : ℕ} (han : (a) % n = 0): {k // a = n * k} :=
  by {
    have : n ∣ a := Nat.modEq_zero_iff_dvd.mp han
    have : a / n * n = a := Nat.div_mul_cancel this
    rw [mul_comm] at this
    exact ⟨(a)/n,this.symm⟩
  }

  theorem get_equation' {a b n : ℕ} (hab: a ≤ b) (han : (b) % n = a % n): {k // b = a + n * k} :=
  by {
    have : (b - a) % n = 0 := Nat.sub_mod_eq_zero_of_mod_eq han
    have pair : {k // b-a = n*k} := get_equation'' this
    have : b-a = n*pair.1 := pair.2
    have : b = a + n * pair.1 := by {
      exact calc
      _ = (b-a) + a := Nat.eq_add_of_sub_eq hab rfl
      _ = (n*pair.1) + a := congr_arg (λ x ↦ x + a) pair.2
      _ = _ := Nat.add_comm _ _

    }
    exact ⟨pair.1, this⟩
  }


  theorem get_equation {a b n : ℕ} (hab: a ≤ b) (han : (b) % n = a % n): ∃ k, b = a + n * k
    := by {let pair := get_equation' hab han; exists pair.1; exact pair.2}

  theorem zero_of_mod {a n : ℕ} (hn: 1 ≤ n) (ha: a % n  = 0 ) (han: a < n) : a = 0
    := by {
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
  theorem mod3_cases {i:ℕ} (hnz : ¬ i % 3 = 0) (h : ¬ i % 3 = 1) : i % 3 = 2
    := by {
      by_contra hnt
      have : i % 3 < 2 ∨ i % 3 = 2 := Nat.lt_or_eq_of_le (Nat.lt_succ.mp (Nat.mod_lt _ (Nat.succ_pos 2)))
      cases this
      have : i % 3 < 1 ∨ i % 3 = 1 := Nat.lt_or_eq_of_le (Nat.lt_succ.mp h_1)
      cases this
      have : i % 3 = 0 := Nat.le_zero.mp (Nat.lt_succ.mp h_2)
      exact hnz this; exact h h_2; exact hnt h_1
    }
end general

-- Our running example will be C₂₃, the cursive NFA that has a cycle of length 2 and then a cycle of length 3.
def C₂₃_step : Fin 5 → Set (Fin 5)
| 0 => {1,2}
| 1 => {0}
| 2 => {3}
| 3 => {4}
| 4 => {2}

def C₂₃ : NFA (Fin 1) (Fin 5) := {
  step := λ q _ ↦ C₂₃_step q
  start := {0}
  accept := {2}
}

structure C₂₃ish (n₂ n₃ :ℕ) (f:ℕ → ℕ) where
 (h00 : f 0 = 0)
 (h0: ∀ t, f t = 0 → f t.succ = 1 ∨ f t.succ = n₂)
 (h1: ∀ i t : ℕ, i % n₂ ≠ 0 → f t = i % n₂ → f t.succ = (i.succ) % n₂)
 (h2s: ∀ i t, f t = n₂ + (i%n₃) → f t.succ = n₂ + (i.succ %n₃))

theorem walk_mod2 {n₂ n₃:ℕ}(hn₂: 1 < n₂){f:ℕ → ℕ}(ish : C₂₃ish n₂ n₃ f)(t: ℕ) (hs : ∀ s, s ≤ t → f s < n₂) : f t = t % n₂
  := by {
  induction t
  rw [ish.h00]
  rfl
  have hfn : f n = n % n₂ := n_ih (λ s hsn ↦ hs s (Nat.le_step hsn))
  by_cases (n % n₂ = 0)
  rw [h] at hfn
  let g := ish.h0 n hfn
  cases g
  rw [h_1]
  have : (n+1) % n₂ = (n % n₂ + 1 % n₂) % n₂ := Nat.add_mod _ _ _
  rw [h,zero_add,Nat.mod_mod] at this
  have ht: 1 % n₂ = 1 := Nat.mod_eq_of_lt hn₂
  rw [ht] at this
  exact this.symm

  rw [h_1]
  exfalso
  let gg := hs n.succ (le_refl _)
  have : n₂ < n₂ := Eq.trans_lt (id h_1.symm) gg
  exact LT.lt.false this
  let g := ish.h1 n n h hfn
  exact g
 }

theorem get_even {n₂ n₃:ℕ}(hn₂: 1 < n₂){f:ℕ → ℕ}(ish : C₂₃ish n₂ n₃ f)(t: ℕ) (h : (∀ s, s ≤ t → f s < n₂)) (h2: f t.succ = n₂): t % n₂ = 0
  := by {
  have ftt : f t = t % n₂ := walk_mod2 hn₂ ish (by {
    exact t
  }) h
  by_contra hcontra
  let g := ish.h1 t t hcontra ftt
  have ht1: t.succ % n₂ = n₂ := Eq.trans g.symm h2
  have ht2: t.succ % n₂ < n₂ := Nat.mod_lt _ (Nat.zero_lt_of_lt hn₂)
  have : n₂ < n₂ := Eq.trans_lt ht1.symm ht2
  exact LT.lt.false this
 }


theorem strengthen {n₂ n₃ t₀:ℕ} (hn₂: 1 < n₂) {f:ℕ → ℕ} (ish : C₂₃ish n₂ n₃ f) (ht₀ : (∀ s, s ≤ t₀ → f s ≠ n₂)) :  ∀ s, s ≤ t₀ → f s < n₂
  := by {
  -- to strengthen n₂_of_01' since the latter
  -- uses f s ≠ n₂ instead of f s < 2 unfortunately
    induction t₀
    intro s
    intro
    have : s = 0 := Nat.le_zero.mp a
    rw [this]
    rw [ish.h00]
    exact Nat.zero_lt_of_lt hn₂

    intro s hs
    cases hs

    let g := n_ih (by {
      intro s hsn
      exact ht₀ _ (Nat.le_step hsn)
    }) n (le_refl _)
    by_cases (f n = 0)
    let gg := ish.h0 n h
    cases gg
    rw [h_1]
    exact hn₂
    let ggg := ht₀ n.succ (le_refl _)
    exfalso
    exact ggg h_1

    let g1 := ish.h1 (f n) n (by {
      contrapose h
      simp
      simp at h
      exact zero_of_mod (Nat.one_le_iff_ne_zero.mpr (Nat.not_eq_zero_of_lt hn₂)) h g
    }) (by {
      exact (Nat.mod_eq_of_lt g).symm
    })
    rw [g1]

    exact Nat.mod_lt _ (Nat.zero_lt_of_lt hn₂)
    let g := n_ih (by {
      intro s hsn
      exact ht₀ _ (Nat.le_step hsn)
    }) s a
    exact g
  }

def walk_in_C₂₃ (f : ℕ → Fin 5)                     := f 0 ∈ C₂₃.start ∧ ∀ k,         f k.succ ∈ C₂₃.step (f k) 0

theorem getish (F:ℕ → Fin 5) (hw : walk_in_C₂₃ F) : C₂₃ish 2 3 (λ n ↦ (F n).1)
  := {
    h00 := by {
      have : F 0 = 0 := Set.eq_of_mem_singleton hw.1
      rw [this]; simp
    }
    h0 := by {
      intro t ht; let g := hw.2 t; have : F t = 0 := by {
        exact Fin.ext ht
      }
      rw [this] at g; cases g;left;rw [h];exact rfl;right;rw [h];exact rfl
    }
    h1 := by {
      intro i t hi ht; have : i % 2 = 1 := Nat.mod_two_ne_zero.mp hi
      rw [this] at ht; have : i.succ % 2 = 0 := by {rw [Nat.succ_eq_add_one,Nat.add_mod,this];simp}
      rw [this]; let g := hw.2 t
      have : F t = 1 := Fin.ext ht
      rw [this] at g; rw [Set.eq_of_mem_singleton g]; simp
    }
    h2s := by {
      intro i t hit
      by_cases hz : (i%3 = 0)
      rw [hz] at hit
      simp at hit
      have : i.succ % 3 = 1 := by {
        rw [Nat.succ_eq_add_one,Nat.add_mod,hz];simp;
      }
      rw [this];have : F t = 2 := Fin.ext hit
      rw [← Nat.succ_eq_add_one]; let g := hw.2 t; rw [this] at g; exact Fin.mk_eq_mk.mp g
      by_cases ho : (i%3 = 1)
      rw [ho] at hit;
      have : i.succ % 3 = 2 := by {
        rw [Nat.succ_eq_add_one,Nat.add_mod,ho];simp
      }
      rw [this]; have : F t = 3 := Fin.ext hit
      let g := hw.2 t; rw [this] at g; rw [Set.eq_of_mem_singleton g]; simp
      have hmt : i % 3 = 2 := mod3_cases hz ho; rw [hmt] at hit;
      have : i.succ % 3 = 0 := by {
        rw [Nat.succ_eq_add_one,Nat.add_mod,hmt,];simp
      }
      rw [this]; simp; let g := hw.2 t;
      have : F t = 4 := Fin.ext hit
      rw [this] at g; rw [Set.eq_of_mem_singleton g]; simp
    }
  }

def walk_ (k:ℕ) (i: ℕ) : Fin 5 :=
ite (i ≥ (2*k).succ)
  (by {
    let u := (i-(2*k).succ) % 3 -- to avoid % casting to Fin 5 too soon
    exact (2 + u)
  })
  (((i % 2): ℕ): Fin 5) -- to avoid % casting to Fin 5 too soon :)

theorem walk__injective' {k₁ k₂ : ℕ} (hk : k₁ < k₂) : walk_ k₁ ≠ walk_ k₂ := by {
  intro hcontra
  have : ∀ n, walk_ k₁ n = walk_ k₂ n := fun n ↦ congrFun hcontra n
  let g := this (2*k₁).succ
  unfold walk_ at g
  simp at g
  have h₀: ¬ (k₂) ≤ (k₁) := Nat.not_le.mpr hk
  have : ¬ (2 * k₂) ≤ (2 * k₁) := by {
    intro hcontra
    have : k₂ ≤ k₁ := Nat.le_of_mul_le_mul_left hcontra (Nat.succ_pos 1)
    exact h₀ this
  }
  have : ¬ Nat.succ (2 * k₂) ≤ Nat.succ (2 * k₁) := by {
    intro hcontra
    exact this (Nat.succ_le_succ_iff.mp hcontra)
  }
  rw [if_neg this] at g
  have : ∀ x : ℕ, x % 2 < 2 := by {intro x;exact Nat.mod_lt _ (Nat.succ_pos 1)}

  have : (2*k₁).succ % 2 = 0 ∨ (2*k₁).succ % 2 = 1
    := Nat.mod_two_eq_zero_or_one (Nat.succ (2 * k₁))
  cases this
  rw [h] at g
  have : 0 = 2 := Fin.mk_eq_mk.mp (id g.symm)
  have : 0 = Nat.succ 1 := this
  exact Nat.succ_ne_zero 1 this.symm

  rw [h] at g
  have : 1 = 2 := Fin.mk_eq_mk.mp (id g.symm)
  have : 1 = Nat.succ 1 := this
  exact Nat.succ_ne_self 1 this.symm

}

theorem keep_arriving (k l : ℕ) : walk_ k (2*k + 1 + 3*l) = 2 :=
  by {
    induction l
    simp
    unfold walk_
    rw [if_pos _]
    simp
    exact Nat.le_refl (Nat.succ (2 * k))

    unfold walk_
    rw [if_pos _]
    simp
    exact Nat.le_add_right (Nat.succ (2 * k)) (3 * Nat.succ _)
  }

theorem unique_walk_C₂₃_helper {w : ℕ → Fin 5} (hw: walk_in_C₂₃ w) (k : ℕ) (hwk: w (2*k).succ = 2 ∧ ∀ n < (2*k).succ, w n ≠ 2)
  : ∀ n < (2*k).succ, w n < 2 := by {
  intro n
  induction n
  intro; rw [hw.1]; exact Fin.coe_sub_iff_lt.mp rfl

  intro hn_1
  by_cases (n_1 < (2*k).succ)
  have : w n_1 ≤ 1 := Fin.succ_le_succ_iff.mp (n_ih h)
  have : w n_1 < 1 ∨ w n_1 = 1 := lt_or_eq_of_le this
  cases' this with h_1'
  have : w n_1 ≤ 0 := Fin.succ_le_succ_iff.mp h_1'
  have h_1 : w n_1 = 0 := Fin.le_zero_iff.mp this
  let g₀ := hwk.2 n_1.succ hn_1
  let g₁ := hw.2 n_1
  rw [h_1] at g₁
  cases g₁
  rw [h_2]
  exact Fin.coe_sub_iff_lt.mp rfl
  exfalso
  exact g₀ h_2
  let g₁ := hw.2 n_1
  rw [h_1] at g₁
  rw [g₁]
  exact Fin.coe_sub_iff_lt.mp rfl
  exfalso
  have : n_1 < (2*k).succ := Nat.lt_of_succ_lt hn_1
  exact h this
  }

theorem unique_walk_C₂₃ {w : ℕ → Fin 5} (hw: walk_in_C₂₃ w) {k : ℕ} (hwk': w (2*k).succ = 2 ∧ ∀ n < (2*k).succ, w n ≠ 2) :
  w = walk_ k :=
  by {
  have hwk : w (2*k).succ = 2 ∧ ∀ n < (2*k).succ, w n < 2 :=
    by {
      constructor
      exact hwk'.1
      exact (unique_walk_C₂₃_helper hw _ hwk')
    }
  apply funext; intro x; induction x
  unfold walk_in_C₂₃ at hw; unfold walk_
  rw [if_neg _]; simp; exact hw.1

  intro hcontra; simp at hcontra

  by_cases hnk : (n.succ ≥ (2*k).succ)
  unfold walk_
  rw [if_pos _]
  simp
  let g := hw.2 n
  rw [n_ih] at g
  unfold walk_ at g
  by_cases hnks : (n ≥ (2*k).succ )

  have h₂: n ≥ 2*k := Nat.lt_succ.mp hnk
  have h₃: n - 2*k ≥ 1 := (le_tsub_iff_left h₂).mpr hnks
  have h₄: n - (2*k).succ + 1 = n - 2*k := by {rw [Nat.sub_succ']; exact Nat.sub_add_cancel h₃}

  rw [if_pos hnks] at g; simp at g; by_cases hnz : ((n - (2*k).succ) % 3 = 0)
  rw [hnz] at g; simp at g; rw [g]
  rw [← h₄,Nat.add_mod,hnz]; simp
  by_cases hno : ((n - (2*k).succ) % 3 = 1)

  rw [← h₄,Nat.add_mod,hno];
  rw [hno] at g; simp at g; rw [g]; simp
  have hns : (n - Nat.succ (2 * k)) % 3 = 2 := mod3_cases hnz hno
  have : (n - (2 * k)) % 3 = 0 := by {rw [← h₄,Nat.add_mod,hns,];simp}
  rw [this]; simp; rw [hns] at g; simp at g; exact g
  have hn2k: n = 2*k := (Nat.eq_of_lt_succ_of_not_lt hnk hnks).symm
  rw [hn2k]; simp; rw [if_neg hnks] at g
  have : 2 ∣ n := Dvd.intro k (id hn2k.symm)
  have : n % 2 = 0 := Nat.mod_eq_zero_of_dvd this
  rw [this] at g
  cases g; exact hwk.1

  rw [hn2k] at h
  exact h; exact hnk
  unfold walk_
  rw [if_neg hnk]
  unfold walk_ at n_ih

  have hnss : n.succ < (2*k).succ := Nat.not_le.mp hnk
  have hnlt : n < (2*k).succ := Nat.lt_of_succ_lt hnss
  have hn2k : ¬ n ≥ (2*k).succ := by {
    intro hcontra
    have : n < n := Nat.lt_of_lt_of_le hnlt hcontra
    exact LT.lt.false this
  }

  rw [if_neg hn2k] at n_ih
  unfold walk_in_C₂₃ at hw
  let g₂ := hw.2 n
  rw [n_ih] at g₂
  cases (Nat.mod_two_eq_zero_or_one n)
  rw [h] at g₂
  simp at g₂
  have : n.succ % 2 = 1 := by {
    rw [Nat.succ_eq_add_one,Nat.add_mod,h,]
    simp
  }
  rw [this]
  simp
  cases g₂
  exact h_1
  exfalso
  let g₂ := hwk.2 n.succ hnss
  rw [h_1] at g₂
  exact LT.lt.false g₂
  have : n.succ % 2 = 0 := by {rw [Nat.succ_eq_add_one,Nat.add_mod,h,];simp}
  rw [this]; simp
  rw [h] at g₂; exact g₂
}

theorem ne_of_le {w : ℕ → Fin 5}
  {t₀:ℕ}
  (hw: walk_in_C₂₃ w)
  (ht₀ : w (Nat.succ t₀) = 2 ∧ ∀ (v : ℕ), w (Nat.succ v) = 2 → t₀ ≤ v)
  : ∀ (s : ℕ), s ≤ t₀ → (w s).1 ≠ 2
  := by {
      intro s hs
      cases s
      intro hcontra
      let gg := hw.1
      simp at gg
      rw [gg] at hcontra
      exact Nat.succ_ne_zero 1 hcontra.symm
      intro hcontra
      let g := ht₀.2 n (Fin.eq_of_veq hcontra)
      have : n < n := Nat.succ_le.mp (le_trans hs g)
      exact LT.lt.false this
    }

theorem ne_first {w : ℕ → Fin 5} {t₀ k:ℕ} (hk: t₀ = 2 * k) (hw: walk_in_C₂₃ w)
  (ht₀ : w (Nat.succ t₀) = 2 ∧ ∀ (v : ℕ), w (Nat.succ v) = 2 → t₀ ≤ v)
  :w (2*k).succ = 2 ∧ ∀ n, n < (2*k).succ → w n ≠ 2 :=
    by {
      constructor; rw [hk] at ht₀; exact ht₀.1

      intro u hu hu2; cases u
      let g := hw.1
      rw [hu2] at g
      exact Nat.succ_ne_zero 1 (Fin.mk_eq_mk.mp g)

      have : 2*k < 2*k := calc
        _ = t₀  := id hk.symm
        _ ≤ n   := ht₀.2 n hu2
        _ < 2*k := Nat.succ_lt_succ_iff.mp hu
      exact LT.lt.false this
    }

noncomputable def getk1 {w : ℕ → Fin 5} {u:ℕ} (hw: walk_in_C₂₃ w) (hu: w (Nat.succ u) = 2) : ℕ
  := by {
    let t₀ := (find_spec_le (λ s ↦ w (Nat.succ s) = 2) u hu).1
    let ht₀ := (find_spec_le (λ s ↦ w (Nat.succ s) = 2) u hu).2
    have h2 : ((w (Nat.succ t₀))).1 = 2 := by {
      exact Fin.mk_eq_mk.mp ht₀.1
    }
    let ish := getish w hw
    have hlt :  ∀ (s : ℕ), s ≤ t₀ → (w s).1 < 2 := by {
      intro _ hs
      exact strengthen (Nat.lt_succ_self _) ish (ne_of_le hw ht₀) _ hs
    }
    have h02 : t₀ % 2 = 0 % 2 := get_even (Nat.lt_succ_self _) ish _ hlt h2
    let k := (get_equation' (Nat.zero_le _) h02).1
    exact k
  }

theorem getk2 {w : ℕ → Fin 5} {u:ℕ} (hw: walk_in_C₂₃ w) (hu: w (Nat.succ u) = 2): w = walk_ (getk1 hw hu)
  := by {
    let t₀ := (find_spec_le (λ s ↦ w (Nat.succ s) = 2) u hu).1
    let ht₀ := (find_spec_le (λ s ↦ w (Nat.succ s) = 2) u hu).2
    have h2 : ((w (Nat.succ t₀))).1 = 2 := by {
      exact Fin.mk_eq_mk.mp ht₀.1
    }
    let ish := getish w hw
    have hlt :  ∀ (s : ℕ), s ≤ t₀ → (w s).1 < 2 := by {
      intro _ hs
      exact strengthen (Nat.lt_succ_self _) ish (ne_of_le hw ht₀) _ hs
    }
    have h02 : t₀ % 2 = 0 % 2 := get_even (Nat.lt_succ_self _) ish _ hlt h2
    let hk := (get_equation' (Nat.zero_le _) h02).2

    rw [zero_add] at hk
    exact unique_walk_C₂₃ hw (ne_first hk hw ht₀)
  }

theorem l_unique {k l₁ l₂ : ℕ} (he: 2*k + 1 + 3*l₁ = 2*k + 1 + 3*l₂) : l₁=l₂
  := by {
    have :  3 * l₁ = 3 * l₂ := Nat.add_left_cancel he
    exact Nat.eq_of_mul_eq_mul_left (Nat.succ_pos 2) this
  }

def functional_eq_add_of_le  {m n : ℕ} (h : m ≤ n) : {k // n = m + k}
  := by {
    have property : n = m + (n - m) := (Nat.add_sub_of_le h).symm
    exact ⟨n-m,property⟩
  }

theorem getl {k n:ℕ} (hmod₀: walk_ k n = 2) :  {l : ℕ // n = 2*k + 1 + 3*l}
  := by {
    have hge : n ≥ 2*k + 1 := by {
      unfold walk_ at hmod₀
      by_contra hcontra
      rw [if_neg hcontra] at hmod₀
      have : n%2 = 0 ∨ n%2 = 1 := Nat.mod_two_eq_zero_or_one n
      cases this
      rw [h] at hmod₀
      have : 0 = 2 := Fin.mk_eq_mk.mp hmod₀
      exact (Nat.succ_ne_zero _).symm this
      rw [h] at hmod₀
      have : 1 = 2 := Fin.mk_eq_mk.mp hmod₀
      exact Nat.succ_ne_self 1 this.symm
    }
    let L := n - (2*k+1)
    have hL : n = 2*k + 1 + L := (functional_eq_add_of_le hge).2
    rw [hL] at hmod₀
    unfold walk_ at hmod₀
    simp at hmod₀
    have : L = n - (2*k+1) := rfl
    rw [← this] at hmod₀
    have hmod : L % 3 = 0 := by {
      by_cases hz : (L % 3 = 0)
      exact hz

      by_cases (L % 3 = 1)
      rw [h] at hmod₀; exfalso; simp at hmod₀
      have : L % 3 = 2 := mod3_cases hz h
      rw [this] at hmod₀
      exfalso
      simp at hmod₀
    }
    have h₁: (L/3)*3 = L := Nat.div_mul_cancel (Nat.modEq_zero_iff_dvd.mp hmod)
    have h₂: L = 3 * (L / 3) := by {
      rw [mul_comm] at h₁
      exact h₁.symm
    }
    let l := L / 3
    have : n = 2 * k + 1 + 3 * l := by {
      rw [← h₂]
      exact hL
    }
    exact ⟨l,this⟩
  }

theorem walk_walks (k:ℕ) : walk_in_C₂₃ (walk_ k) :=
  by {
    constructor
    unfold walk_
    have : ¬ 0 ≥ Nat.succ (2 * k) := of_decide_eq_false rfl
    rw [if_neg this]
    exact rfl
    intro k_1; induction k_1; unfold walk_
    have : ¬ Nat.zero ≥ Nat.succ (2 * k) := of_decide_eq_false rfl
    rw [if_neg this]
    by_cases (k=0)
    have : Nat.succ Nat.zero ≥ Nat.succ (2 * k)
      := Nat.succ_le_succ (Nat.le_zero.mpr (mul_eq_zero_of_right 2 h))
    rw [if_pos this,h]
    right
    exact rfl
    have h₁: ¬ Nat.zero = (2 * k) := by {
      intro hcontra
      cases Nat.zero_eq_mul.mp hcontra
      exact Nat.succ_ne_zero 1 h_1; exact h h_1
    }
    have h₂: ¬ Nat.zero ≥ (2 * k) := by {
      intro hcontra
      exact h₁ (id (Nat.le_zero.mp hcontra).symm)
    }
    have : ¬ Nat.succ Nat.zero ≥ Nat.succ (2 * k) := by {
      intro hcontra
      exact h₂ (Nat.lt_succ.mp hcontra)
    }
    rw [if_neg this]; left; rfl
    unfold walk_
    by_cases hss : (Nat.succ (Nat.succ n) ≥ Nat.succ (2 * k))
    rw [if_pos hss]
    by_cases hnk : (Nat.succ n ≥ Nat.succ (2 * k))
    rw [if_pos hnk]
    simp
    have h₁ : n ≥ 2*k := Nat.succ_le_succ_iff.mp hnk
    have h₂ : n + 1 - 2*k = n - 2*k + 1 := Nat.sub_add_comm h₁

    by_cases hnz : (((n - 2 * k) % 3) = 0)
    rw [hnz,h₂,Nat.add_mod,hnz]
    exact rfl
    by_cases hno : (((n - 2 * k) % 3) = 1)
    rw [h₂,Nat.add_mod,hno]; exact rfl
    have h₁: ((n - 2 * k) % 3) = 2 := mod3_cases hnz hno
    have h₂: ((n + 1 - 2 * k) % 3) = 0 := by {
      rw [h₂,Nat.add_mod,h₁]
      simp
    }
    rw [h₁,h₂]; exact rfl
    rw [if_neg hnk]; simp
    have h₅ : n.succ = 2*k := (Nat.eq_of_lt_succ_of_not_lt hss hnk).symm
    have h₃: n+1 - 2*k = 0 := tsub_eq_of_eq_add_rev h₅
    rw [h₃,h₅]; simp; right; exact rfl
    -- early times:
    rw [if_neg hss]
    have : ¬ Nat.succ n ≥ Nat.succ (2 * k) := by {
      intro hcontra
      have : n.succ ≤ n.succ.succ := Nat.le_succ (Nat.succ n)
      exact hss (le_trans hcontra this)
    }
    rw [if_neg this]
    by_cases (n.succ % 2 = 0)
    rw [h]; simp
    have : n.succ.succ % 2 = 1 := by {
      rw [Nat.succ_eq_add_one,Nat.add_mod,h,];simp
    }
    rw [this]; simp; left; exact rfl
    have : n.succ % 2 = 1 := Nat.mod_two_ne_zero.mp h
    rw [this]
    have : n.succ.succ % 2 = 0 := by {
      rw [Nat.succ_eq_add_one,Nat.add_mod,this,];simp
    }
    rw [this]; exact rfl
  }

theorem walk__injective (k₁ k₂ : ℕ) (he : walk_ k₁ = walk_ k₂) : k₁ = k₂ :=
  by {
    contrapose he
    have : k₁ < k₂ ∨ k₂ < k₁ := Ne.lt_or_lt he
    cases this; exact walk__injective' h; exact (walk__injective' h).symm
  }

def walk_of_solution (T:ℕ)
  : {p : ℕ×ℕ // T.succ = 2 * p.1 + 1 + 3 * p.2} → {w : ℕ → Fin 5 // walk_in_C₂₃ w ∧ w T.succ = 2}
  := by {
    intro p; let k := p.1.1
    exists walk_ k; constructor; exact walk_walks k; rw [p.2]; exact keep_arriving _ _
  }

theorem walk_of_solution_injective (T:ℕ) :
Function.Injective (λ p ↦ walk_of_solution T p) := by {
  unfold Function.Injective
  intro p₁ p₂ hp
  unfold walk_of_solution at hp
  simp at hp
  have h₁₁: p₁.1.1 = p₂.1.1 := walk__injective p₁.1.1 p₂.1.1 hp
  have h₁₂: p₁.1.2 = p₂.1.2 := l_unique (Eq.trans p₁.2.symm (by {rw [h₁₁]; exact p₂.2}))
  exact SetCoe.ext (Prod.ext h₁₁ h₁₂)
}

theorem walk_of_solution_surjective (T:ℕ) :
Function.Surjective (λ p ↦ walk_of_solution T p) := by {
  unfold Function.Surjective
  intro wpair
  let ⟨hw,hT⟩ := wpair.2; let k := getk1 hw hT
  have hwp : wpair.1 = walk_ k := getk2 _ _
  rw [hwp] at hT
  rename wpair.1 (Nat.succ T) = 2 => hTold
  let lpair := (getl hT); let l := lpair.1
  exists ⟨(k,l), lpair.2⟩; exact SetCoe.ext (id hwp.symm)
}

theorem walk_of_solution_bijective (T:ℕ) :
Function.Bijective (λ p ↦ walk_of_solution T p) := by {
  constructor; exact walk_of_solution_injective _; exact walk_of_solution_surjective _
}

theorem main {T:ℕ} : (∃! p : ℕ×ℕ, T.succ = 2 * p.1 + 1 + 3 * p.2) ↔ (∃! w, walk_in_C₂₃ w ∧ w T.succ = 2)
  := unique_iff_of_bijective (walk_of_solution_bijective T)
