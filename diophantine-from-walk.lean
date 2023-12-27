import Mathlib.Computability.NFA
import Mathlib.Data.Nat.Basic
import Mathlib.MeasureTheory.Constructions.Prod.Basic
import Std.Data.Nat.Lemmas

set_option tactic.hygienic false
-- set_option maxHeartbeats 10000000
/-
Connect the diophantine equation a₀x+a₁y=n with
a walk in a digraph that has a cycle of length a₀ followed by a cycle of length a₁.
-/

def c₀ : ℕ := 10
def c₁ : ℕ := 15 -- c₀ and c₁ can be anything, try it! December 27, 2023.
def a₀ : ℕ := c₀.succ
def a₁ : ℕ := c₁.succ

theorem ha₀pos : 0 < a₀ := Nat.zero_lt_succ _

-- Our running example will be the "cursive" NFA that has a cycle of length a₀ and then a cycle of length a₁.
-- We implement it as an infinite NFA where only the first a₀+a₁ states are reachable,
-- in order to avoid type casting issues.
def cursive_step : ℕ → Set (ℕ) :=
λ q ↦ ite (q=0)
  {1,a₀}
  (ite (q<a₀)
    {(q+1) % a₀}
    {((a₀ + (((q-a₀+1) % a₁))):ℕ)}
  )

def cursive : NFA (Fin 1) (ℕ) := {
  step := λ q _ ↦ cursive_step q
  start := {0}
  accept := {a₀}
}

-- Some properties of walks in cursive NFAs:
structure cursiveish (a₀ a₁ :ℕ) (f:ℕ → ℕ) where
 (h00 : f 0 = 0)
 (h0: ∀ t, f t = 0 → f t.succ = 1 ∨ f t.succ = a₀)
 (h1: ∀ i t : ℕ, i % a₀ ≠ 0 → f t = i % a₀ → f t.succ = (i.succ) % a₀)
 (h2s: ∀ i t, f t = a₀ + (i%a₁) → f t.succ = a₀ + (i.succ %a₁))

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
  have h₁: f a'pair = b     := hb.2 (f a'pair) (f a'pair).2
  have h₁': f a'pair = ⟨b,hb.1⟩ := Subtype.coe_eq_of_eq_mk h₁
  have h₃: f a'pair = f apair := Eq.trans h₁' ha.symm
  exact congr_arg (λ x ↦ x.1) (h.1 h₃)
}

  def find_spec_le
    (Z : ℕ → Prop)  (u:ℕ) (hu: Z u) [DecidablePred Z] : {t₀ // Z t₀ ∧ ∀ v, Z v → t₀ ≤ v}
    := ⟨Nat.find (Exists.intro u hu),by {
      constructor
      exact Nat.find_spec _
      intro v hv
      exact Nat.find_le hv
    }⟩

  -- To get uniqueness we turn ∃ results into functional results:
  def get_equation'' {a n : ℕ} (han : (a) % n = 0): {k // a = n * k} :=
  by {
    have : n ∣ a := Nat.modEq_zero_iff_dvd.mp han
    have : a / n * n = a := Nat.div_mul_cancel this
    rw [mul_comm] at this
    exact ⟨(a)/n,this.symm⟩
  }

  def get_equation' {a b n : ℕ} (hab: a ≤ b) (han : (b) % n = a % n): {k // b = a + n * k} :=
  by {
    have : (b - a) % n = 0 := Nat.sub_mod_eq_zero_of_mod_eq han
    have pair : {k // b-a = n*k} := get_equation'' this
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


end general


theorem walk_mod_a₀ {f:ℕ → ℕ}(ish : cursiveish a₀ a₁ f)(t: ℕ)
(hs : ∀ s, s ≤ t → f s < a₀) : f t = t % a₀
  := by {
  induction t
  rw [ish.h00]
  rfl
  have hfn : f n = n % a₀ := n_ih (λ s hsn ↦ hs s (Nat.le_step hsn))
  by_cases hna : (n % a₀ = 0)
  rw [hna] at hfn
  let g := ish.h0 n hfn
  cases g
  rename f n.succ = 1 => cg
  rw [cg]
  have : (n+1) % a₀ = (n % a₀ + 1 % a₀) % a₀ := Nat.add_mod _ _ _
  rw [hna,zero_add,Nat.mod_mod] at this

  by_cases (1 < a₀)
  have ht: 1 % a₀ = 1 := Nat.mod_eq_of_lt h
  rw [ht] at this
  exact this.symm
  have : a₀ ≤ 1 := by exact Nat.not_lt.mp h
  have : a₀ < 1 ∨ a₀ = 1 := by exact Nat.lt_or_eq_of_le this
  cases this

  have ha₀0: a₀ = 0 := by exact Nat.lt_one_iff.mp h_1

  rw [ha₀0] at hna
  have : n=0 := by exact Nat.modEq_zero_iff.mp hna
  rw [this]
  rw [ha₀0]
  rfl
  rw [h_1]
  rw [Nat.mod_one]
  exfalso

  let G := hs n.succ (le_refl _)
  rw [h_1] at G
  have : 1 < 1 := by exact Eq.trans_lt (id cg.symm) G
  exact LT.lt.false this

  rw [h]
  exfalso
  let gg := hs n.succ (le_refl _)
  have : a₀ < a₀ := Eq.trans_lt (id h.symm) gg
  exact LT.lt.false this
  let g := ish.h1 n n hna hfn
  exact g
 }

theorem get_a₀dvd {f:ℕ → ℕ}(ish : cursiveish a₀ a₁ f)(t: ℕ)
(h : (∀ s, s ≤ t → f s < a₀)) (h2: f t.succ = a₀): t % a₀ = 0
  := by {
  have ftt : f t = t % a₀ := walk_mod_a₀ ish (by {
    exact t
  }) h
  by_contra hcontra
  let g := ish.h1 t t hcontra ftt
  have ht1: t.succ % a₀ = a₀ := Eq.trans g.symm h2
  have ht2: t.succ % a₀ < a₀ := Nat.mod_lt _ ha₀pos
  have : a₀ < a₀ := Eq.trans_lt ht1.symm ht2
  exact LT.lt.false this
 }


theorem strengthen {t₀:ℕ} {f:ℕ → ℕ}
  (ish : cursiveish a₀ a₁ f) (ht₀ : (∀ s, s ≤ t₀ → f s ≠ a₀)) :  ∀ s, s ≤ t₀ → f s < a₀
  := by {
    induction t₀
    intro s
    intro
    have : s = 0 := Nat.le_zero.mp a
    rw [this]
    rw [ish.h00]
    exact ha₀pos

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

    let G := ht₀ n.succ (le_refl _)
    rw [h_1] at G
    by_contra hcontra
    have : a₀ ≤ 1 := by exact Nat.not_lt.mp hcontra
    have : a₀ < 1 ∨ a₀ = 1 := by exact Nat.lt_or_eq_of_le this
    cases this
    have : a₀ ≤ 0 := by exact Nat.lt_succ.mp h_2
    have : 0 < a₀ := ha₀pos
    exact Nat.le_lt_antisymm this h_2
    exact G h_2.symm

    let ggg := ht₀ n.succ (le_refl _)
    exfalso
    exact ggg h_1

    let g1 := ish.h1 (f n) n (by {
      contrapose h
      simp
      simp at h
      exact zero_of_mod (Nat.one_le_iff_ne_zero.mpr (Nat.not_eq_zero_of_lt ha₀pos)) h g
    }) (by {
      exact (Nat.mod_eq_of_lt g).symm
    })
    rw [g1]

    exact Nat.mod_lt _ (ha₀pos)
    let g := n_ih (by {
      intro s hsn
      exact ht₀ _ (Nat.le_step hsn)
    }) s a
    exact g
  }

def walk_in_cursive (f : ℕ → ℕ) := f 0 ∈ cursive.start ∧ ∀ k, f k.succ ∈ cursive.step (f k) 0


theorem generalh2s (F: ℕ → ℕ)
(hw: walk_in_cursive F)
: ∀ (i t : ℕ), (F t) = a₀ + i % a₁ → (F (Nat.succ t)) = a₀ + Nat.succ i % a₁
:= by {
  intro i t hit
  let g := hw.2 t
  unfold walk_in_cursive at g
  rw [hit] at g
  unfold cursive at g
  unfold cursive_step at g
  simp at g
  rw [g]
}

theorem getish (F:ℕ → ℕ) (hw : walk_in_cursive F) : cursiveish a₀ a₁ (λ n ↦ (F n))
  := {
    h00 := by {
      have : F 0 = 0 := Set.eq_of_mem_singleton hw.1
      rw [this];
    }
    h0 := by {
      intro t ht; let g := hw.2 t;
      rw [ht] at g; cases g;left;rw [h];right;rw [h];
    }
    h1 := by {
      intro i t hi ht;
      unfold walk_in_cursive at hw
      unfold cursive at hw
      unfold cursive_step at hw
      simp at hw
      let g := hw.2 t
      have : F t ≠ 0 := by exact Eq.trans_ne ht hi
      rw [if_neg this] at g
      have : i % a₀ < a₀ := Nat.mod_lt _ (by {
        have : a₀ = c₀.succ := rfl
        rw [this]
        exact Nat.succ_pos (c₀)
      })
      rw [← ht] at this
      rw [if_pos this] at g
      simp at g
      rw [Nat.add_mod] at g
      rw [ht] at g
      rw [g]
      simp
    }
    h2s := generalh2s _ hw
  }

def walk_ (k:ℕ) (i: ℕ) : ℕ :=
ite (i ≥ (a₀*k).succ)
  ((a₀ + ((i-(a₀*k).succ) % a₁)))
  (i % a₀)

theorem walk__injective' {k₁ k₂ : ℕ} (hk : k₁ < k₂) : walk_ k₁ ≠ walk_ k₂ := by {
  intro hcontra
  have : ∀ n, walk_ k₁ n = walk_ k₂ n := fun n ↦ congrFun hcontra n
  let g := this (a₀*k₁).succ
  unfold walk_ at g
  simp at g
  have h₀: ¬ (k₂) ≤ (k₁) := Nat.not_le.mpr hk
  have : ¬ (a₀ * k₂) ≤ (a₀ * k₁) := by {
    intro hcontra
    have : k₂ ≤ k₁ := Nat.le_of_mul_le_mul_left hcontra (Nat.succ_pos c₀)
    exact h₀ this
  }
  have : ¬ Nat.succ (a₀ * k₂) ≤ Nat.succ (a₀ * k₁) := by {
    intro hcontra
    exact this (Nat.succ_le_succ_iff.mp hcontra)
  }
  rw [if_neg this] at g
  have : ∀ x : ℕ, x % a₀ < a₀ := by {intro x;exact Nat.mod_lt _ (Nat.succ_pos c₀)}
  let G := this (a₀*k₁).succ
  rw [← g] at G
  exact LT.lt.false G

}

theorem keep_arriving (k l : ℕ) : walk_ k (a₀*k + 1 + a₁*l) = a₀ :=
  by {
    induction l; simp; unfold walk_; rw [if_pos _]; simp; exact Nat.le_refl (Nat.succ (a₀ * k))
    unfold walk_; rw [if_pos _]; simp; exact Nat.le_add_right (Nat.succ (a₀ * k)) (a₁ * Nat.succ _)
  }

theorem unique_walk_cursive_helper {w : ℕ → ℕ} (hw: walk_in_cursive w) (k : ℕ) (hwk: w (a₀*k).succ = a₀ ∧ ∀ n < (a₀*k).succ, w n ≠ a₀)
  : ∀ n < (a₀*k).succ, w n < a₀ := by {
  intro n
  induction n
  intro; rw [hw.1]; exact Nat.zero_lt_succ _

  intro hn_1
  by_cases (n_1 < (a₀*k).succ)
  let G:= hwk.2 n_1.succ hn_1
  unfold walk_in_cursive at hw
  unfold cursive at hw
  unfold cursive_step at hw
  simp at hw
  let g := hw.2 n_1
  let gg := n_ih h
  rw [if_pos gg] at g
  by_cases (w n_1=0)
  rw [if_pos h] at g
  cases g
  rw [h_1]
  have : 0 < a₀ := ha₀pos
  have : 1 ≤ a₀ := by exact this
  have : 1 < a₀ ∨ 1 = a₀ := by exact Nat.lt_or_eq_of_le this
  cases this
  exact h_2
  exfalso
  rw [← h_2] at G
  exact G h_1


  exfalso
  exact G h_1
  rw [if_neg h] at g
  simp at g
  rw [g]
  exact Nat.mod_lt _ (Nat.zero_lt_succ _)
  exfalso
  have : n_1 < (a₀*k).succ := Nat.lt_of_succ_lt hn_1
  exact h this
  }


theorem little_lemma {w: ℕ → ℕ} {k n: ℕ}
(g: w (Nat.succ n) ∈ NFA.step cursive (a₀ + (n - Nat.succ (a₀ * k)) % a₁) 0)
(h₄: n - Nat.succ (a₀ * k) + 1 = n - a₀ * k) : w (Nat.succ n) = a₀ + (n - a₀ * k) % a₁
:= by {unfold cursive at g; unfold cursive_step at g; simp at g; rw [← h₄]; exact g}

theorem unique_walk_cursive {w : ℕ → ℕ} (hw: walk_in_cursive w) {k : ℕ} (hwk': w (a₀*k).succ = a₀ ∧ ∀ n < (a₀*k).succ, w n ≠ a₀) :
  w = walk_ k :=
  by {
  have hwk : w (a₀*k).succ = a₀ ∧ ∀ n < (a₀*k).succ, w n < a₀ :=
    by {
      constructor
      exact hwk'.1
      exact (unique_walk_cursive_helper hw _ hwk')
    }
  apply funext; intro x; induction x
  unfold walk_in_cursive at hw; unfold walk_
  rw [if_neg _]; simp; exact hw.1

  intro hcontra; simp at hcontra

  by_cases hnk : (n.succ ≥ (a₀*k).succ)
  unfold walk_
  rw [if_pos _]
  simp
  let g := hw.2 n
  rw [n_ih] at g
  unfold walk_ at g
  by_cases hnks : (n ≥ (a₀*k).succ )

  have h₂: n ≥ a₀*k := Nat.lt_succ.mp hnk
  have h₃: n - a₀*k ≥ 1 := (le_tsub_iff_left h₂).mpr hnks
  have h₄: n - (a₀*k).succ + 1 = n - a₀*k := by {rw [Nat.sub_succ']; exact Nat.sub_add_cancel h₃}

  rw [if_pos hnks] at g;
  exact little_lemma g h₄

  have hn2k: n = a₀*k := (Nat.eq_of_lt_succ_of_not_lt hnk hnks).symm
  rw [hn2k]; simp; rw [if_neg hnks] at g
  have : a₀ ∣ n := Dvd.intro k (id hn2k.symm)
  have : n % a₀ = 0 := Nat.mod_eq_zero_of_dvd this
  rw [this] at g
  cases g; exact hwk.1

  rw [hn2k] at h
  exact h; exact hnk
  unfold walk_
  rw [if_neg hnk]
  unfold walk_ at n_ih

  have hnss : n.succ < (a₀*k).succ := Nat.not_le.mp hnk
  have hnlt : n < (a₀*k).succ := Nat.lt_of_succ_lt hnss
  have hn2k : ¬ n ≥ (a₀*k).succ := by {
    intro hcontra
    have : n < n := Nat.lt_of_lt_of_le hnlt hcontra
    exact LT.lt.false this
  }

  rw [if_neg hn2k] at n_ih
  unfold walk_in_cursive at hw
  let g₂ := hw.2 n
  rw [n_ih] at g₂

  unfold cursive at g₂
  unfold cursive_step at g₂
  simp at g₂
  have : n % a₀ < a₀ := Nat.mod_lt _ (Nat.zero_lt_succ _)
  rw [if_pos this] at g₂
  by_cases (n % a₀ = 0)
  rw [if_pos h] at g₂
  have h1: n.succ % a₀ = 1 := by {
    rw [Nat.succ_eq_add_one,Nat.add_mod,h,]
    simp
  }
  rw [h] at n_ih
  let g := hw.2 n
  rw [n_ih] at g
  unfold cursive at g
  unfold cursive_step at g
  simp at g
  cases g₂
  rw [h1]
  cases g
  exact h_2
  exact h_1
  simp at h_1
  rw [h1]
  exfalso
  let G := hwk'.2 n.succ hnss
  exact G h_1
  rw [if_neg h] at g₂
  simp at g₂
  exact g₂
}


theorem ne_of_le {w : ℕ → ℕ}
  {t₀:ℕ}
  (hw: walk_in_cursive w)
  (ht₀ : w (Nat.succ t₀) = a₀ ∧ ∀ (v : ℕ), w (Nat.succ v) = a₀ → t₀ ≤ v)
  : ∀ (s : ℕ), s ≤ t₀ → (w s) ≠ a₀
  := by {
      intro s hs
      cases s
      intro hcontra
      let gg := hw.1
      simp at gg
      rw [gg] at hcontra
      exact Nat.succ_ne_zero c₀ hcontra.symm
      intro hcontra
      let g := ht₀.2 n (hcontra)
      have : n < n := Nat.succ_le.mp (le_trans hs g)
      exact LT.lt.false this
    }


theorem ne_first {w : ℕ → ℕ} {t₀ k:ℕ} (hk: t₀ = a₀ * k) (hw: walk_in_cursive w)
  (ht₀ : w (Nat.succ t₀) = a₀ ∧ ∀ (v : ℕ), w (Nat.succ v) = a₀ → t₀ ≤ v)
  :w (a₀*k).succ = a₀ ∧ ∀ n, n < (a₀*k).succ → w n ≠ a₀ :=
    by {
      constructor; rw [hk] at ht₀; exact ht₀.1

      intro u hu hu2; cases u
      let g := hw.1
      rw [hu2] at g
      exact Nat.succ_ne_zero c₀ g

      have : a₀*k < a₀*k := calc
        _ = t₀  := id hk.symm
        _ ≤ n   := ht₀.2 n hu2
        _ < a₀*k := Nat.succ_lt_succ_iff.mp hu
      exact LT.lt.false this
    }

 def getk1 {w : ℕ → ℕ} {u:ℕ} (hw: walk_in_cursive w) (hu: w (Nat.succ u) = a₀) : ℕ
  := by {
    let t₀ := (find_spec_le (λ s ↦ w (Nat.succ s) = a₀) u hu).1
    let ht₀ := (find_spec_le (λ s ↦ w (Nat.succ s) = a₀) u hu).2
    let ish := getish w hw
    have hlt :  ∀ (s : ℕ), s ≤ t₀ → (w s) < a₀ := by {
      intro _ hs
      exact strengthen ish (ne_of_le hw ht₀) _ hs
    }
    have h02 : t₀ % a₀ = 0 % a₀ := get_a₀dvd ish _ hlt ht₀.1
    let k := (get_equation' (Nat.zero_le _) h02).1
    exact k
  }

theorem getk2 {w : ℕ → ℕ} {u:ℕ} (hw: walk_in_cursive w) (hu: w (Nat.succ u) = a₀): w = walk_ (getk1 hw hu)
  := by {
    let t₀ := (find_spec_le (λ s ↦ w (Nat.succ s) = a₀) u hu).1
    let ht₀ := (find_spec_le (λ s ↦ w (Nat.succ s) = a₀) u hu).2
    let ish := getish w hw
    have hlt :  ∀ (s : ℕ), s ≤ t₀ → (w s) < a₀ := by {
      intro _ hs
      exact strengthen ish (ne_of_le hw ht₀) _ hs
    }
    have h02 : t₀ % a₀ = 0 % a₀ := get_a₀dvd ish _ hlt ht₀.1
    let hk := (get_equation' (Nat.zero_le _) h02).2

    rw [zero_add] at hk
    exact unique_walk_cursive hw (ne_first hk hw ht₀)
  }

theorem l_unique {k l₁ l₂ : ℕ} (he: a₀*k + 1 + a₁*l₁ = a₀*k + 1 + a₁*l₂) : l₁=l₂
  := by {
    have hyp: a₁ * l₁ = a₁ * l₂ := Nat.add_left_cancel he
    have : a₁ = c₁.succ := rfl
    rw [this] at hyp
    exact Nat.eq_of_mul_eq_mul_left (Nat.succ_pos _) hyp
  }

def functional_eq_add_of_le  {m n : ℕ} (h : m ≤ n) : {k // n = m + k}
  := ⟨n-m,(Nat.add_sub_of_le h).symm⟩

theorem getl {k n:ℕ} (hmod₀: walk_ k n = a₀) :  {l : ℕ // n = a₀*k + 1 + a₁*l}
  := by {
    have hge : n ≥ a₀*k + 1 := by {
      unfold walk_ at hmod₀
      by_contra hcontra
      rw [if_neg hcontra] at hmod₀
      have : n % a₀ < a₀ := Nat.mod_lt _ ha₀pos
      rw [hmod₀] at this
      exact LT.lt.false this
    }
    let L := n - (a₀*k+1)
    have hL : n = a₀*k + 1 + L := (functional_eq_add_of_le hge).2
    rw [hL] at hmod₀
    unfold walk_ at hmod₀
    simp at hmod₀
    have : L = n - (a₀*k+1) := rfl
    rw [← this] at hmod₀
    have h₁: (L/a₁)*a₁ = L := Nat.div_mul_cancel (Nat.modEq_zero_iff_dvd.mp hmod₀)
    have h₂: L = a₁ * (L / a₁) := by {
      rw [mul_comm] at h₁
      exact h₁.symm
    }
    let l := L / a₁
    have : n = a₀ * k + 1 + a₁ * l := by {
      rw [← h₂]
      exact hL
    }
    exact ⟨l,this⟩
  }


theorem walk_walks (k:ℕ) : walk_in_cursive (walk_ k) :=
  by {
    constructor
    unfold walk_
    have : ¬ 0 ≥ Nat.succ (a₀ * k) := of_decide_eq_false rfl
    rw [if_neg this]
    exact rfl
    intro k_1; induction k_1; unfold walk_
    have : ¬ Nat.zero ≥ Nat.succ (a₀ * k) := of_decide_eq_false rfl
    rw [if_neg this]
    by_cases (k=0)
    have : Nat.succ Nat.zero ≥ Nat.succ (a₀ * k)
      := Nat.succ_le_succ (Nat.le_zero.mpr (mul_eq_zero_of_right a₀ h))
    rw [if_pos this,h]
    right
    exact rfl
    have h₁: ¬ Nat.zero = (a₀ * k) := by {
      intro hcontra
      cases Nat.zero_eq_mul.mp hcontra
      have : 0 < a₀ := ha₀pos
      rw [h_1] at this
      exact Nat.not_succ_le_zero 0 this
      exact h h_1
    }
    have h₂: ¬ Nat.zero ≥ (a₀ * k) := by {
      intro hcontra
      exact h₁ (id (Nat.le_zero.mp hcontra).symm)
    }
    have : ¬ Nat.succ Nat.zero ≥ Nat.succ (a₀ * k) := by {
      intro hcontra
      exact h₂ (Nat.lt_succ.mp hcontra)
    }
    rw [if_neg this]; left; rfl
    unfold walk_
    by_cases hss : (Nat.succ (Nat.succ n) ≥ Nat.succ (a₀ * k))
    rw [if_pos hss]
    by_cases hnk : (Nat.succ n ≥ Nat.succ (a₀ * k))
    rw [if_pos hnk]
    simp
    have h₁ : n ≥ a₀*k := Nat.succ_le_succ_iff.mp hnk
    have h₂ : n + 1 - a₀*k = n - a₀*k + 1 := Nat.sub_add_comm h₁

    unfold cursive
    unfold cursive_step
    simp
    rw [h₂]

    rw [if_neg hnk]; simp
    have h₅ : n.succ = a₀*k := (Nat.eq_of_lt_succ_of_not_lt hss hnk).symm
    have h₃: n+1 - a₀*k = 0 := tsub_eq_of_eq_add_rev h₅
    rw [h₃,h₅]; simp; right; exact rfl
    -- early times:
    rw [if_neg hss]
    have : ¬ Nat.succ n ≥ Nat.succ (a₀ * k) := by {
      intro hcontra
      have : n.succ ≤ n.succ.succ := Nat.le_succ (Nat.succ n)
      exact hss (le_trans hcontra this)
    }
    rw [if_neg this]
    by_cases (n.succ % a₀ = 0)
    rw [h];
    have : n.succ.succ % a₀ = 1 := by {
      rw [Nat.succ_eq_add_one,Nat.add_mod,h,];simp
    }
    rw [this]; left; exact rfl

    unfold cursive
    unfold cursive_step
    simp
    rw [if_neg h]
    have : n.succ % a₀ < a₀ := Nat.mod_lt _ ha₀pos
    rw [if_pos this]
    simp
  }


theorem walk__injective (k₁ k₂ : ℕ) (he : walk_ k₁ = walk_ k₂) : k₁ = k₂ :=
  by {
    contrapose he
    have : k₁ < k₂ ∨ k₂ < k₁ := Ne.lt_or_lt he
    cases this; exact walk__injective' h; exact (walk__injective' h).symm
  }

def walk_of_solution (T:ℕ)
  : {p : ℕ×ℕ // T.succ = a₀ * p.1 + 1 + a₁ * p.2} → {w : ℕ → ℕ // walk_in_cursive w ∧ w T.succ = a₀}
  := by {
    intro p; let k := p.1.1
    exists walk_ k; constructor
    exact walk_walks k; rw [p.2];
    exact keep_arriving _ _
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
  rename wpair.1 (Nat.succ T) = a₀ => hTold
  let lpair := (getl hT); let l := lpair.1
  exists ⟨(k,l), lpair.2⟩; exact SetCoe.ext (id hwp.symm)
}

theorem walk_of_solution_bijective (T:ℕ) :
Function.Bijective (λ p ↦ walk_of_solution T p) := by {
  constructor; exact walk_of_solution_injective _; exact walk_of_solution_surjective _
}

theorem main {T:ℕ} : (∃! p : ℕ×ℕ, T.succ = a₀ * p.1 + 1 + a₁ * p.2)
↔ (∃! w, walk_in_cursive w ∧ w T.succ = a₀)
  := unique_iff_of_bijective (walk_of_solution_bijective T)
