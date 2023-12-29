import Mathlib.Computability.NFA
import Mathlib.Data.Nat.Basic
import Mathlib.MeasureTheory.Constructions.Prod.Basic
import Std.Data.Nat.Lemmas
import Mathlib.Data.Matrix.Basic

set_option tactic.hygienic false
-- set_option maxHeartbeats 10000000
/-
Connect the diophantine equation a₀x+a₁y=n with
a walk in a digraph that has a cycle of length a₀ followed by a cycle of length a₁.
-/

-- Some properties of walks in cursive NFAs:
structure cursiveish (a₀ a₁ :ℕ) (f:ℕ → ℕ) where
 (h00 : f 0 = 0)
 (h0: ∀ t, f t = 0 → f t.succ = 1 % a₀ ∨ f t.succ = a₀)
 (h1: ∀ i t : ℕ, i % a₀ ≠ 0 → f t = i % a₀ → f t.succ = (i.succ) % a₀)
 (h2s: ∀ i t, f t = a₀ + (i%a₁) → f t.succ = a₀ + (i.succ %a₁))

section general

def functional_eq_add_of_le  {m n : ℕ} (h : m ≤ n) : {k // n = m + k}
  := ⟨n-m,(Nat.add_sub_of_le h).symm⟩

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

theorem walk_mod_a₀ {a₀ a₁ : ℕ} {f:ℕ → ℕ}(ish : cursiveish a₀ a₁ f)(t: ℕ)
(hs : ∀ s, s ≤ t → f s < a₀) : f t = t % a₀
  := by {
  induction t
  rw [ish.h00]
  rfl
  have hfn : f n = n % a₀ := n_ih (λ s hsn ↦ hs s (Nat.le_step hsn))
  by_cases hna : (n % a₀ = 0); rw [hna] at hfn
  let g := ish.h0 n hfn; cases g
  rename f n.succ = 1 % a₀ => cg; rw [cg]
  have : (n+1) % a₀ = (n % a₀ + 1 % a₀) % a₀ := Nat.add_mod _ _ _
  rw [hna,zero_add,Nat.mod_mod] at this; exact id this.symm

  rw [h]; exfalso; let gg := hs n.succ (le_refl _)
  have : a₀ < a₀ := Eq.trans_lt (id h.symm) gg
  exact LT.lt.false this; exact ish.h1 n n hna hfn
 }

 theorem get_a₀dvd {a₀ a₁ : ℕ} (ha₀pos : 0 < a₀) {f:ℕ → ℕ}(ish : cursiveish a₀ a₁ f)(t: ℕ)
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

theorem strengthen {a₀ a₁ : ℕ} (ha₀pos : 0 < a₀) {t₀:ℕ} {f:ℕ → ℕ}
  (ish : cursiveish a₀ a₁ f) (ht₀ : (∀ s, s ≤ t₀ → f s ≠ a₀)) :  ∀ s, s ≤ t₀ → f s < a₀
  := by {
    induction t₀; intro s; intro; have : s = 0 := Nat.le_zero.mp a
    rw [this,ish.h00]; exact ha₀pos

    intro s hs; cases hs
    let g := n_ih (by {intro _ hsn; exact ht₀ _ (Nat.le_step hsn)}) n (le_refl _)
    by_cases (f n = 0); let gg := ish.h0 n h; cases gg; rw [h_1]

    let G := ht₀ n.succ (le_refl _); rw [h_1] at G
    exact Nat.mod_lt _ ha₀pos

    let ggg := ht₀ n.succ (le_refl _); exfalso; exact ggg h_1

    let g1 := ish.h1 (f n) n (by {
      contrapose h; simp; simp at h
      exact zero_of_mod (Nat.one_le_iff_ne_zero.mpr (Nat.not_eq_zero_of_lt ha₀pos)) h g
    }) (Nat.mod_eq_of_lt g).symm
    rw [g1]

    exact Nat.mod_lt _ (ha₀pos)
    let g := n_ih (by {intro _ hsn; exact ht₀ _ (Nat.le_step hsn)}) s a
    exact g
  }


-- Our running example will be the "cursive" NFA that has a cycle of length a₀ and then a cycle of length a₁.
-- We implement it as an infinite NFA where only the first a₀+a₁ states are reachable,
-- in order to avoid type casting issues.

def cursive_step (a_ : Fin 2 → ℕ)  : ℕ → Set (ℕ) :=
by {
  let a₀ := a_ 0
  let a₁ := a_ 1
  exact (
  λ q ↦ ite (q=0)
  {1 % a₀,a₀}
  (ite (q<a₀) {(q+1) % a₀} {((a₀ + (((q-a₀+1) % a₁))):ℕ)}))
}

def cursive_step' (a_ : Fin 2 → ℕ)  : ℕ → Set (ℕ) :=
  by {
    let a₀ := a_ 0
    let a₁ := a_ 1
    exact (
      λ q ↦ ite (q=0)
      {1 % a₀,a₀}
      (ite (q<a₀) {(q+1) % a₀} {((a₀ + (((q-a₀+1) % a₁))):ℕ)})
    )
}
def cursive' (a_ : Fin 2 → ℕ) : NFA (Fin 1) (ℕ) := {
  step := λ q _ ↦ cursive_step' a_ q
  start := {0}
  accept := {a_ 0}
}
def walk_in_cursive' (a_ : Fin 2 → ℕ) (f : ℕ → ℕ) := f 0 ∈ (cursive' a_).start
∧ ∀ k, f k.succ ∈ (cursive' a_).step (f k) 0
theorem generalh2s' (a_ : Fin 2 → ℕ) (ha₀pos : 0 < a_ 0) (F: ℕ → ℕ)
(hw: walk_in_cursive' a_ F)
: ∀ (i t : ℕ), (F t) = a_ 0 + i % a_ 1 → (F (Nat.succ t)) = a_ 0 + Nat.succ i % a_ 1
:= by {
  intro i t hit; let g := hw.2 t; unfold walk_in_cursive' at g; rw [hit] at g
  unfold cursive' at g;
  unfold cursive_step' at g; simp at g;
  have : a_ 0 ≠ 0 := by {intro hcontra; rw [hcontra] at ha₀pos; exact LT.lt.false ha₀pos}
  have : ¬ ( a_ 0 = 0 ∧ i % a_ 1 = 0) := by {intro hcontra; exact this hcontra.1}
  rw [if_neg this] at g
  rw [g]
}

theorem getish' (F:ℕ → ℕ) (a_ : Fin 2 → ℕ) (ha₀pos : 0 < a_ 0) (hw : walk_in_cursive' a_ F) :
cursiveish (a_ 0) (a_ 1) (λ n ↦ (F n))
  := {
    h00 := by {
      have : F 0 = 0 := Set.eq_of_mem_singleton hw.1
      rw [this];
    }
    h0 := by {
      intro t ht; let g := hw.2 t;
      rw [ht] at g; cases g;left;rw [h];
      right;rw [h];
    }
    h1 := by {
      let a₀ := a_ 0
      intro i t hi ht;
      unfold walk_in_cursive' at hw; unfold cursive' at hw
      unfold cursive_step' at hw; simp at hw
      let g := hw.2 t
      have : F t ≠ 0 := Eq.trans_ne ht hi
      rw [if_neg this] at g
      have : i % a₀ < a₀ := Nat.mod_lt _ (ha₀pos)
      rw [← ht] at this; rw [if_pos this] at g
      simp at g; rw [Nat.add_mod,ht] at g
      rw [g]; simp
    }
    h2s := generalh2s' _ ha₀pos _ hw
  }

noncomputable def walk_' (a_ : Fin 2 → ℕ) (k:ℕ) (i: ℕ) : ℕ :=
by {
  let a₀ := a_ 0
  let a₁ := a_ 1
  exact (ite (i ≥ (a₀*k).succ)
  ((a₀ + ((i-(a₀*k).succ) % a₁)))
  (i % a₀)
)
}

theorem walk__injective_lt' (a_ : Fin 2 → ℕ) (ha₀pos : 0 < a_ 0) {k₁ k₂ : ℕ} (hk : k₁ < k₂) : walk_' a_ k₁ ≠ walk_' a_ k₂ := by {
  intro hcontra
  have : ∀ n, walk_' a_ k₁ n = walk_' a_ k₂ n := fun n ↦ congrFun hcontra n
  let g := this (a_ 0 * k₁).succ
  unfold walk_' at g;
  simp at g
  have h₀: ¬ (k₂) ≤ (k₁) := Nat.not_le.mpr hk
  -- let a₀ := a_ 0
  -- let a₁ := a_ 1
  have : ¬ (a_ 0 * k₂) ≤ (a_ 0 * k₁) := by {
    intro hcontra
    have : k₂ ≤ k₁ := Nat.le_of_mul_le_mul_left hcontra (ha₀pos)
    exact h₀ this
  }
  have : ¬ Nat.succ (a_ 0 * k₂) ≤ Nat.succ (a_ 0 * k₁) := by {
    intro hcontra
    exact this (Nat.succ_le_succ_iff.mp hcontra)
  }
  rw [if_neg this] at g
  have : ∀ x : ℕ, x % a_ 0 < a_ 0 := by {intro x;exact Nat.mod_lt _ ha₀pos}
  let G := this (a_ 0*k₁).succ;
  rw [← g] at G; exact LT.lt.false G
}

theorem keep_arriving' (a_ : Fin 2 → ℕ) (k l : ℕ) : walk_' a_ k (a_ 0*k + 1 + a_ 1*l) = a_ 0 :=
  by {
    induction l;
    unfold walk_'; rw [if_pos _]; simp; exact Nat.le_refl (Nat.succ (a_ 0 * k))
    unfold walk_'; rw [if_pos _]; simp; exact Nat.le_add_right (Nat.succ (a_ 0 * k)) (a_ 1 * Nat.succ _)
  }

theorem unique_walk_cursive_helper' (a_ : Fin 2 → ℕ) (ha₀pos : 0 < a_ 0) {w : ℕ → ℕ}
(hw: walk_in_cursive' a_ w) (k : ℕ) (hwk: w (a_ 0*k).succ = a_ 0 ∧ ∀ n < (a_ 0*k).succ, w n ≠ a_ 0)
  : ∀ n < (a_ 0*k).succ, w n < a_ 0 := by {
  intro n; induction n; intro; rw [hw.1]; exact ha₀pos

  intro hn_1; by_cases (n_1 < (a_ 0*k).succ)
  let G:= hwk.2 n_1.succ hn_1
  unfold walk_in_cursive' at hw; unfold cursive' at hw; unfold cursive_step' at hw
  simp at hw; let g := hw.2 n_1; let gg := n_ih h; rw [if_pos gg] at g
  by_cases (w n_1=0); rw [if_pos h] at g; simp at g; cases g
  rw [h_1]; exact Nat.mod_lt _ ha₀pos

  exfalso; exact G h_1; let H := hw.2 n_1
  rw [if_neg h,if_pos gg] at H; simp at H; rw [H]; exact Nat.mod_lt _ ha₀pos

  let g := hw.2 n_1; unfold cursive' at g; unfold cursive_step' at g; simp at g
  have : n_1 < (a_ 0*k).succ := Nat.lt_of_succ_lt hn_1
  let G := n_ih this; rw [if_pos G] at g
  have : w n_1 ≠ 0 := by {
    intro hcontra; rw [if_pos hcontra] at g; simp at g; cases g
    exact h this; let H := hwk.2 n_1.succ hn_1; exact H h_1
  }
  rw [if_neg _] at g; simp at g; rw [g]; exact Nat.mod_lt _ ha₀pos; exact this
  }

theorem little_lemma' (a_ : Fin 2 → ℕ) (ha₀pos : 0 < a_ 0)  {w: ℕ → ℕ} {k n: ℕ}
(g: w (Nat.succ n) ∈ NFA.step (cursive' a_) (a_ 0 + (n - Nat.succ (a_ 0 * k)) % a_ 1) 0)
(h₄: n - Nat.succ (a_ 0 * k) + 1 = n - a_ 0 * k) : w (Nat.succ n) = a_ 0 + (n - a_ 0 * k) % a_ 1
:= by {
  unfold cursive' at g; unfold cursive_step' at g; simp at g; rw [← h₄];
  have : ¬ (a_ 0 = 0 ∧ (n - Nat.succ (a_ 0 * k)) % a_ 1 = 0) := by {
    intro hcontra
    have : 0 < 0 := by {
      rw [hcontra.1] at ha₀pos
      exact ha₀pos
    }
    exact LT.lt.false this
  }
  rw [if_neg this] at g
  exact g
}

theorem unique_walk_cursive' (a_ : Fin 2 → ℕ) (ha₀pos : 0 < a_ 0) {w : ℕ → ℕ}
  (hw: walk_in_cursive' a_ w) {k : ℕ} (hwk': w (a_ 0*k).succ = a_ 0 ∧ ∀ n < (a_ 0*k).succ, w n ≠ a_ 0) :
  w = walk_' a_ k :=
  by {
  let a₀ := a_ 0
  have hwk : w (a₀*k).succ = a₀ ∧ ∀ n < (a₀*k).succ, w n < a₀ :=
    ⟨ hwk'.1, (unique_walk_cursive_helper' a_ ha₀pos hw _ hwk')⟩
  apply funext; intro x; induction x; unfold walk_in_cursive' at hw; unfold walk_'
  rw [if_neg _]; simp; exact hw.1
  intro hcontra; simp at hcontra
  by_cases hnk : (n.succ ≥ (a₀*k).succ)
  unfold walk_'; rw [if_pos _]; simp; let g := hw.2 n; rw [n_ih] at g
  unfold walk_' at g; by_cases hnks : (n ≥ (a₀*k).succ )

  have h₂: n ≥ a₀*k := Nat.lt_succ.mp hnk
  have h₃: n - a₀*k ≥ 1 := (le_tsub_iff_left h₂).mpr hnks
  have h₄: n - (a₀*k).succ + 1 = n - a₀*k := by {rw [Nat.sub_succ']; exact Nat.sub_add_cancel h₃}

  rw [if_pos hnks] at g; exact little_lemma' a_ ha₀pos g h₄

  have hn2k: n = a₀*k := (Nat.eq_of_lt_succ_of_not_lt hnk hnks).symm
  rw [hn2k]; simp; rw [if_neg hnks] at g; have : a₀ ∣ n := Dvd.intro k (id hn2k.symm)
  have : n % a₀ = 0 := Nat.mod_eq_zero_of_dvd this
  rw [this] at g
  cases g; exact hwk.1

  rw [hn2k] at h; exact h; exact hnk; unfold walk_'; rw [if_neg hnk]
  unfold walk_' at n_ih

  have hnss : n.succ < (a₀*k).succ := Nat.not_le.mp hnk
  have hnlt : n < (a₀*k).succ := Nat.lt_of_succ_lt hnss
  have hn2k : ¬ n ≥ (a₀*k).succ := by {
    intro hcontra
    have : n < n := Nat.lt_of_lt_of_le hnlt hcontra
    exact LT.lt.false this
  }

  rw [if_neg hn2k] at n_ih; unfold walk_in_cursive' at hw
  let g₂ := hw.2 n; rw [n_ih] at g₂

  unfold cursive' at g₂; unfold cursive_step' at g₂
  simp at g₂
  have : n % a₀ < a₀ := Nat.mod_lt _ (ha₀pos)
  rw [if_pos this] at g₂; by_cases (n % a₀ = 0); rw [if_pos h] at g₂
  have h1: n.succ % a₀ = 1 % a₀ := by {
    rw [Nat.succ_eq_add_one,Nat.add_mod,h,]
    simp
  }
  rw [h] at n_ih; let g := hw.2 n; rw [n_ih] at g
  unfold cursive' at g; unfold cursive_step' at g
  simp at g; cases g₂; rw [h1]; cases g; exact h_2; exact h_1
  simp at h_1; rw [h1]; exfalso; let G := hwk'.2 n.succ hnss
  exact G h_1; rw [if_neg h] at g₂; simp at g₂; exact g₂
}

theorem ne_of_le' (a_ : Fin 2 → ℕ) (ha₀pos : 0 < a_ 0) {w : ℕ → ℕ}
  {t₀:ℕ}
  (hw: walk_in_cursive' a_ w)
  (ht₀ : w (Nat.succ t₀) = a_ 0 ∧ ∀ (v : ℕ), w (Nat.succ v) = a_ 0 → t₀ ≤ v)
  : ∀ (s : ℕ), s ≤ t₀ → (w s) ≠ a_ 0
  := by {
      intro s hs
      cases s
      intro hcontra
      let gg := hw.1
      simp at gg
      rw [gg] at hcontra
      rw [← hcontra] at ha₀pos
      exact LT.lt.false ha₀pos
      intro hcontra
      let g := ht₀.2 n (hcontra)
      have : n < n := Nat.succ_le.mp (le_trans hs g)
      exact LT.lt.false this
    }

theorem ne_first' (a_ : Fin 2 → ℕ) (ha₀pos : 0 < a_ 0) {w : ℕ → ℕ} {t₀ k:ℕ} (hk: t₀ = a_ 0 * k)
(hw: walk_in_cursive' a_ w)
  (ht₀ : w (Nat.succ t₀) = a_ 0 ∧ ∀ (v : ℕ), w (Nat.succ v) = a_ 0 → t₀ ≤ v)
  :w (a_ 0*k).succ = a_ 0 ∧ ∀ n, n < (a_ 0 * k).succ → w n ≠ a_ 0 :=
    by {
      let a₀ := a_ 0
      constructor; rw [hk] at ht₀; exact ht₀.1

      intro u hu hu2; cases u
      let g := hw.1
      rw [hu2] at g
      rw [← g] at ha₀pos
      exact LT.lt.false ha₀pos

      have : a₀*k < a₀*k := calc
        _ = t₀  := id hk.symm
        _ ≤ n   := ht₀.2 n hu2
        _ < a₀*k := Nat.succ_lt_succ_iff.mp hu
      exact LT.lt.false this
    }

noncomputable def getk1' (a_ : Fin 2 → ℕ) (ha₀pos : 0 < a_ 0) {w : ℕ → ℕ} {u:ℕ}
(hw: walk_in_cursive' a_ w) (hu: w (Nat.succ u) = a_ 0) : ℕ
  := by {
    let a₀ := a_ 0
    let t₀ := (find_spec_le (λ s ↦ w (Nat.succ s) = a₀) u hu).1
    let ht₀ := (find_spec_le (λ s ↦ w (Nat.succ s) = a₀) u hu).2
    let ish := getish' w a_ ha₀pos hw
    have hlt :  ∀ (s : ℕ), s ≤ t₀ → (w s) < a₀ := by {
      intro _ hs
      exact strengthen ha₀pos ish (ne_of_le' a_ ha₀pos hw ht₀) _ hs
    }
    have h02 : t₀ % a₀ = 0 % a₀ := get_a₀dvd ha₀pos ish _ hlt ht₀.1
    let k := (get_equation' (Nat.zero_le _) h02).1
    exact k
  }

  theorem getk2' (a_ : Fin 2 → ℕ) (ha₀pos : 0 < a_ 0) {w : ℕ → ℕ} {u:ℕ}
  (hw: walk_in_cursive' a_ w) (hu: w (Nat.succ u) = a_ 0)
  : w = walk_' a_ (getk1' a_ ha₀pos hw hu)
  := by {
    let a₀ := a_ 0
    let t₀ := (find_spec_le (λ s ↦ w (Nat.succ s) = a₀) u hu).1
    let ht₀ := (find_spec_le (λ s ↦ w (Nat.succ s) = a₀) u hu).2
    let ish := getish' w a_ ha₀pos hw
    have hlt :  ∀ (s : ℕ), s ≤ t₀ → (w s) < a₀ := by {
      intro _ hs
      exact strengthen ha₀pos ish (ne_of_le' a_ ha₀pos hw ht₀) _ hs
    }
    have h02 : t₀ % a₀ = 0 % a₀ := get_a₀dvd ha₀pos ish _ hlt ht₀.1
    let hk := (get_equation' (Nat.zero_le _) h02).2

    rw [zero_add] at hk
    exact unique_walk_cursive' a_ ha₀pos hw (ne_first' a_ ha₀pos hk hw ht₀)
  }

theorem l_unique' (a_ : Fin 2 → ℕ) (ha₁pos : 0 < a_ 1) {k l₁ l₂ : ℕ}
  (he: a_ 0*k + 1 + a_ 1*l₁ = a_ 0*k + 1 + a_ 1*l₂) : l₁=l₂
  :=  Nat.eq_of_mul_eq_mul_left ha₁pos (Nat.add_left_cancel he)

theorem getl' (a_ : Fin 2 → ℕ) (ha₀pos : 0 < a_ 0) {k n:ℕ} (hmod₀: walk_' a_ k n = a_ 0)
:  {l : ℕ // n = a_ 0*k + 1 + a_ 1*l}
  := by {
    let a₀ := a_ 0
    let a₁ := a_ 1
    have hge : n ≥ a₀*k + 1 := by {
      unfold walk_' at hmod₀; by_contra hcontra; rw [if_neg hcontra] at hmod₀
      have : n % a₀ < a₀ := Nat.mod_lt _ ha₀pos; rw [hmod₀] at this
      exact LT.lt.false this
    }
    let L := n - (a₀*k+1)
    have hL : n = a₀*k + 1 + L := (functional_eq_add_of_le hge).2
    rw [hL] at hmod₀; unfold walk_' at hmod₀; simp at hmod₀
    have : L = n - (a₀*k+1) := rfl; rw [← this] at hmod₀
    have h₁: (L/a₁)*a₁ = L := Nat.div_mul_cancel (Nat.modEq_zero_iff_dvd.mp hmod₀)
    have h₂: L = a₁ * (L / a₁) := by {rw [mul_comm] at h₁; exact h₁.symm}
    let l := L / a₁
    have : n = a₀ * k + 1 + a₁ * l := by {rw [← h₂];exact hL}
    exact ⟨l,this⟩
  }

theorem walk_walks' (a_ : Fin 2 → ℕ) (ha₀pos : 0 < a_ 0) (k:ℕ)
  : walk_in_cursive' a_ (walk_' a_ k) :=
  by {
    let a₀ := a_ 0
    constructor; unfold walk_'
    have : ¬ 0 ≥ Nat.succ (a₀ * k) := of_decide_eq_false rfl
    rw [if_neg this]
    exact rfl
    intro k_1; induction k_1; unfold walk_'
    have : ¬ Nat.zero ≥ Nat.succ (a₀ * k) := of_decide_eq_false rfl
    rw [if_neg this]
    by_cases (k=0)
    have : Nat.succ Nat.zero ≥ Nat.succ (a₀ * k)
      := Nat.succ_le_succ (Nat.le_zero.mpr (mul_eq_zero_of_right a₀ h))
    rw [if_pos this,h]; simp; right; exact rfl
    have h₁: ¬ Nat.zero = (a₀ * k) := by {
      intro hcontra; cases Nat.zero_eq_mul.mp hcontra
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

    unfold walk_'
    by_cases hss : (Nat.succ (Nat.succ n) ≥ Nat.succ (a₀ * k))
    rw [if_pos hss]
    by_cases hnk : (Nat.succ n ≥ Nat.succ (a₀ * k))
    rw [if_pos hnk]
    simp
    have h₁ : n ≥ a₀*k := Nat.succ_le_succ_iff.mp hnk
    have h₂ : n + 1 - a₀*k = n - a₀*k + 1 := Nat.sub_add_comm h₁

    unfold cursive'; unfold cursive_step'; simp; rw [h₂]

    have : ¬ (a_ 0 = 0 ∧ (n - a_ 0 * k) % a_ 1 = 0) := by {
      intro hcontra
      have : 0 < 0 := by {
        rw [hcontra.1] at ha₀pos
        exact ha₀pos
      }
      exact LT.lt.false this
    }
    rw [if_neg this]
    simp
    rw [if_neg hnk];
    have h₅ : n.succ = a₀*k := (Nat.eq_of_lt_succ_of_not_lt hss hnk).symm
    have h₃: n+1 - a₀*k = 0 := tsub_eq_of_eq_add_rev h₅
    simp
    rw [h₃,h₅]; simp; right; exact rfl
    -- early times:
    rw [if_neg hss]
    have : ¬ Nat.succ n ≥ Nat.succ (a₀ * k) := by {
      intro hcontra
      have : n.succ ≤ n.succ.succ := Nat.le_succ (Nat.succ n)
      exact hss (le_trans hcontra this)
    }
    rw [if_neg this]; by_cases (n.succ % a₀ = 0); rw [h];
    have : n.succ.succ % a₀ = 1 % a₀ := by {
      rw [Nat.succ_eq_add_one,Nat.add_mod,h,];simp
    }
    rw [this]; left; exact rfl

    unfold cursive'; unfold cursive_step'; simp
    rw [if_neg h]; have : n.succ % a₀ < a₀ := Nat.mod_lt _ ha₀pos
    rw [if_pos this]; simp
  }

theorem walk__injective' (a_ : Fin 2 → ℕ) (ha₀pos : 0 < a_ 0) (k₁ k₂ : ℕ)
(he : walk_' a_ k₁ = walk_' a_ k₂) : k₁ = k₂ :=
  by {
    contrapose he
    have : k₁ < k₂ ∨ k₂ < k₁ := Ne.lt_or_lt he
    cases this; exact walk__injective_lt' a_ ha₀pos h;
    exact (walk__injective_lt' a_ ha₀pos h).symm
  }

noncomputable def walk_of_solution' (T:ℕ) (a_ : Fin 2 → ℕ) (ha₀pos : 0 < a_ 0)
-- Here we see T and a_ together specify an instance
  : {p : ℕ×ℕ // T.succ = a_ 0 * p.1 + 1 + a_ 1 * p.2}
  → {w : ℕ → ℕ // walk_in_cursive' a_ w ∧ w T.succ = a_ 0}
  := by {
    intro p; let k := p.1.1
    exists walk_' a_ k; constructor
    exact walk_walks' a_ ha₀pos k; rw [p.2];
    exact keep_arriving' _ _ _
  }

theorem walk_of_solution_injective' (T:ℕ)  (a_ : Fin 2 → ℕ)(ha₀pos : 0 < a_ 0) (ha₁pos : 0 < a_ 1) :
Function.Injective (λ p ↦ walk_of_solution' T a_ ha₀pos p) := by {
  unfold Function.Injective
  intro p₁ p₂ hp
  unfold walk_of_solution' at hp
  simp at hp
  have h₁₁: p₁.1.1 = p₂.1.1 := walk__injective' a_ ha₀pos p₁.1.1 p₂.1.1 hp
  have h₁₂: p₁.1.2 = p₂.1.2 := l_unique' a_ ha₁pos (Eq.trans p₁.2.symm (by {rw [h₁₁]; exact p₂.2}))
  exact SetCoe.ext (Prod.ext h₁₁ h₁₂)
}

theorem walk_of_solution_surjective' (T:ℕ)  (a_ : Fin 2 → ℕ) (ha₀pos : 0 < a_ 0):
Function.Surjective (λ p ↦ walk_of_solution' T a_ ha₀pos p) := by {
  let a₀ := a_ 0
  unfold Function.Surjective
  intro wpair
  let ⟨hw,hT⟩ := wpair.2; let k := getk1' a_ ha₀pos hw hT
  have hwp : wpair.1 = walk_' a_ k := getk2' a_ ha₀pos _ _
  rw [hwp] at hT
  rename wpair.1 (Nat.succ T) = a₀ => hTold
  let lpair := (getl' a_ ha₀pos hT); let l := lpair.1
  exists ⟨(k,l), lpair.2⟩; exact SetCoe.ext (id hwp.symm)
}

theorem walk_of_solution_bijective' (T:ℕ)  (a_ : Fin 2 → ℕ) (ha₀pos : 0 < a_ 0) (ha₁pos : 0 < a_ 1):
Function.Bijective (λ p ↦ walk_of_solution' T a_ ha₀pos p) := by {
  constructor; exact walk_of_solution_injective' _ _ _ ha₁pos;
  exact walk_of_solution_surjective' _ _ _
}

theorem main' {T:ℕ} {a_ : Fin 2 → ℕ} (ha₀pos : 0 < a_ 0) (ha₁pos : 0 < a_ 1) : (∃! p : ℕ×ℕ, T.succ = a_ 0 * p.1 + 1 + a_ 1 * p.2)
↔ (∃! w, walk_in_cursive' a_ w ∧ w T.succ = a_ 0)
  := unique_iff_of_bijective (walk_of_solution_bijective' T a_ ha₀pos ha₁pos)

-- We can now elegantly get rid of the successor in theorem main:
theorem main_n' {n:ℕ}  {a_ : Fin 2 → ℕ} (ha₀pos : 0 < a_ 0) (ha₁pos : 0 < a_ 1)
: (∃! p : ℕ×ℕ, n = a_ 0 * p.1 + 1 + a_ 1 * p.2)
↔ (∃! w, walk_in_cursive' a_ w ∧ w n = a_ 0) :=
by {
  let a₀ := a_ 0
  let a₁ := a_ 1
  cases n;
  -- n is 0:
  constructor; intro h; exfalso; rcases h with ⟨p,hp⟩; let g := hp.1
  have : 1 ≤ 0 := calc
         1 ≤ a₀ * p.1 + 1 := Nat.le_add_left 1 (a₀ * p.1)
         _ ≤ a₀ * p.1 + 1 + a₁ * p.2 := Nat.le_add_right (a₀ * p.1 + 1) (a₁ * p.2)
         _ = 0 := self_eq_add_left.mp g
  exact Nat.not_succ_le_zero 0 this

  intro h; exfalso; rcases h with ⟨w,hw⟩; let G := hw.1.2; rw [hw.1.1.1] at G
  exact LT.lt.false (Nat.lt_of_lt_of_eq ha₀pos (id G.symm))
  -- n is T.succ:
  exact main' ha₀pos ha₁pos
}

theorem main_prod' {n:ℕ} {a_ : Fin 2 → ℕ} (ha₀pos : 0 < a_ 0) (ha₁pos : 0 < a_ 1)
: (∃! p : Fin 2 → ℕ, n = a_ 0 * p 0 + 1 + a_ 1 * p 1)
↔ (∃! w, walk_in_cursive' a_ w ∧ w n = a_ 0) :=
by {
  constructor; intro h
  rcases h with ⟨p,hp⟩
  exact (main_n' ha₀pos ha₁pos).mp (by {
    exists (p 0, p 1); simp
    constructor; exact hp.1
    intro p'0 p'1 hp'; let g := hp.2 (λ i ↦ [p'0, p'1].get i) hp'
    constructor
    exact congr_arg (λ x ↦ x 0) g
    exact congr_arg (λ x ↦ x 1) g
  })
  intro h
  let g := (main_n' ha₀pos ha₁pos).mpr h
  rcases g with ⟨p,hp⟩
  exists (λ i ↦ [p.1, p.2].get i)
  constructor; simp; exact hp.1; intro p' hp'
  let g := hp.2 (p' 0, p' 1) hp'; apply funext; intro i
  have : i ≤ 1 := Fin.le_last _
  have : i < 1 ∨ i = 1 := by exact lt_or_eq_of_le this
  cases this
  have : i ≤ 0 := by exact Fin.succ_le_succ_iff.mp h_1
  have : i = 0 := by exact Fin.le_zero_iff.mp this
  rw [this]; simp; exact congr_arg (λ x ↦ x.1) g; rw [h_1]
  simp; exact congr_arg (λ x ↦ x.2) g
}

theorem main_dot' {n:ℕ} {a_ : Fin 2 → ℕ} (ha₀pos : 0 < a_ 0) (ha₁pos : 0 < a_ 1)
: (∃! p : Fin 2 → ℕ, n = Matrix.dotProduct a_ p + 1)
↔ (∃! w, walk_in_cursive' a_ w ∧ w n = a_ 0) := -- maybe make it in terms of T to look nicer
by {
  let a₀ := a_ 0
  let a₁ := a_ 1
  constructor; intro h; rcases h with ⟨p,hp⟩
  have : (∃! p : Fin 2 → ℕ, n = a₀ * p 0 + 1 + a₁ * p 1) := by {
    exists p; constructor; let g := hp.1
    unfold Matrix.dotProduct at g; rw [g];
    simp; ring; intro y h
    apply hp.2 y; rw [h]
    have : a₀ * y 0 + 1 + a₁ * y 1 = a₀ * y 0 + a₁ * y 1 + 1 := by ring
    rw [this];
    unfold Matrix.dotProduct
    rfl
  }
  exact (main_prod' ha₀pos ha₁pos).mp this
  intro h
  have : (∃! p : Fin 2 → ℕ, n = a₀ * p 0 + 1 + a₁ * p 1) := (main_prod' ha₀pos ha₁pos).mpr h
  rcases this with ⟨p,hp⟩
  exists p; constructor; let g := hp.1; rw [g]; simp;unfold Matrix.dotProduct
  simp; ring
  intro y hy; let g := hp.2 y; simp at g;apply g -- smart!
  rw [hy]; unfold Matrix.dotProduct
  have : a₀ * y 0 + 1 + a₁ * y 1 = a₀ * y 0 + a₁ * y 1 + 1 := by ring
  rw [this]; rfl
}

theorem main_dot_knapsack' {T:ℕ} {a_ : Fin 2 → ℕ} (ha₀pos : 0 < a_ 0) (ha₁pos : 0 < a_ 1)
: (∃! p : Fin 2 → ℕ, T = Matrix.dotProduct a_ p)
↔ (∃! w, walk_in_cursive' a_ w ∧ w T.succ = a_ 0) := -- maybe make it in terms of T to look nicer
by {
  constructor; intro h; rcases h with ⟨p,hp⟩; apply (main_dot' ha₀pos ha₁pos).mp
  exists p; constructor; simp; simp at hp; exact hp.1
  intro y; let g := hp.2 y; simp at g; intro h; simp at h; exact g h

  intro h
  have : (∃! p : Fin 2 → ℕ, T.succ = Matrix.dotProduct a_ p + 1) := (main_dot' ha₀pos ha₁pos).mpr h
  rcases this with ⟨p,hp⟩; exists p; simp; simp at hp; exact hp
}
