import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.Algebra.Order.Floor
import Mathlib.Data.Nat.Log
import Mathlib.InformationTheory.Hamming
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fin.Tuple.Take

set_option tactic.hygienic false
set_option maxHeartbeats 2000000
/-!

  # Hyde's Theorem


-/

open Finset Fintype


section General

/-- if a function f(0)=0, f(k)=k, f(s+1) ≤ f(s) + 1 in between, then f = id
-/
lemma boundFuncAdd {k : ℕ} {f : Fin (k+1) → Fin (k+1)} (a b : Fin (k+1))
    (h₀ : f a = b) (h : ∀ (s : ℕ) (hs : s < k),
      (f (⟨s+1, add_lt_add_right hs 1⟩)).1
    ≤ (f ⟨s, Nat.lt_add_right 1 hs⟩).1 + 1) :
    ∀ (s : ℕ) (hs : s + a < k+1), (f ⟨s + a, hs⟩).1 ≤ s + b.1 := by
    intro s
    induction s with
    | zero =>
      intro hs
      simp
      rw [h₀]
    | succ n ih =>
      intro hs
      have := ih (by linarith)
      calc
       (f ⟨n + 1 + a.1, hs⟩).1 = (f ⟨n + a.1 + 1, by omega⟩).1 := by ring_nf
       _ ≤  (f ⟨n + a.1, by omega⟩).1 + 1 := by
        have := h (n+a.1) (by omega)
        simp_all
       _ ≤ _ := by linarith

lemma id_of_slow {k : ℕ} {f : Fin (k+1) → Fin (k+1)}
    (h₀ : f 0 = 0) (hk : f (Fin.last k) = (Fin.last k))
    (h : ∀ (s : ℕ) (hs : s < k),
      (f (⟨s+1, add_lt_add_right hs 1⟩)).1
    ≤ (f ⟨s, Nat.lt_add_right 1 hs⟩).1 + 1) :
    ∀ (s : ℕ) (hs : s < k), f ⟨s,by omega⟩ = ⟨s,by omega⟩ := by
    by_contra H
    push_neg at H
    obtain ⟨a,hl,ha⟩ := H

    have : (f ⟨a,by linarith⟩).1 < a := by
      have := @boundFuncAdd k f 0 0 h₀ h a (by simp;omega)
      simp at this ha
      contrapose ha
      simp_all
      have : (f ⟨a, by omega⟩).1 = a := by linarith
      exact Eq.symm (Fin.eq_of_val_eq (id (Eq.symm this)))
    let b := (f ⟨a,by linarith⟩).1
    have : (f (Fin.last k)).1 < k := by
      have := @boundFuncAdd k f ⟨a, by omega⟩ ⟨b,by omega⟩ rfl h (k-a)
        (by simp;omega)
      simp at this
      have hka: k - a + a = k := by omega
      simp_rw [hka] at this
      have hkab : k - a + b < k := by omega
      calc _ ≤ k - a + b := by exact this
      _ < k := hkab
    have : (f (Fin.last k)).1 = k := by simp_all
    linarith

end General

/-- p is an accepting path for the word w in the NFA δ. -/
def accepts_word_path {Q A : Type*} {n : ℕ}
    (δ : A → Q → Set Q) (w : Fin n → A) (init : Q) (final : Q) (path : Fin (n+1) → Q) : Prop := by
  exact path 0 = init ∧ path (Fin.last n) = final
   ∧ ∀ i : Fin n, path (⟨i.1+1,by omega⟩) ∈ δ (w i) (path ⟨i.1,by omega⟩)

/-- p is an accepting path for the NFA δ. -/
def accepts_path {Q A : Type*} {n : ℕ}
    (δ : A → Q → Set Q) (init : Q) (final : Q) (path : Fin (n+1) → Q) : Prop := by
  exact path 0 = init ∧ path (Fin.last n) = final
   ∧ ∀ i : Fin (n), ∃ a : A, path (⟨i.1+1,by omega⟩) ∈ δ a (path ⟨i.1,by omega⟩)

lemma accepts_path_of_accepts_word_path {Q A : Type*} {n : ℕ}
    (δ : A → Q → Set Q) (w : Fin n → A) (init : Q) (final : Q) (path : Fin (n+1) → Q)
    (h : accepts_word_path δ w init final path) :
    accepts_path δ init final path :=
  ⟨h.1, h.2.1, fun i => ⟨w i, by simp_all [accepts_word_path]⟩⟩


/-- Kayleigh Hyde's δ. -/
def khδ {A : Type} {k : ℕ} --(hk : k ≥ 1)
  (w : Fin (2*k+1) → A) : A → Fin (k+1) → Set (Fin (k+1)) := by
  let n := 2*k + 1
  intro b q r -- is r reachable in one step from q reading b?
  let b₀ := w ⟨q, by omega⟩ -- go forward
  by_cases H₀ : q.1 = 0
  · by_cases H : q.1 = k
    · exact (b = b₀)-- q = k = 0
    · exact (b = b₀ ∧ r.1 = q.1 + 1)-- q = 0 but not k
  · let b₁ := w ⟨2 * k + 1 - q.1, by omega⟩ -- go backward
    by_cases H : q = k
    · exact (b = b₀ ∧ q.1 = r.1)     ∨ (b = b₁ ∧ r.1 + 1 = q.1)--q = k ≠ 0
    · exact (b = b₀ ∧ r.1 = q.1 + 1) ∨ (b = b₁ ∧ q.1 = r.1 + 1) -- generic case


def kayleighδ {A : Type} {k : ℕ} --(hk : k ≥ 1)
  (w : Fin (2*k+1) → A) : A → Fin (k+1) → Set (Fin (k+1)) := by
  let n := 2*k + 1
  intro b q r -- is r reachable in one step from q reading b?
  -- n = 3, n/2 = 1
  let b₀ := w ⟨q, by omega⟩ -- go forward
  by_cases H₀ : q.1 = 0
  · let P : Prop := (b = b₀ ∧ r.1 = q.1 + 1) --∨ (b = b₁ ∧ q.1 = r.1 + 1)
    exact P
  let b₁ := w ⟨2 * k + 1 - q.1, by
    have : 0 < q.1 := by omega
    omega
    ⟩ -- go backward
-- REALLY, WE SHOULD ALLOW Q = 0 = K HERE
  by_cases H : q = k -- q = 1
  · -- last state
    let P₀ : Prop := (b = b₀ ∧ q.1 = r.1) ∨ (b = b₁ ∧ r.1 + 1 = q.1)
    exact P₀
  · -- last q = 0
    let P : Prop := (b = b₀ ∧ r.1 = q.1 + 1) ∨ (b = b₁ ∧ q.1 = r.1 + 1)
    exact P


theorem move_slowly_kh {A : Type} {k : ℕ} {w : Fin (2 * k + 1) → A}
    {p : Fin (2 * (k + 1)) → Fin (k + 1)}
    (h : accepts_path (@khδ A k w) 0 0 p)
    {s : ℕ} (hs : s < 2 * k + 1) :
    (p ⟨s + 1, by omega⟩).1 ≤ (p ⟨s, by omega⟩).1 + 1 := by
  unfold khδ accepts_path at h
  simp at h
  have := h.2.2 ⟨s,hs⟩
  obtain ⟨a,ha⟩ := this
  split_ifs at ha with g₀ g₁
  · simp at ha
    cases ha ; omega
  · cases ha
    · aesop
  · cases ha
    · aesop
    · have := h_1.2;simp_all
  · cases ha
    · aesop
    · have := h_1.2
      simp_all
      omega

theorem move_slowly {A : Type} {k : ℕ} {w : Fin (2 * k + 1) → A}
    {p : Fin (2 * (k + 1)) → Fin (k + 1)}
    (h : accepts_path (@kayleighδ A k w) 0 0 p)
    {s : ℕ} (hs : s < 2 * k + 1) :
    (p ⟨s + 1, by omega⟩).1 ≤ (p ⟨s, by omega⟩).1 + 1 := by
  unfold kayleighδ accepts_path at h
  simp at h
  have := h.2.2 ⟨s,hs⟩
  obtain ⟨a,ha⟩ := this
  split_ifs at ha with g₀ g₁
  · simp at ha
    cases ha ; omega
  · cases ha
    have := h_1.2
    aesop
    have := h_1.2
    revert this
    simp;omega
  · cases ha
    · aesop
    · have := h_1.2;simp_all;omega



theorem move_slowly_reverse_kh {A : Type} {k : ℕ} {w : Fin (2 * k + 1) → A}
    {p : Fin (2 * (k + 1)) → Fin (k + 1)}
    (h : accepts_path (@khδ A k w) 0 0 p)
    {s : ℕ} (hs : s < 2 * k + 1) :
    (p ⟨s, by omega⟩).1 ≤ (p ⟨s + 1, by omega⟩).1 + 1 := by
  unfold khδ accepts_path at h
  simp at h
  have := h.2.2 ⟨s,hs⟩
  split_ifs at this with g₀
  · simp at this
    obtain ⟨a,ha⟩ := this
    cases ha ; omega
  · cases this with
    | intro a h =>
      simp at h
      cases h ; omega
  · cases this with
  | intro a h =>
    cases h
    have := h_1.2
    simp_all
    simp_all
  · cases this with
  | intro a h =>
    cases h
    have := h_1.2
    simp_all
    omega
    simp_all


theorem move_slowly_reverse {A : Type} {k : ℕ} {w : Fin (2 * k + 1) → A}
    {p : Fin (2 * (k + 1)) → Fin (k + 1)}
    (h : accepts_path (@kayleighδ A k w) 0 0 p)
    {s : ℕ} (hs : s < 2 * k + 1) :
    (p ⟨s, by omega⟩).1 ≤ (p ⟨s + 1, by omega⟩).1 + 1 := by
  unfold kayleighδ accepts_path at h
  simp at h
  have := h.2.2 ⟨s,hs⟩
  split_ifs at this with g₀
  · simp at this
    obtain ⟨a,ha⟩ := this
    cases ha ; omega
  · cases this with
    | intro a h =>
      simp at h
      cases h <;> omega
  · cases this with
  | intro a h =>
    cases h
    have := h_1.2
    simp_all;omega;
    simp_all

theorem kayleighBound_kh {A : Type} {k : ℕ} {w : Fin (2 * k + 1) → A}
    {p : Fin (2 * (k + 1)) → Fin (k + 1)}
    (h : accepts_path (@khδ A k w) 0 0 p) :
    ∀ s, ∀ hs : s < 2*(k+1), (p ⟨s,by omega⟩).1 ≤ s := by
  intro s
  induction s with
  | zero => intro hs;simp;unfold accepts_path at h;aesop
  | succ n ih =>
    intro hs
    have := move_slowly_kh h (show n < 2 * k + 1 by omega)
    have := ih (by omega)
    omega

theorem kayleighBound {A : Type} {k : ℕ} {w : Fin (2 * k + 1) → A}
    {p : Fin (2 * (k + 1)) → Fin (k + 1)}
    (h : accepts_path (@kayleighδ A k w) 0 0 p) :
    ∀ s, ∀ hs : s < 2*(k+1), (p ⟨s,by omega⟩).1 ≤ s := by
  intro s
  induction s with
  | zero => intro hs;simp;unfold accepts_path at h;aesop
  | succ n ih =>
    intro hs
    have := move_slowly h (show n < 2 * k + 1 by omega)
    have := ih (by omega)
    omega


theorem kayleighBound_lower_kh {A : Type} {k : ℕ} (w : Fin (2 * k + 1) → A)
    (p : Fin (2 * (k + 1)) → Fin (k + 1))
    (h : accepts_path (@khδ A k w) 0 0 p) :
    ∀ (s : ℕ) (hs : s < 2 * k + 1),
    (p ⟨s + 1, by omega⟩).1 ≥ (p ⟨s, by omega⟩).1 - 1 := by
      intro s
      induction s with
      | zero =>
        intro hs
        simp
        unfold accepts_path khδ at h
        rw [h.1]
        simp
      | succ n ih =>
        intro hs
        have := ih (by omega)
        unfold accepts_path at h
        obtain ⟨a,ha⟩ := h.2.2 ⟨n+1,hs⟩
        unfold khδ at ha
        simp at ha
        split_ifs at ha <;> cases ha <;> omega


theorem kayleighBound_lower {A : Type} {k : ℕ} (w : Fin (2 * k + 1) → A)
    (p : Fin (2 * (k + 1)) → Fin (k + 1))
    (h : accepts_path (@kayleighδ A k w) 0 0 p) :
    ∀ (s : ℕ) (hs : s < 2 * k + 1),
    (p ⟨s + 1, by omega⟩).1 ≥ (p ⟨s, by omega⟩).1 - 1 := by
      intro s
      induction s with
      | zero =>
        intro hs
        simp
        unfold accepts_path kayleighδ at h
        rw [h.1]
        simp
      | succ n ih =>
        intro hs
        have := ih (by omega)
        unfold accepts_path at h
        obtain ⟨a,ha⟩ := h.2.2 ⟨n+1,hs⟩
        unfold kayleighδ at ha
        simp at ha
        split_ifs at ha <;> cases ha <;> omega


/-- If the Kayleigh graph ever uses the loop, we know when! -/
theorem hyde_loop_when_kh {A : Type} {k : ℕ}
    (w : Fin (2 * k + 1) → A)
    (p : Fin (2 * (k + 1)) → Fin (k + 1))
    (h : accepts_path (@khδ A k w) 0 0 p) (t : Fin (2 * k + 1))
    (ht : p ⟨t.1,by omega⟩ = Fin.last k ∧ p (⟨t.1+1, by omega⟩) = Fin.last k) :
    t = ⟨k, by omega⟩ := by
  by_contra H
  have : t.1 < k ∨ t.1 > k := by
    have : t.1 ≠ k := by
      intro hc
      apply H
      exact Fin.eq_mk_iff_val_eq.mpr hc
    exact Nat.lt_or_gt_of_ne this
  cases this
  · have : (p ⟨t.1,by omega⟩).1 < k := by
      have : ∀ s, ∀ hs : s < 2*k+1, (p (⟨s+1,by omega⟩)).1 ≤ p ⟨s,by omega⟩ + 1 := by
        apply move_slowly_kh; tauto
      have : ∀ s, ∀ hs : s < 2*(k+1), (p ⟨s,by omega⟩).1 ≤ s := by
        apply kayleighBound_kh; tauto
      have := this t.1 (by omega)
      omega
    rw [ht.1] at this
    simp at this
  · have g₀ : t.1 < 2*k + 1 := by
      by_contra H
      have ht2 := t.2
      have ht : t.1 = 2*k+1 := by omega
      unfold accepts_path khδ at h
      have := h.2.1
      rw [ht] at H
      have : p ⟨t.1,by omega⟩ = 0 := by
        rw [← this]; congr
      have : Fin.last k = 0 := by aesop
      have : k = 0 := by exact Fin.last_eq_zero_iff.mp this
      omega
    have : ∀ s, ∀ hs : s < 2*k+1, (p (⟨s+1,by omega⟩)).1 ≥ p ⟨s,by omega⟩ - 1 := by
      apply kayleighBound_lower_kh
      tauto
    have : ∀ s,
      ∀ hs : s < 2 * k+1 - t.1, -- t + s < 2(k+1)
      (p (⟨t.1 + 1 + s, by omega⟩)).1 ≥ k - s := by
      intro s
      induction s with
      | zero =>
        intro h
        simp_all
      | succ s ih =>
        intro h₂
        have h₀ := ih (by omega)
        have h₁ := this (t.1 + s + 1) (by have := t.2;omega)
        simp_all
        calc
        _ ≤ _ := h₀
        _ ≤  (p ⟨t.1 + s + 2, by omega⟩).1 + 1 + s := by ring_nf;ring_nf at h₁;omega
        _ ≤ _ := by ring_nf;omega
    have := this (2*k+1-(t+1)) (by omega)
    simp at this
    have hsmile: 2 * k - t.1 ≥ 0 := by omega
    have :  k ≤ (p ⟨t.1 + 1 + (2 * k - ↑t), by omega⟩).1 + (2 * k - t.1) := this
    have :  k - (2*k - t.1) ≤ (p ⟨t.1 + 1 + (2 * k - t.1), by omega⟩).1 := Nat.sub_le_of_le_add this
    have h₀ :  1 ≤ (p ⟨t.1 + 1 + (2 * k - t.1), by omega⟩).1 := by omega
    have : t.1 + 1 + (2 * k - t.1) = 2*k+1 := by omega
    have h₁ :  1 ≤ (p ⟨2 * k + 1, by omega⟩).1 := by
      simp_rw [this] at h₀
      exact h₀
    unfold accepts_path at h
    have := h.2.1
    change 1 ≤ (p (Fin.last (2*k+1))).1 at h₁
    simp_all


/-- If the Kayleigh graph ever uses the loop, we know when! -/
theorem hyde_loop_when {A : Type} {k : ℕ}
    (w : Fin (2 * k + 1) → A)
    (p : Fin (2 * (k + 1)) → Fin (k + 1))
    (h : accepts_path (@kayleighδ A k w) 0 0 p) (t : Fin (2 * k + 1))
    (ht : p ⟨t.1,by omega⟩ = Fin.last k ∧ p (⟨t.1+1, by omega⟩) = Fin.last k) :
    t = ⟨k, by omega⟩ := by
  by_contra H
  have : t.1 < k ∨ t.1 > k := by
    have : t.1 ≠ k := by
      intro hc
      apply H
      exact Fin.eq_mk_iff_val_eq.mpr hc
    exact Nat.lt_or_gt_of_ne this
  cases this
  · have : (p ⟨t.1,by omega⟩).1 < k := by
      have : ∀ s, ∀ hs : s < 2*k+1, (p (⟨s+1,by omega⟩)).1 ≤ p ⟨s,by omega⟩ + 1 := by
        apply move_slowly; tauto
      have : ∀ s, ∀ hs : s < 2*(k+1), (p ⟨s,by omega⟩).1 ≤ s := by
        apply kayleighBound; tauto
      have := this t.1 (by omega)
      omega
    rw [ht.1] at this
    simp at this
  · have g₀ : t.1 < 2*k + 1 := by
      by_contra H
      have ht2 := t.2
      have ht : t.1 = 2*k+1 := by omega
      unfold accepts_path kayleighδ at h
      have := h.2.1
      rw [ht] at H
      have : p ⟨t.1,by omega⟩ = 0 := by
        rw [← this]; congr
      have : Fin.last k = 0 := by aesop
      have : k = 0 := by exact Fin.last_eq_zero_iff.mp this
      omega
    have : ∀ s, ∀ hs : s < 2*k+1, (p (⟨s+1,by omega⟩)).1 ≥ p ⟨s,by omega⟩ - 1 := by
      apply kayleighBound_lower
      tauto
    have : ∀ s,
      ∀ hs : s < 2 * k+1 - t.1, -- t + s < 2(k+1)
      (p (⟨t.1 + 1 + s, by omega⟩)).1 ≥ k - s := by
      intro s
      induction s with
      | zero =>
        intro h
        simp_all
      | succ s ih =>
        intro h₂
        have h₀ := ih (by omega)
        have h₁ := this (t.1 + s + 1) (by have := t.2;omega)
        simp_all
        calc
        _ ≤ _ := h₀
        _ ≤  (p ⟨t.1 + s + 2, by omega⟩).1 + 1 + s := by ring_nf;ring_nf at h₁;omega
        _ ≤ _ := by ring_nf;omega
    have := this (2*k+1-(t+1)) (by omega)
    simp at this
    have hsmile: 2 * k - t.1 ≥ 0 := by omega
    have :  k ≤ (p ⟨t.1 + 1 + (2 * k - ↑t), by omega⟩).1 + (2 * k - t.1) := this
    have :  k - (2*k - t.1) ≤ (p ⟨t.1 + 1 + (2 * k - t.1), by omega⟩).1 := Nat.sub_le_of_le_add this
    have h₀ :  1 ≤ (p ⟨t.1 + 1 + (2 * k - t.1), by omega⟩).1 := by omega
    have : t.1 + 1 + (2 * k - t.1) = 2*k+1 := by omega
    have h₁ :  1 ≤ (p ⟨2 * k + 1, by omega⟩).1 := by
      simp_rw [this] at h₀
      exact h₀
    unfold accepts_path at h
    have := h.2.1
    change 1 ≤ (p (Fin.last (2*k+1))).1 at h₁
    simp_all


open Nat

theorem hyde_parity_kh {A : Type} {k : ℕ} (w : Fin (2 * k + 1) → A) (p : Fin (2 * (k + 1)) → Fin (k + 1))
  (h : accepts_path (@khδ A k w) 0 0 p)
  (H : ¬ ∃ t : Fin (2*k+1), p ⟨t.1,by omega⟩ = Fin.last k ∧ p (⟨t.1+1, by omega⟩) = Fin.last k) :
  ∀ (t : ℕ) (ht : t < 2 * (k + 1)), (p ⟨t, ht⟩).1 % 2 = t % 2 := by
      push_neg at H
      intro t
      induction t with
      | zero =>
        simp
        simp [kayleighδ,accepts_path] at h
        rw [h.1]
        simp
      | succ n ih =>
        intro ht
        have h₀ := ih (by omega)
        have h₁ := h.2.2 ⟨n, by simp_all; omega⟩
        simp [khδ] at h₁ -- timed out
        obtain ⟨a,h₁⟩ := h₁
        split_ifs at h₁ with g₀ g₂ g₁
        · have : k = 0 := by omega
          subst this
          simp_all
          have := H (by omega)
          exfalso
          apply this
          apply Fin.mk.inj_iff.mpr
          simp
        · have why := h₁.2
          simp_rw [g₀] at why h₀
          rw [why]
          aesop
        · cases h₁ with
        | inl h₁ =>
          have why := h₁.2
          rw [← why]
          specialize H ⟨n, by omega⟩ g₁
          exfalso
          apply H
          apply Fin.eq_of_val_eq
          rw [← why]
          aesop
        | inr h₁ =>
          have why := h₁.2
          simp_rw [g₁] at why
          cases mod_two_eq_zero_or_one (p ⟨n + 1, ht⟩).1
          · rw [h_1]
            apply congrArg (fun x => x % 2) at why
            rw [add_mod] at why
            rw [h_1] at why
            simp at why
            have : (p ⟨n,by omega⟩).1 = k := by
              exact (@Fin.mk.inj_iff (k+1) (p ⟨n, by omega⟩).1 k (by omega) (by omega)).mp
                (by tauto)
            apply congrArg (fun x => x % 2) at this
            rw [this, ← why] at h₀
            clear this why h_1 h₁ g₁ g₀ a
            rw [add_mod, h₀]
            simp
            rw [← two_mul]
            simp
          · rw [h_1]
            apply congrArg (fun x => x % 2) at why
            rw [add_mod] at why
            rw [h_1] at why
            simp at why
            have : (p ⟨n,by omega⟩).1 = k := by
              exact (@Fin.mk.inj_iff (k+1) (p ⟨n, by omega⟩).1 k (by omega) (by omega)).mp
                (by tauto)
            apply congrArg (fun x => x % 2) at this
            rw [this, ← why] at h₀
            rw [add_mod, ← h₀]
        · cases h₁
          · have why := h_1.2
            rw [why, add_mod, h₀, ← add_mod]
          · have why := h_1.2
            apply congrArg (fun x => x % 2) at why
            simp_rw [h₀] at why
            clear h_1 g₁ g₀
            symm at why
            rw [add_mod]
            rw [← why]
            simp
            rw [add_assoc]
            simp



theorem hyde_parity {A : Type} {k : ℕ} (w : Fin (2 * k + 1) → A) (p : Fin (2 * (k + 1)) → Fin (k + 1))
  (h : accepts_path (@kayleighδ A k w) 0 0 p)
  (H : ¬ ∃ t : Fin (2*k+1), p ⟨t.1,by omega⟩ = Fin.last k ∧ p (⟨t.1+1, by omega⟩) = Fin.last k) :
  ∀ (t : ℕ) (ht : t < 2 * (k + 1)), (p ⟨t, ht⟩).1 % 2 = t % 2 := by
      push_neg at H
      intro t
      induction t with
      | zero =>
        simp
        simp [kayleighδ,accepts_path] at h
        rw [h.1]
        simp
      | succ n ih =>
        intro ht
        have h₀ := ih (by omega)
        have h₁ := h.2.2 ⟨n, by simp_all; omega⟩
        simp [kayleighδ] at h₁ -- timed out
        obtain ⟨a,h₁⟩ := h₁
        split_ifs at h₁ with g₀ g₁
        · have why := h₁.2
          simp_rw [g₀] at why h₀
          rw [why]
          aesop
        · cases h₁ with
        | inl h₁ =>
          have why := h₁.2
          rw [← why]
          specialize H ⟨n, by omega⟩ g₁
          exfalso
          apply H
          apply Fin.eq_of_val_eq
          rw [← why]
          aesop
        | inr h₁ =>
          have why := h₁.2
          simp_rw [g₁] at why
          cases mod_two_eq_zero_or_one (p ⟨n + 1, ht⟩).1
          · rw [h_1]
            apply congrArg (fun x => x % 2) at why
            rw [add_mod] at why
            rw [h_1] at why
            simp at why
            have : (p ⟨n,by omega⟩).1 = k := by
              exact (@Fin.mk.inj_iff (k+1) (p ⟨n, by omega⟩).1 k (by omega) (by omega)).mp
                (by tauto)
            apply congrArg (fun x => x % 2) at this
            rw [this, ← why] at h₀
            clear this why h_1 h₁ g₁ g₀ a
            rw [add_mod, h₀]
            simp
            rw [← two_mul]
            simp
          · rw [h_1]
            apply congrArg (fun x => x % 2) at why
            rw [add_mod] at why
            rw [h_1] at why
            simp at why
            have : (p ⟨n,by omega⟩).1 = k := by
              exact (@Fin.mk.inj_iff (k+1) (p ⟨n, by omega⟩).1 k (by omega) (by omega)).mp
                (by tauto)
            apply congrArg (fun x => x % 2) at this
            rw [this, ← why] at h₀
            rw [add_mod, ← h₀]
        · cases h₁
          · have why := h_1.2
            rw [why, add_mod, h₀, ← add_mod]
          · have why := h_1.2
            apply congrArg (fun x => x % 2) at why
            simp_rw [h₀] at why
            clear h_1 g₁ g₀
            symm at why
            rw [add_mod]
            rw [← why]
            simp
            rw [add_assoc]
            simp


theorem move_slowly_rev_aux_kh {A : Type} {k : ℕ} (w : Fin (2 * k + 1) → A)
(p : Fin (2 * (k + 1)) → Fin (k + 1))
    (h : accepts_path (@khδ A k w) 0 0 p) (s₁ : ℕ) (hs₁ : s₁ < k) :
    k ≤ k - ↑(p ⟨s₁ + k + 1, by omega⟩) + 1 + ↑(p ⟨s₁ + 1 + k + 1, by omega⟩) := by
  suffices k ≤ k + 1 + (p ⟨s₁ + 1 + k + 1, by omega⟩).1  - (p ⟨s₁ + k + 1, by omega⟩).1 by omega
  simp_rw [show s₁ + 1 + k + 1 = s₁ + k + 1 + 1 by ring]
  have hmo := @move_slowly_reverse_kh _ k w p h (s₁ + k + 1) (by omega)
  have : k + (1 + (p ⟨s₁ + k + 1 + 1, by omega⟩).1 - (p ⟨s₁ + k + 1, by omega⟩).1)
    = k + 1 + (p ⟨s₁ + k + 1 + 1, by omega⟩).1 - (p ⟨s₁ + k + 1, by omega⟩).1 := by
    apply Nat.eq_sub_of_add_eq'
    omega
  rw [← this]
  apply Nat.le_add_right


theorem move_slowly_rev_aux {A : Type} {k : ℕ} (w : Fin (2 * k + 1) → A)
(p : Fin (2 * (k + 1)) → Fin (k + 1))
    (h : accepts_path (@kayleighδ A k w) 0 0 p) (s₁ : ℕ) (hs₁ : s₁ < k) :
    k ≤ k - ↑(p ⟨s₁ + k + 1, by omega⟩) + 1 + ↑(p ⟨s₁ + 1 + k + 1, by omega⟩) := by
  suffices k ≤ k + 1 + (p ⟨s₁ + 1 + k + 1, by omega⟩).1  - (p ⟨s₁ + k + 1, by omega⟩).1 by omega
  simp_rw [show s₁ + 1 + k + 1 = s₁ + k + 1 + 1 by ring]
  have hmo := @move_slowly_reverse _ k w p h (s₁ + k + 1) (by omega)
  have : k + (1 + (p ⟨s₁ + k + 1 + 1, by omega⟩).1 - (p ⟨s₁ + k + 1, by omega⟩).1)
    = k + 1 + (p ⟨s₁ + k + 1 + 1, by omega⟩).1 - (p ⟨s₁ + k + 1, by omega⟩).1 := by
    apply Nat.eq_sub_of_add_eq'
    omega
  rw [← this]
  apply Nat.le_add_right

/-- Hyde's theorem (2013). -/
theorem hyde_unique_path_kh {A : Type} {k : ℕ} (w : Fin (2*k+1) → A)
  (p : Fin (2*(k+1)) → Fin (k+1))
  (h : accepts_path (@khδ A k w) 0 0 p) :
  p = fun t : Fin (2*(k+1)) => dite (t.1 ≤ k)
    (fun ht => (⟨t.1,     Order.lt_add_one_iff.mpr ht⟩ : Fin (k+1)))
    (fun ht => (⟨2*k+1-t.1,by omega⟩ : Fin (k+1)))  := by
  by_cases H : ∃ t : Fin (2*k+1), p ⟨t.1,by omega⟩ = Fin.last k ∧ p (⟨t.1+1, by omega⟩) = Fin.last k -- we use the loop
  · obtain ⟨t,ht⟩ := H
    have : t = ⟨k,by omega⟩ := by apply hyde_loop_when_kh <;> tauto
    ext s
    split_ifs with g₀
    · by_cases hh : s.1 = k
      · have : s = ⟨k, by omega⟩ := Eq.symm (Fin.eq_of_val_eq (id (Eq.symm hh)))
        aesop
      have := @id_of_slow k (fun x => p ⟨x.1,by have := x.2;linarith⟩)
        (by simp;unfold accepts_path at h;tauto) (by simp;aesop)
        (by
          intro s hs;simp
          exact @move_slowly_kh _ k w p h s (by omega)
        ) s (by omega)
      simp at this
      rw [this]
    · -- the same as the other case but in opposite order...
      rw [this] at ht
      clear this
      simp at g₀
      by_cases hh : s.1 = 2 * k + 1
      · unfold accepts_path at h
        have h₁ := h.2.1
        simp_rw [hh]
        simp
        have h₀ : s = Fin.last (2*k+1) := Eq.symm (Fin.eq_of_val_eq (id (Eq.symm hh)))
        rw [h₀]
        exact (@Fin.mk.inj_iff ((k+1)) (p (Fin.last (2*k+1))).1 0
          (by omega) (by omega)).mp h₁

      let f : Fin ((k+1)) → Fin ((k+1)) :=
        fun u  => ⟨k - (p ⟨u + k + 1,by omega⟩).1, by omega⟩

      simp
      suffices (f ⟨s.1 - (k+1),by omega⟩).1 = s.1 - (k+1) by
        unfold f at this
        simp at this
        have h₀ : s.1 - (k+1) + k + 1 = s.1 := by omega
        simp_rw [h₀] at this
        change k - (p s).1 = s.1 - (k+1) at this
        omega
      have := @id_of_slow k (fun x => ⟨(f ⟨x, by omega⟩).1, by
        unfold f
        simp;omega
      ⟩) (by
        simp;unfold f;
        simp_all
      ) (by
        simp;unfold f;
        unfold accepts_path at h
        have := h.2.1
        simp at this
        have hp : p (Fin.last (2 * k + 1)) = p ⟨k+k+1, by omega⟩ := by
          congr
          unfold Fin.last
          simp
          apply two_mul
        simp_rw [← hp]
        simp_rw [this]
        rfl
        ) (by
          intro s₁ hs₁
          simp
          apply move_slowly_rev_aux_kh <;> tauto
        ) (s - (k+1)) (by
          omega
        )
      simp_all
  · have : ∀ (t : ℕ) (ht : t < 2 * (k+1)), (p ⟨t,ht⟩).1 % 2 = t % 2 := by
      apply hyde_parity_kh <;> tauto

    have : p (Fin.last (2*k+1)) ≠ 0 := by
      intro hc
      have := this (Fin.last (2*k+1)) (by omega)
      simp at this
      rw [hc] at this
      revert this
      simp
      intro hc
      symm at hc
      revert hc
      simp
      show  ¬(2 * k + 1) % 2 = ↑(p (Fin.last (2 * k + 1))) % 2
      rw [hc]
      simp
      apply succ_mod_two_eq_one_iff.mpr
      simp
    exfalso
    unfold accepts_path at h
    tauto


/-- Hyde's theorem (2013). -/
theorem hyde_unique_path {A : Type} {k : ℕ} (w : Fin (2*k+1) → A)
  (p : Fin (2*(k+1)) → Fin (k+1))
  (h : accepts_path (@kayleighδ A k w) 0 0 p) :
  p = fun t : Fin (2*(k+1)) => dite (t.1 ≤ k)
    (fun ht => (⟨t.1,     Order.lt_add_one_iff.mpr ht⟩ : Fin (k+1)))
    (fun ht => (⟨2*k+1-t.1,by omega⟩ : Fin (k+1)))  := by
  by_cases H : ∃ t : Fin (2*k+1), p ⟨t.1,by omega⟩ = Fin.last k ∧ p (⟨t.1+1, by omega⟩) = Fin.last k -- we use the loop
  · obtain ⟨t,ht⟩ := H
    have : t = ⟨k,by omega⟩ := by apply hyde_loop_when <;> tauto
    ext s
    split_ifs with g₀
    · by_cases hh : s.1 = k
      · have : s = ⟨k, by omega⟩ := Eq.symm (Fin.eq_of_val_eq (id (Eq.symm hh)))
        aesop
      have := @id_of_slow k (fun x => p ⟨x.1,by have := x.2;linarith⟩)
        (by simp;unfold accepts_path at h;tauto) (by simp;aesop)
        (by
          intro s hs;simp
          exact @move_slowly _ k w p h s (by omega)
        ) s (by omega)
      simp at this
      rw [this]
    · -- the same as the other case but in opposite order...
      rw [this] at ht
      clear this
      simp at g₀
      by_cases hh : s.1 = 2 * k + 1
      · unfold accepts_path at h
        have h₁ := h.2.1
        simp_rw [hh]
        simp
        have h₀ : s = Fin.last (2*k+1) := Eq.symm (Fin.eq_of_val_eq (id (Eq.symm hh)))
        rw [h₀]
        exact (@Fin.mk.inj_iff ((k+1)) (p (Fin.last (2*k+1))).1 0
          (by omega) (by omega)).mp h₁

      let f : Fin ((k+1)) → Fin ((k+1)) :=
        fun u  => ⟨k - (p ⟨u + k + 1,by omega⟩).1, by omega⟩

      simp
      suffices (f ⟨s.1 - (k+1),by omega⟩).1 = s.1 - (k+1) by
        unfold f at this
        simp at this
        have h₀ : s.1 - (k+1) + k + 1 = s.1 := by omega
        simp_rw [h₀] at this
        change k - (p s).1 = s.1 - (k+1) at this
        omega
      have := @id_of_slow k (fun x => ⟨(f ⟨x, by omega⟩).1, by
        unfold f
        simp;omega
      ⟩) (by
        simp;unfold f;
        simp_all
      ) (by
        simp;unfold f;
        unfold accepts_path at h
        have := h.2.1
        simp at this
        have hp : p (Fin.last (2 * k + 1)) = p ⟨k+k+1, by omega⟩ := by
          congr
          unfold Fin.last
          simp
          apply two_mul
        simp_rw [← hp]
        simp_rw [this]
        rfl
        ) (by
          intro s₁ hs₁
          simp
          apply move_slowly_rev_aux <;> tauto
        ) (s - (k+1)) (by
          omega
        )
      simp_all
  · have : ∀ (t : ℕ) (ht : t < 2 * (k+1)), (p ⟨t,ht⟩).1 % 2 = t % 2 := by
      apply hyde_parity <;> tauto

    have : p (Fin.last (2*k+1)) ≠ 0 := by
      intro hc
      have := this (Fin.last (2*k+1)) (by omega)
      simp at this
      rw [hc] at this
      revert this
      simp
      intro hc
      symm at hc
      revert hc
      simp
      show  ¬(2 * k + 1) % 2 = ↑(p (Fin.last (2 * k + 1))) % 2
      rw [hc]
      simp
      apply succ_mod_two_eq_one_iff.mpr
      simp
    exfalso
    unfold accepts_path at h
    tauto


/-- Hyde's theorem (2013). -/
theorem hyde_unique_path'''_kh {A : Type} {k : ℕ} (w v : Fin (2*k+1) → A)
  (p : Fin (2*(k+1)) → Fin (k+1))
  (h : accepts_word_path (@khδ A k w) v 0 0 p) :
  p = fun t : Fin (2*(k+1)) => dite (t.1 ≤ k)
    (fun ht => (⟨t.1,     Order.lt_add_one_iff.mpr ht⟩ : Fin (k+1)))
    (fun ht => (⟨2*k+1-t.1,by omega⟩ : Fin (k+1)))  := by
  apply hyde_unique_path_kh
  apply accepts_path_of_accepts_word_path <;> tauto


/-- Hyde's theorem (2013). -/
theorem hyde_unique_path''' {A : Type} {k : ℕ} (w v : Fin (2*k+1) → A)
  (p : Fin (2*(k+1)) → Fin (k+1))
  (h : accepts_word_path (@kayleighδ A k w) v 0 0 p) :
  p = fun t : Fin (2*(k+1)) => dite (t.1 ≤ k)
    (fun ht => (⟨t.1,     Order.lt_add_one_iff.mpr ht⟩ : Fin (k+1)))
    (fun ht => (⟨2*k+1-t.1,by omega⟩ : Fin (k+1)))  := by
  apply hyde_unique_path
  apply accepts_path_of_accepts_word_path <;> tauto


theorem hyde_unique_word {A : Type} {k : ℕ} (w v : Fin (2*k+1) → A)
    (p : Fin (2*(k+1)) → Fin (k+1))
    (ha : accepts_word_path (@kayleighδ A k w) v 0 0 p) :
    w = v := by
  ext ⟨i,hi⟩
  have hup := hyde_unique_path''' w v p ha
  subst hup
  unfold accepts_word_path kayleighδ at ha
  simp at ha
  have h₂ := ha.2 ⟨i, hi⟩
  split_ifs at h₂ with g₀ g₁ g₂ g₃ g₄
  · -- g₀: i ≤ k; g₁ : i = 0
    simp_all; symm
    change v 0 = w 0 ∧ (@dite (Fin (k + 1)) (1 ≤ k) (decLe 1 k) (fun h ↦ ⟨1, by omega⟩) fun h ↦ ⟨2 * k, by omega⟩).1 =1 at h₂
    tauto
  · -- g₀: i ≤ k; g₁ : i ≠ 0; g₂: i = k
    simp_all
    simp at g₀ g₂
    have : i = k := by exact Fin.mk.inj_iff.mp g₂
    have : ¬ i + 1 ≤ k := by omega
    simp_all
    have : 2 * k - k = k := by omega
    conv at h₂ =>
      right
      left
      rw [this]

    change  v ⟨k, by omega⟩ = w ⟨k, by omega⟩ ∧ k = k
      ∨ v ⟨k, by omega⟩ = w ⟨2 * k + 1 - k, by omega⟩ ∧ k + 1 = k at h₂
    cases h₂
    symm
    tauto
    exfalso
    have := h.2
    simp at this
  · -- g₀: i ≤ k; g₁ : i ≠ 0; g₂ : i ≠ k
    have : i ≤ k := by exact g₀
    have : i ≠ k := by
      intro hc
      apply g₂
      exact Fin.mk.inj_iff.mpr hc
    have : i + 1 ≤ k := by
      omega
    simp_all
    cases h₂
    symm
    tauto
    exfalso
    have := h.2
    simp at this
    omega
  · -- g₀ : ¬ i ≤ k; g₃ : 2k+1-i=0
    simp_all
    have : ¬ i ≤ k := by exact g₀
    have : ¬ i + 1 ≤ k := by omega
    simp_all
    exfalso
    omega
  · -- g₀ : ¬ i ≤ k; g₃ : 2k+1-i≠ 0; g₄: 2k+1-i=k
    simp_all
    have : ¬ i ≤ k := by exact g₀
    have : ¬ i + 1 ≤ k := by omega
    simp_all
    change
      v ⟨i, hi⟩ = w ⟨2 * k + 1 - i, by omega⟩ ∧ 2 * k + 1 - i = 2 * k - i ∨
      v ⟨i, hi⟩ = w ⟨2 * k + 1 - (2 * k + 1 - i), by omega⟩ ∧ 2 * k - i + 1 = 2 * k + 1 - i
      at h₂
    cases h₂
    · exfalso
      omega
    · have : ¬ i ≤ k := g₀
      have : ⟨2 * k + 1 - i, by
        suffices 2 * k + 1 < k + 1 + i by omega
        rw [two_mul]
        suffices k + 1 < 1 + i by omega
        suffices k < i by omega
        omega
      ⟩ = (Fin.last k : Fin (k+1)) := by tauto
      have : 2 * k + 1 - i = k := by
        exact Fin.mk.inj_iff.mp this
      simp_rw [this] at h
      have : i = k + 1 := by omega
      subst this
      symm
      have : 2 * k + 1 - k = k + 1 := by omega
      simp_rw [this] at h
      tauto
  · -- g₀ : ¬ i ≤ k; g₃ : 2k+1-i≠ 0; g₄: 2k+1-i≠ k
    simp_all
    have : ¬ i ≤ k := by exact g₀
    have : ¬ i + 1 ≤ k := by omega
    simp_all
    change
      v ⟨i, hi⟩ = w ⟨2 * k + 1 - i, by omega⟩ ∧ 2 * k - i = 2 * k + 1 - i + 1 ∨
      v ⟨i, hi⟩ = w ⟨2 * k + 1 - (2 * k + 1 - i), by omega⟩ ∧ 2 * k + 1 - i = 2 * k - i + 1 at h₂
    cases h₂
    exfalso
    omega
    -- finally... the reward
    have : 2 * k + 1 - (2 * k + 1 - i) = i := by omega
    simp_rw [this] at h
    symm;tauto


theorem aux₀ {A : Type} {k : ℕ} (w v : Fin (2 * k + 1) → A) (i : ℕ) (hi : i < 2 * k + 1) (g₀ : ¬ i ≤ k)
  (g₄ : ¬ 2 * k + 1 - i = 0) (g₆ : ⟨2 * k + 1 - i, by omega⟩ = Fin.last k) (this_1 : ¬i + 1 ≤ k) (this : k < i + 1)
  (h₂ :
    v ⟨i, hi⟩ = w ⟨2 * k + 1 - i, by omega⟩ ∧ 2 * k + 1 - i = 2 * k - i ∨
      v ⟨i, hi⟩ = w ⟨2 * k + 1 - (2 * k + 1 - i), by omega⟩ ∧ 2 * k - i + 1 = 2 * k + 1 - i) :
  w ⟨i, hi⟩ = v ⟨i, hi⟩ := by

    cases h₂
    · omega
    · have : ¬ i ≤ k := g₀
      have : ⟨2 * k + 1 - i, by omega⟩ = (Fin.last k : Fin (k+1)) := by tauto
      have : 2 * k + 1 - i = k := Fin.mk.inj_iff.mp this
      simp_rw [this] at h
      have : i = k + 1 := by omega
      subst this
      symm
      have : 2 * k + 1 - k = k + 1 := by omega
      simp_rw [this] at h
      tauto

theorem hyde_unique_word_kh {A : Type} {k : ℕ} (w v : Fin (2*k+1) → A)
    (p : Fin (2*(k+1)) → Fin (k+1))
    (ha : accepts_word_path (@khδ A k w) v 0 0 p) :
    w = v := by
  ext ⟨i,hi⟩
  have hup := hyde_unique_path'''_kh w v p ha
  subst hup
  unfold accepts_word_path khδ at ha
  simp at ha
  have h₂ := ha.2 ⟨i, hi⟩
  clear ha
  have case1 (g₀ : i ≤ k) (g₁ : i=0) (g₂ : i=k) : w ⟨i,hi⟩ = v ⟨i,hi⟩ := by
    subst g₁
    simp_all
    exact h₂.symm
  have case3 (g₀ : i ≤ k) (g₁ : i≠ 0) (g₃ : ⟨i,by omega⟩= Fin.last k) : w ⟨i,hi⟩ = v ⟨i,hi⟩ := by
    have : i = k := Fin.mk.inj_iff.mp g₃
    subst this
    simp_all
    cases h₂
    · tauto
    · simp at h
      omega
  have case4 (g₀ : i ≤ k) (g₁ : i≠ 0) (g₃ : ¬ ⟨i,by omega⟩= Fin.last k) : w ⟨i,hi⟩ = v ⟨i,hi⟩ := by
    have : i ≤ k := g₀
    have : i ≠ k := fun hc => g₃ <| Fin.mk.inj_iff.mpr hc
    have : i + 1 ≤ k := by omega
    simp_all
    cases h₂
    · tauto
    · have := h.2
      simp at this
      omega
  have case5 (g₀ : ¬ i ≤ k) (g₄ : 2*k+1-i=0) (g₅: 2*k+1-i=k) : w ⟨i,hi⟩ = v ⟨i,hi⟩ := by
    have : ¬ i ≤ k := by exact g₀
    have : ¬ i + 1 ≤ k := by omega
    simp_all
    omega
  have case6 (g₀ : ¬ i ≤ k) (g₄ : 2*k+1-i=0) (g₅: 2*k+1-i≠ k) : w ⟨i,hi⟩ = v ⟨i,hi⟩ := by
    have : ¬ i ≤ k := by exact g₀
    have : ¬ i + 1 ≤ k := by omega
    simp_all
    omega
  split_ifs at h₂ with g₀ g₁ g₂ g₃ g₄ g₅ g₆
  · apply case1 <;> tauto
  · exact h₂.1.symm
  · apply case3 <;> tauto
  · apply case4 <;> tauto
  · apply case5 <;> tauto
  · apply case6 <;> tauto
  · -- g₀ : ¬ i ≤ k; g₃ : 2k+1-i≠ 0; g₄: 2k+1-i=k
    simp_all
    have : ¬ i ≤ k := g₀
    have : ¬ i + 1 ≤ k := by omega
    simp_all
    apply aux₀ <;> tauto
  · have : ¬ i ≤ k := g₀
    have : ¬ i + 1 ≤ k := by omega
    simp_all
    cases h₂
    · have : 2 * k - i = 2 * k + 1 - i + 1 := h.2
      omega
    · have : 2 * k + 1 - (2 * k + 1 - i) = i := by omega
      simp_rw [this] at h
      tauto


theorem hyde_accepts_kh {A : Type} {k : ℕ}  (w : Fin (2*k+1) → A) :
  accepts_word_path (@khδ A k w) w 0 0 fun t : Fin (2*(k+1)) => dite (t.1 ≤ k)
    (fun ht => (⟨t.1,     Order.lt_add_one_iff.mpr ht⟩ : Fin (k+1)))
    (fun ht => (⟨2*k+1-t.1,by omega⟩ : Fin (k+1))) := by
  unfold khδ accepts_word_path
  simp
  constructor
  · intro h
    exfalso
    omega
  · intro i
    split_ifs with g₀ g₁ g₂ g₃ g₄ g₅ g₆
    · -- new
      simp at g₁ g₂
      have : i = 0 := by exact Eq.symm (Fin.eq_of_val_eq (id (Eq.symm g₁)))
      subst this
      have : k = 0 := by exact id (Eq.symm g₂)
      subst this
      simp
      trivial
    · simp_all
      have : 1 ≤ k := by omega
      simp_all
      show w ⟨i,by omega⟩ = w 0 ∧ 1 = 1
      simp_all
    · simp_all
      have : i.1 = k := Fin.mk.inj_iff.mp g₃
      simp_rw [this]
      simp
      show k = 2 * k - k ∨ w i = w ⟨2 * k + 1 - k, by omega⟩ ∧ 2 * k - k + 1 = k
      left
      omega
    · have : ¬ i.1 = k := by
        intro hc
        apply g₃
        exact Fin.mk.inj_iff.mpr hc
      have : i.1 ≤ k := by exact g₀
      have : i.1 + 1 ≤ k := by omega
      simp_all
      show i.1+1 = i.1 + 1 ∨ w i = w ⟨2 * k + 1 - i.1, by simp_all;omega⟩
        ∧ i.1 = i.1+1 + 1
      simp
    · -- new
      simp at g₄ g₅
      simp_all
      subst g₄
      have := i.2
      have : i.1 = 0 := by omega
      have : i = 0 := by exact Eq.symm (Fin.eq_of_val_eq (id (Eq.symm this)))
      subst this
      rfl

    · simp_all
      have : ¬ i.1 + 1 ≤ k := by omega

      simp_all
      split_ifs with g₀
      · exfalso
        omega
      · show w i = w 0 ∧ 2 * k - i.1 = 1
        have : 2 * k + 1 - i.1 = 0 := by tauto
        have : i.1 = 2 * k + 1 := by omega
        simp_all
        omega
    · simp_all
      have : 2 * k + 1 - i.1  = k := Fin.mk.inj_iff.mp (by tauto)
      have : i.1 = k + 1 := by omega
      simp_rw [this]
      have : ¬ k + 1 + 1 ≤ k := by omega
      rw [dif_neg this]
      simp
      show w i = w ⟨2 * k - k, by omega⟩ ∧
      2 * k - k = (2*k-(k+1)) ∨ w i = w ⟨2 * k + 1 - (2 * k -k), by omega⟩
      ∧ (2*k-(k+1)) + 1 = 2 * k - k
      right
      constructor
      · congr
        apply Fin.mk.inj_iff.mpr
        omega
      · omega
    · have : ¬ i.1 + 1 ≤ k := by
        omega
      rw [dif_neg this]
      show w i = w ⟨2 * k + 1 - i.1, by omega⟩ ∧ 2*k-i.1 = 2 * k + 1 - i.1 + 1 ∨
      w i = w ⟨2 * k + 1 - (2 * k + 1 - i.1), by omega⟩ ∧
      2 * k + 1 - i.1 = 2*k-i.1 + 1
      right
      constructor
      · have : 2 * k + 1 - (2 * k + 1 - i) = i := by omega
        simp_rw [this]
      · omega

theorem hyde_accepts {A : Type} {k : ℕ} (hk : k ≥ 1) (w : Fin (2*k+1) → A) :
  accepts_word_path (@kayleighδ A k w) w 0 0 fun t : Fin (2*(k+1)) => dite (t.1 ≤ k)
    (fun ht => (⟨t.1,     Order.lt_add_one_iff.mpr ht⟩ : Fin (k+1)))
    (fun ht => (⟨2*k+1-t.1,by omega⟩ : Fin (k+1))) := by
  unfold kayleighδ accepts_word_path
  simp
  constructor
  · intro h
    exfalso
    omega
  · intro i
    split_ifs with g₀ g₁ g₂ g₃ g₄
    · -- i ≤ k, i=0
      simp_all
      show w ⟨i,by omega⟩ = w 0 ∧ 1 = 1
      simp_all
    · -- i ≤ k, i ≠ 0, i = k
      simp_all
      have : i.1 = k := Fin.mk.inj_iff.mp g₂
      simp_rw [this]
      simp
      show k = 2 * k - k ∨ w i = w ⟨2 * k + 1 - k, by omega⟩ ∧ 2 * k - k + 1 = k

      left
      omega
    · -- i ≤ k, i ≠ 0, i ≠ k
      have : ¬ i.1 = k := by
        intro hc
        apply g₂
        exact Fin.mk.inj_iff.mpr hc
      have : i.1 ≤ k := by exact g₀
      have : i.1 + 1 ≤ k := by omega
      simp_all
      show i.1+1 = i.1 + 1 ∨ w i = w ⟨2 * k + 1 - i.1, by simp_all;omega⟩
        ∧ i.1 = i.1+1 + 1
      simp
    · -- ¬ i ≤ k, 2k+1-i=0
      simp_all
      have : ¬ i.1 + 1 ≤ k := by omega

      simp_all
      split_ifs with g₀
      · exfalso
        omega
      · show w i = w 0 ∧ 2 * k - i.1 = 1
        have : 2 * k + 1 - i.1 = 0 := by tauto
        have : i.1 = 2 * k + 1 := by omega
        simp_all
        omega
    · -- ¬ i ≤ k, ¬ 2k+1-i=0, 2k+1-i=k
      simp_all
      have : 2 * k + 1 - i.1  = k := Fin.mk.inj_iff.mp (by tauto)
      have : i.1 = k + 1 := by omega
      simp_rw [this]
      have : ¬ k + 1 + 1 ≤ k := by omega
      rw [dif_neg this]
      simp
      show w i = w ⟨2 * k - k, by omega⟩ ∧
      2 * k - k = (2*k-(k+1)) ∨ w i = w ⟨2 * k + 1 - (2 * k -k), by omega⟩
      ∧ (2*k-(k+1)) + 1 = 2 * k - k
      right
      constructor
      · congr
        apply Fin.mk.inj_iff.mpr
        omega
      · omega
    · --¬ i ≤ k, ¬ 2k+1-i=0, 2k+1-i≠ k
      have : ¬ i.1 + 1 ≤ k := by
        omega
      rw [dif_neg this]
      show w i = w ⟨2 * k + 1 - i.1, by omega⟩ ∧ 2*k-i.1 = 2 * k + 1 - i.1 + 1 ∨
      w i = w ⟨2 * k + 1 - (2 * k + 1 - i.1), by omega⟩ ∧
      2 * k + 1 - i.1 = 2*k-i.1 + 1
      right
      constructor
      · have : 2 * k + 1 - (2 * k + 1 - i) = i := by omega
        simp_rw [this]
      · omega


def strongly_unique {A Q : Type} (n : ℕ) (δ : A → Q → Set Q) (init final : Q) : Prop :=
  ∀ (v₀ v₁ : Fin n → A)
    (p₀ p₁ : Fin (n+1) → Q),
    (h₀ : accepts_word_path δ v₀ init final p₀) →
    (h₁ : accepts_word_path δ v₁ init final p₁) →
    p₀ = p₁ ∧ v₀ = v₁

theorem hyde_strong_unique_kh {A : Type} {k : ℕ} (v₀ v₁ w : Fin (2*k+1) → A)
    (p₀ p₁ : Fin (2*(k+1)) → Fin (k+1))
    (h₀ : accepts_word_path (@khδ A k w) v₀ 0 0 p₀)
    (h₁ : accepts_word_path (@khδ A k w) v₁ 0 0 p₁) :
    p₀ = p₁ ∧ v₀ = v₁ := by
  let hydepath := fun t : Fin (2*(k+1)) => dite (t.1 ≤ k)
    (fun ht => (⟨t.1,     Order.lt_add_one_iff.mpr ht⟩ : Fin (k+1)))
    (fun ht => (⟨2*k+1-t.1,by omega⟩ : Fin (k+1)))
  have : p₀ = hydepath := by
    apply hyde_unique_path_kh
    apply accepts_path_of_accepts_word_path
    exact h₀
  have : p₁ = hydepath := by
    apply hyde_unique_path_kh
    apply accepts_path_of_accepts_word_path
    exact h₁
  have : w = v₀ := by
    apply hyde_unique_word_kh
    exact h₀
  have : w = v₁ := by
    apply hyde_unique_word_kh
    exact h₁
  simp_all


theorem hyde_strong_unique {A : Type} {k : ℕ} (v₀ v₁ w : Fin (2*k+1) → A)
    (p₀ p₁ : Fin (2*(k+1)) → Fin (k+1))
    (h₀ : accepts_word_path (@kayleighδ A k w) v₀ 0 0 p₀)
    (h₁ : accepts_word_path (@kayleighδ A k w) v₁ 0 0 p₁) :
    p₀ = p₁ ∧ v₀ = v₁ := by
  let hydepath := fun t : Fin (2*(k+1)) => dite (t.1 ≤ k)
    (fun ht => (⟨t.1,     Order.lt_add_one_iff.mpr ht⟩ : Fin (k+1)))
    (fun ht => (⟨2*k+1-t.1,by omega⟩ : Fin (k+1)))
  have : p₀ = hydepath := by
    apply hyde_unique_path
    apply accepts_path_of_accepts_word_path
    exact h₀
  have : p₁ = hydepath := by
    apply hyde_unique_path
    apply accepts_path_of_accepts_word_path
    exact h₁
  have : w = v₀ := by
    apply hyde_unique_word
    exact h₀
  have : w = v₁ := by
    apply hyde_unique_word
    exact h₁
  simp_all

theorem hyde_strongly_unique_kh {A : Type} {k : ℕ} (w : Fin (2*k+1) → A) :
  strongly_unique (2*k+1) (@khδ A k w) 0 0 := by
    unfold strongly_unique
    intro v₀ v₁ p₀ p₁ h₀ h₁
    apply hyde_strong_unique_kh <;> tauto


theorem hyde_strongly_unique {A : Type} {k : ℕ} (w : Fin (2*k+1) → A) :
  strongly_unique (2*k+1) (@kayleighδ A k w) 0 0 := by
    unfold strongly_unique
    intro v₀ v₁ p₀ p₁ h₀ h₁
    apply hyde_strong_unique <;> tauto


def nfa_complexity_at_most {A : Type} {n : ℕ} (w : Fin n → A) (q : ℕ): Prop :=
  ∃ Q : Type, ∃ _ : Fintype Q, card Q = q ∧
    ∃ δ init final p, @accepts_word_path Q A n (δ) w init final p
    ∧ ∀ v : Fin n → A, ∀ p',
      @accepts_word_path Q A n (δ) v init final p' → p = p' ∧ w = v

theorem extend_accept {A : Type} {k : ℕ} {w : Fin (2 * k + 1) → A} {Q : Type}
    {δ : A → Q → Set Q} {init final : Q} (p : Fin (2 * k + 1 + 1) → Q)
    (hp : accepts_word_path δ w init final p)
    {v : Fin (2 * k) → A} {p' : Fin (2 * k + 1) → Q}
    (h : accepts_word_path δ v init (p ⟨2 * k, by omega⟩) p') :
    let pe := Fin.snoc p' (p (Fin.last (2 * k + 1)));
    let ve := Fin.snoc v (w (Fin.last (2 * k)));
    accepts_word_path δ ve init final pe := by
  intro pe ve
  unfold accepts_word_path at hp
  unfold accepts_word_path at h
  constructor
  · unfold pe
    rw [← h.1]
    simp [Fin.snoc]
    rfl
  · constructor
    · unfold pe
      have := h.2.1
      simp [Fin.snoc]
      tauto
    · intro i
      unfold pe Fin.snoc ve Fin.snoc
      simp
      by_cases hi : i.1 < 2 * k
      · simp_all
        have := h.2.2 ⟨i.1, by omega⟩
        simp at this
        exact this
      · rw [dif_neg hi]
        rw [dif_neg hi]
        have : i.1 = 2 * k := by omega
        have : i = Fin.last (2*k) := by exact Fin.eq_last_of_not_lt hi
        subst this
        have : p' (Fin.last (2*k)) = p ⟨2*k, by omega⟩ := by tauto
        rw [this]
        tauto

/-- Jan 3, 2024: subword inequality -/
theorem restricting
 {A : Type} {n q : ℕ} (w : Fin (n+1) → A)
 (h : nfa_complexity_at_most w q) : nfa_complexity_at_most (Fin.init w) q := by
  obtain ⟨Q,hQ⟩ := h
  obtain ⟨x,hx⟩ := hQ
  use Q, x
  obtain ⟨δ,hδ⟩ := hx.2
  obtain ⟨init,hinit⟩ := hδ
  obtain ⟨final, hfinal⟩ := hinit
  obtain ⟨p,hp⟩ := hfinal
  unfold accepts_word_path at hp ⊢
  constructor
  · tauto
  · use δ
    use init
    use p ⟨n, by omega⟩
    use Fin.init p

    constructor
    · constructor
      · rw [← hp.1.1]
        rfl
      · constructor
        · rfl
        · intro i
          exact hp.1.2.2 ⟨i.1, by omega⟩
    · intro v
      intro p'
      intro h
      have use := hp.2 (Fin.snoc v (w (Fin.last n)))
        (Fin.snoc p' (p (Fin.last (n+1)))) (by
          constructor
          · rw [← h.1]
            conv =>
              left
              right
              change @Fin.castSucc (n+1) 0
            apply Fin.snoc_castSucc
          · constructor
            · have := hp.1.2.1
              rw [← this]
              simp
            · intro i
              have := hp.1.2.2 i
              by_cases hi : i.1 < n
              · have := h.2.2 ⟨i.1, hi⟩
                simp at this
                revert this
                apply Iff.mp
                apply Eq.to_iff
                congr
                · symm
                  have : @Fin.snoc n (fun a ↦ A) v (w (Fin.last n)) i  = v ⟨i.1, hi⟩ := by
                    conv =>
                      left
                      right
                      change @Fin.castSucc (n) ⟨i.1,by omega⟩
                    apply Fin.snoc_castSucc
                  rw [this]
                  have : @Fin.snoc (n + 1) (fun a ↦ Q) p' (p (Fin.last (n + 1))) ⟨i.1, by omega⟩ = p' i := by
                    conv =>
                      left
                      right
                      change @Fin.castSucc (n+1) ⟨i.1,by omega⟩
                    apply Fin.snoc_castSucc
                  rw [this]
                · symm
                  conv =>
                    left
                    right
                    change @Fin.castSucc (n+1) ⟨i.1 + 1,by omega⟩
                  apply Fin.snoc_castSucc
              · have : i.1 = n := by omega
                have : i = Fin.last n := Fin.eq_last_of_not_lt hi
                subst this
                simp_rw [this]
                have := hp.1.2.2 ⟨n, by omega⟩
                revert this;
                apply Iff.mp
                apply Eq.to_iff
                congr
                · simp
                  conv =>
                    left
                    left
                    right
                    change Fin.last n
                  have : @Fin.snoc (n + 1) (fun a ↦ Q) p' (p (Fin.last (n + 1))) ⟨n, by omega⟩ =
                    p ⟨n, by omega⟩ := by
                      have := h.2.1
                      rw [← this]
                      conv =>
                        left
                        right
                        change @Fin.castSucc (n+1) ⟨n,by omega⟩
                      apply Fin.snoc_castSucc
                  rw [this]
                · symm
                  simp
                  conv =>
                    right
                    right
                    change Fin.last (n+1)
                  conv =>
                    left;right;change Fin.last (n+1)
                  simp
        )

      constructor
      · rw [use.1];simp
      · rw [use.2];simp




theorem hydetheorem_kh
 {A : Type} {k : ℕ} (w : Fin (2*k+1) → A) :
 nfa_complexity_at_most w (k+1) := by
 use Fin (k+1)
 use Fin.fintype (k + 1)
 constructor
 · exact Fintype.card_fin (k + 1)
 · use khδ w
   use 0
   use 0
   use fun t : Fin (2*(k+1)) => dite (t.1 ≤ k)
    (fun ht => (⟨t.1,     Order.lt_add_one_iff.mpr ht⟩ : Fin (k+1)))
    (fun ht => (⟨2*k+1-t.1,by omega⟩ : Fin (k+1)))
   constructor
   · exact hyde_accepts_kh w
   · intro v p' h
     constructor
     · symm
       apply hyde_unique_path'''_kh
       exact h
     · exact hyde_unique_word_kh w v p' h

theorem hydetheorem
 {A : Type} {k : ℕ} (hk : k ≥ 1) (w : Fin (2*k+1) → A) :
 nfa_complexity_at_most w (k+1) := by
 use Fin (k+1)
 use Fin.fintype (k + 1)
 constructor
 · exact Fintype.card_fin (k + 1)
 · use kayleighδ w
   use 0
   use 0
   use fun t : Fin (2*(k+1)) => dite (t.1 ≤ k)
    (fun ht => (⟨t.1,     Order.lt_add_one_iff.mpr ht⟩ : Fin (k+1)))
    (fun ht => (⟨2*k+1-t.1,by omega⟩ : Fin (k+1)))
   constructor
   · exact hyde_accepts hk w
   · intro v p' h
     constructor
     · symm
       apply hyde_unique_path'''
       exact h
     · exact hyde_unique_word w v p' h



open Classical
theorem hyde_short₁ {A : Type} (w : Fin 1 → A) :
nfa_complexity_at_most w 1 := by
  unfold nfa_complexity_at_most
  use Fin 1
  use (Fin.fintype 1)
  use rfl
  use (fun a q => ite (a = w 0) {q} ∅)
  use 0
  use 0
  use (fun t => 0)
  constructor
  · unfold accepts_word_path
    simp
    intro i
    have := i.2
    have : i.1 = 0 := by omega
    have : i = 0 := Fin.fin_one_eq_zero i
    subst this
    rfl
  · intro v p' h
    constructor
    · ext t
      simp
    · ext i
      have := i.2
      have : i.1 = 0 := by omega
      have : i = 0 := Fin.fin_one_eq_zero i
      subst this
      unfold accepts_word_path at h
      have := h.2.2 0
      simp at this
      tauto

/-- The empty word has A_N at most 1.
This version does not require the alphabet A to be nonempty,
hence does not follow using `restricting`.
-/
theorem hyde_short₀ {A : Type} (w : Fin 0 → A) :
nfa_complexity_at_most w 1 := by
  unfold nfa_complexity_at_most
  use Fin 1
  use (Fin.fintype 1)
  use rfl
  use (fun a q => ∅)
  use 0
  use 0
  use (fun t => 0)
  constructor
  · unfold accepts_word_path
    constructor
    · simp
    · constructor
      · simp
      · intro i
        have := i.2
        simp at this
  · intro v p' h
    constructor
    · ext t
      simp
    · ext i
      have := i.2
      simp at this

theorem hyde_all_lengths₂_kh {A : Type} {n : ℕ} (hn : n ≥ 1) (w : Fin n → A) :
nfa_complexity_at_most w (n/2+1) := by
  by_cases he : Odd n
  · obtain ⟨k,hk⟩ := he
    subst hk
    have : (2 * k + 1) / 2 + 1 = k + 1 := by omega
    rw [this]
    apply hydetheorem_kh
  · simp at he
    obtain ⟨k, hk⟩ := he
    rw [← two_mul] at hk
    subst hk
    have : (2 * k)/2 + 1 = k + 1 := by omega
    rw [this]
    have : Nonempty A := by
      refine Nonempty.intro ?val
      exact w ⟨0,by omega⟩
    have : Inhabited A := by
      exact Classical.inhabited_of_nonempty this
    let w' := @Fin.snoc (2*k) (fun _ => A) w (Inhabited.default)
    have : w = Fin.init w' := by unfold w';simp
    rw [this]
    apply @restricting A (2*k) (k+1) w'
    apply hydetheorem_kh


theorem hyde_all_lengths₂ {A : Type} {n : ℕ} (hn : n ≥ 2) (w : Fin n → A) :
nfa_complexity_at_most w (n/2+1) := by
  by_cases he : Odd n
  · obtain ⟨k,hk⟩ := he
    subst hk
    have : (2 * k + 1) / 2 + 1 = k + 1 := by omega
    rw [this]
    apply hydetheorem
    omega
  · simp at he
    obtain ⟨k, hk⟩ := he
    rw [← two_mul] at hk
    subst hk
    have : (2 * k)/2 + 1 = k + 1 := by omega
    rw [this]
    have : Nonempty A := by
      refine Nonempty.intro ?val
      exact w ⟨0,by omega⟩
    have : Inhabited A := by
      exact Classical.inhabited_of_nonempty this
    let w' := @Fin.snoc (2*k) (fun _ => A) w (Inhabited.default)
    have : w = Fin.init w' := by unfold w';simp
    rw [this]
    apply @restricting A (2*k) (k+1) w'
    apply hydetheorem
    omega

theorem hyde_all_lengths_kh {A : Type} {n : ℕ} (w : Fin n → A) :
    nfa_complexity_at_most w (n/2+1) := by
  by_cases H : n = 0
  · subst H
    have := @hyde_short₀ A w
    simp;tauto
  · have : n ≥ 1 := by omega
    apply hyde_all_lengths₂_kh
    tauto

theorem hyde_all_lengths {A : Type} {n : ℕ} (w : Fin n → A) :
    nfa_complexity_at_most w (n/2+1) := by
  by_cases H : n = 0
  · subst H
    have := @hyde_short₀ A w
    simp;tauto
  · by_cases H : n = 1
    · subst H
      have := @hyde_short₁ A w
      simp;tauto
    · have : n ≥ 2 := by omega
      apply hyde_all_lengths₂
      tauto



theorem A_N_bounded {A : Type} {n : ℕ} (w : Fin n → A) :
  ∃ q, nfa_complexity_at_most w q := by
  use n/2+1
  apply hyde_all_lengths

noncomputable def A_N {A : Type} : {n : ℕ} → (Fin n → A) → ℕ :=
  fun w => Nat.find (A_N_bounded w)

theorem A_N_bound {A : Type} {n : ℕ} (w : Fin n → A) :
  A_N w ≤ n/2+1 := by
  unfold A_N
  have := hyde_all_lengths w
  exact find_le this
