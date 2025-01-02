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
   ∧ ∀ i : Fin (n), path (⟨i.1+1,by omega⟩) ∈ δ (w i) (path ⟨i.1,by omega⟩)

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

-- Now we can define general Kayleigh graph for odd-length words.
def kayleighδ {A : Type} {k : ℕ} (hk : k ≥ 1)
  (w : Fin (2*k+1) → A) : A → Fin (k+1) → Set (Fin (k+1)) := by
  let n := 2*k + 1
  intro b q r -- is r reachable in one step from q reading b?
  -- n = 3, n/2 = 1
  let b₀ := w ⟨q, by omega⟩
  let b₁ := w ⟨k + 1 - q, by omega⟩
  by_cases H : q = k -- q = 1
  · -- last state
    let P₀ : Prop := (b = b₀ ∧ q.1 = r.1) ∨ (b = w ⟨q+1,by omega⟩ ∧ r.1 + 1 = q.1)
    exact P₀
  · -- last q = 0
    let P : Prop := (b = b₀ ∧ r.1 = q.1 + 1) ∨ (b = b₁ ∧ q.1 = r.1 + 1)
    exact P

theorem move_slowly' {A : Type} {k : ℕ} {hk : k ≥ 1} {w : Fin (2 * k + 1) → A}
    {p : Fin (2 * (k + 1)) → Fin (k + 1)}
    (h : accepts_path (@kayleighδ A k hk w) 0 0 p)
    {s : ℕ} (hs : s < 2 * k + 1) :
    (p ⟨s + 1, by omega⟩).1 ≤ (p ⟨s, by omega⟩).1 + 1 := by
  unfold kayleighδ accepts_path at h
  simp at h
  have := h.2.2 ⟨s,hs⟩
  obtain ⟨a,ha⟩ := this
  split_ifs at ha with g₀
  simp at ha
  cases ha <;> omega
  cases ha
  have := h_1.2
  aesop
  have := h_1.2
  revert this
  simp;omega

theorem move_slowly_reverse' {A : Type} {k : ℕ} {hk : k ≥ 1} {w : Fin (2 * k + 1) → A}
    {p : Fin (2 * (k + 1)) → Fin (k + 1)}
    (h : accepts_path (@kayleighδ A k hk w) 0 0 p)
    {s : ℕ} (hs : s < 2 * k + 1) :
    (p ⟨s, by omega⟩).1 ≤ (p ⟨s + 1, by omega⟩).1 + 1 := by
  unfold kayleighδ accepts_path at h
  simp at h
  have := h.2.2 ⟨s,hs⟩
  split_ifs at this with g₀
  simp at this
  obtain ⟨a,ha⟩ := this
  cases ha <;> omega
  cases this with
  | intro a h =>
    simp at h
    cases h <;> omega


theorem kayleighBound' {A : Type} {k : ℕ} {hk : k ≥ 1} {w : Fin (2 * k + 1) → A}
    {p : Fin (2 * (k + 1)) → Fin (k + 1)}
    (h : accepts_path (@kayleighδ A k hk w) 0 0 p) :
    ∀ s, ∀ hs : s < 2*(k+1), (p ⟨s,by omega⟩).1 ≤ s := by
  intro s
  induction s with
  | zero => intro hs;simp;unfold accepts_path at h;aesop
  | succ n ih =>
    intro hs
    have := move_slowly' h (show n < 2 * k + 1 by omega)
    have := ih (by omega)
    omega

theorem kayleighBound_lower' {A : Type} {k : ℕ} (hk : k ≥ 1) (w : Fin (2 * k + 1) → A)
    (p : Fin (2 * (k + 1)) → Fin (k + 1))
    (h : accepts_path (@kayleighδ A k hk w) 0 0 p) :
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
theorem hyde_loop_when' {A : Type} {k : ℕ} (hk : k ≥ 1)
    (w : Fin (2 * k + 1) → A)
    (p : Fin (2 * (k + 1)) → Fin (k + 1))
    (h : accepts_path (@kayleighδ A k (by omega) w) 0 0 p) (t : Fin (2 * k + 1))
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
        apply move_slowly'; tauto
      have : ∀ s, ∀ hs : s < 2*(k+1), (p ⟨s,by omega⟩).1 ≤ s := by
        apply kayleighBound'; tauto
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
      apply kayleighBound_lower'
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

theorem hyde_parity' {A : Type} {k : ℕ} (hk : k ≥ 1) (w : Fin (2 * k + 1) → A) (p : Fin (2 * (k + 1)) → Fin (k + 1))
  (h : accepts_path (@kayleighδ A k (by omega) w) 0 0 p)
  (H : ¬ ∃ t : Fin (2*k+1), p ⟨t.1,by omega⟩ = Fin.last k ∧ p (⟨t.1+1, by omega⟩) = Fin.last k) :
  ∀ (t : ℕ) (ht : t < 2 * (k + 1)), (p ⟨t, ht⟩).1 % 2 = t % 2 := by
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
        split_ifs at h₁ with g₀
        · cases h₁
          · push_neg at H
            specialize H ⟨n, by omega⟩ g₀
            exfalso
            apply H
            apply Fin.eq_of_val_eq
            have := h_1.2
            simp_all
          · have why := h_1.2
            simp_all
            apply congrArg (fun x => x % 2) at why
            rw [g₀] at h₀
            simp at h₀
            rw [h₀, add_mod] at why
            cases mod_two_eq_zero_or_one (p ⟨n + 1, ht⟩).1
            · rw [h_2] at why
              simp at why
              rw [h_2]
              simp_all
              rw [← two_mul]
              simp
            · rw [h_2] at why
              simp at why
              rw [h_2, add_mod, ← why]
        · cases h₁
          · have why := h_1.2
            cases mod_two_eq_zero_or_one (p ⟨n + 1, ht⟩).1
            · rw [h_2]
              apply congrArg (fun x => x % 2) at why
              rw [h_2, add_mod, h₀] at why
              simp at why
              exact why
            · rw [h_2]
              apply congrArg (fun x => x % 2) at why
              change (p ⟨n + 1, ht⟩).1 % 2 = ((p ⟨n, lt_of_succ_lt ht⟩).1 + 1) % 2 at why
              rw [h_2, add_mod, h₀] at why
              simp at why
              exact why
          · have why := h_1.2
            cases mod_two_eq_zero_or_one (p ⟨n + 1, ht⟩).1
            · rw [h_2]
              apply congrArg (fun x => x % 2) at why
              rw [add_mod, h_2, add_mod, h₀] at why
              simp at why
              rw [add_mod, why]
            · rw [h_2]
              apply congrArg (fun x => x % 2) at why
              change (p ⟨n, lt_of_succ_lt ht⟩).1 % 2 = (↑(p ⟨n + 1, ht⟩) + 1) % 2 at why
              rw [add_mod, h_2, h₀] at why
              simp at why
              rw [add_mod, why]


theorem move_slowly_rev_aux' {A : Type} {k : ℕ} (hk : k ≥ 1) (w : Fin (2 * k + 1) → A)
(p : Fin (2 * (k + 1)) → Fin (k + 1))
    (h : accepts_path (@kayleighδ A k (by omega) w) 0 0 p) (s₁ : ℕ) (hs₁ : s₁ < k) :
    k ≤ k - ↑(p ⟨s₁ + k + 1, by omega⟩) + 1 + ↑(p ⟨s₁ + 1 + k + 1, by omega⟩) := by
  suffices k ≤ k + 1 + (p ⟨s₁ + 1 + k + 1, by omega⟩).1  - (p ⟨s₁ + k + 1, by omega⟩).1 by omega
  simp_rw [show s₁ + 1 + k + 1 = s₁ + k + 1 + 1 by ring]
  have hmo := @move_slowly_reverse' _ k hk w p h (s₁ + k + 1) (by omega)
  have : k + (1 + (p ⟨s₁ + k + 1 + 1, by omega⟩).1 - (p ⟨s₁ + k + 1, by omega⟩).1)
    = k + 1 + (p ⟨s₁ + k + 1 + 1, by omega⟩).1 - (p ⟨s₁ + k + 1, by omega⟩).1 := by
    apply Nat.eq_sub_of_add_eq'
    omega
  rw [← this]
  apply Nat.le_add_right

/-- Hyde's theorem (2013). -/
theorem hyde_unique_path' {A : Type} {k : ℕ} (hk : k ≥ 1) (w : Fin (2*k+1) → A)
  (p : Fin (2*(k+1)) → Fin (k+1))
  (h : accepts_path (@kayleighδ A k (by omega) w) 0 0 p) :
  p = fun t : Fin (2*(k+1)) => dite (t.1 ≤ k)
    (fun ht => (⟨t.1,     Order.lt_add_one_iff.mpr ht⟩ : Fin (k+1)))
    (fun ht => (⟨2*k+1-t.1,by omega⟩ : Fin (k+1)))  := by
  by_cases H : ∃ t : Fin (2*k+1), p ⟨t.1,by omega⟩ = Fin.last k ∧ p (⟨t.1+1, by omega⟩) = Fin.last k -- we use the loop
  · obtain ⟨t,ht⟩ := H
    have : t = ⟨k,by omega⟩ := by apply hyde_loop_when' <;> tauto
    ext s
    split_ifs with g₀
    · by_cases hh : s.1 = k
      · have : s = ⟨k, by omega⟩ := Eq.symm (Fin.eq_of_val_eq (id (Eq.symm hh)))
        aesop
      have := @id_of_slow k (fun x => p ⟨x.1,by have := x.2;linarith⟩)
        (by simp;unfold accepts_path at h;tauto) (by simp;aesop)
        (by
          intro s hs;simp
          exact @move_slowly' _ k hk w p h s (by omega)
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
          apply move_slowly_rev_aux' <;> tauto
        ) (s - (k+1)) (by
          omega
        )
      simp_all
  · have : ∀ (t : ℕ) (ht : t < 2 * (k+1)), (p ⟨t,ht⟩).1 % 2 = t % 2 := by
      apply hyde_parity' <;> tauto

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
theorem hyde_unique_path {A : Type} {k : ℕ} (hk : k ≥ 1) (w v : Fin (2*k+1) → A)
  (p : Fin (2*(k+1)) → Fin (k+1))
  (h : accepts_word_path (@kayleighδ A k (by omega) w) v 0 0 p) :
  p = fun t : Fin (2*(k+1)) => dite (t.1 ≤ k)
    (fun ht => (⟨t.1,     Order.lt_add_one_iff.mpr ht⟩ : Fin (k+1)))
    (fun ht => (⟨2*k+1-t.1,by omega⟩ : Fin (k+1)))  := by
  apply hyde_unique_path'
  apply accepts_path_of_accepts_word_path <;> tauto
  tauto
