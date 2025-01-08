import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.Algebra.Order.Floor
import Mathlib.Data.Nat.Log
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fin.Tuple.Take
set_option maxHeartbeats 2000000
/-!

  # Hyde's Theorem


-/

open Finset Fintype Nat Classical

section General

/--  Version of boundFuncAdd that uses Fin API more. -/
lemma boundFuncAdd' {k : ℕ} {f : Fin (k+1) → Fin (k+1)} (a b : Fin (k+1))
    (h₀ : f a = b) (h : ∀ s : Fin k,
      (f s.succ).1
    ≤ (f s.castSucc).1 + 1) :
    ∀ (s : ℕ) (hs : s + a < k+1), (f ⟨s + a, hs⟩).1 ≤ s + b.1 := by
    intro s
    induction s with
    | zero =>
      intro hs
      simp only [zero_add]
      rw [h₀]
    | succ n ih =>
      intro hs
      simp_rw [add_assoc, add_comm 1 a.1, ← add_assoc] at hs ⊢
      simp_rw [add_assoc n 1, add_comm 1 b.1, ← add_assoc n b.1]
      have h₀ := ih (lt_of_succ_lt hs)
      have h₁ := h (⟨n+a.1,by omega⟩)
      calc
      _ ≤ (f ⟨n + a.1, lt_of_succ_lt hs⟩).1 + 1 := h₁
      _ ≤ _                             := Nat.add_le_add_right (ih (lt_of_succ_lt hs)) 1



/-- Version of id_of_slow using Fin API more.-/
lemma id_of_slow' {k : ℕ} {f : Fin (k+1) → Fin (k+1)}
    (h₀ : f 0 = 0) (hk : f (Fin.last k) = (Fin.last k))
    (h : ∀ (s : Fin k),
      (f s.succ).1
    ≤ (f s.castSucc).1 + 1) {a : Fin k} :
    f a.castSucc = a.castSucc := by
    by_contra H
    have : (f a.castSucc).1 < a := by
      have := @boundFuncAdd' k f 0 0 h₀ h a.1 (by
        simp;omega
      )
      simp at this
      contrapose H
      simp_all
      exact Fin.eq_of_val_eq <| Nat.le_antisymm this H
    let b := (f a.castSucc)
    have : (f (Fin.last k)).1 < k := by
      have := @boundFuncAdd' k f a.castSucc b rfl h (k-a)
        (by simp)
      simp at this
      calc
      _ ≤ k - a.1 + b.1 := this
      _ < k := by omega
    have : (f (Fin.last k)).1 = k := by simp_all
    omega

end General

/-- p is an accepting path for the word w in the NFA δ. -/
def accepts_word_path {Q A : Type*} {n : ℕ}
    (δ : A → Q → Set Q) (w : Fin n → A) (init : Q) (final : Q) (path : Fin (n+1) → Q) :=
  path 0 = init ∧ path (Fin.last n) = final
  ∧ ∀ i : Fin n, path i.succ ∈ δ (w i) (path i.castSucc)

-- #print axioms accepts_word_path
/-- p is an accepting path for the NFA δ. -/
def accepts_path {Q A : Type*} {n : ℕ}
    (δ : A → Q → Set Q) (init final : Q) (path : Fin (n+1) → Q) :=
  path 0 = init ∧ path (Fin.last n) = final
  ∧ ∀ i : Fin n, ∃ a : A, path i.succ ∈ δ a (path i.castSucc)

lemma accepts_path_of_accepts_word_path {Q A : Type*} {n : ℕ}
    (δ : A → Q → Set Q) (w : Fin n → A) (init final : Q) (path : Fin (n+1) → Q)
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

/-- A version of move_slowly using the Fin API more. -/
theorem move_slowly' {A : Type} {k : ℕ} {w : Fin (2 * k + 1) → A}
    {p : Fin (2 * (k + 1)) → Fin (k + 1)}
    (h : accepts_path (khδ w) 0 0 p)
    (s : Fin (2 * k + 1)) :
    (p s.succ).1 ≤ (p s.castSucc).1 + 1 := by
  unfold khδ accepts_path at h
  simp at h
  have := h.2.2 s
  obtain ⟨a,ha⟩ := this
  split_ifs at ha with g₀ g₁
  · cases ha ; omega
  · cases ha
    · aesop
  · cases ha with
  | inl h_1 => aesop
  | inr h_1 => have := h_1.2;simp_all
  · cases ha with
  | inl h_1 => aesop
  | inr h_1 =>
    have := h_1.2
    simp_all
    omega


/-- A proof of kayleighBound that uses Fin API instead of ⟨,⟩ notation -/
theorem kayleighBound' {A : Type} {k : ℕ} {w : Fin (2 * k + 1) → A}
    {p : Fin (2 * k + 1 + 1) → Fin (k + 1)}
    (h : accepts_path (khδ w) 0 0 p) :
    ∀ s : Fin (2*k+1+1), (p s).1 ≤ s.1 := by
  intro s
  exact @Fin.induction (2*k+1) (fun n => (p n).1 ≤ n.1)
    (by simp;rw [h.1];simp) (by
      intro n ih
      calc
      _ ≤ (p (n.castSucc)).1 + 1 := move_slowly' h n
      _ ≤ n.castSucc + 1         := add_le_add_right ih 1
      _ ≤ _                      := le_refl (↑n.castSucc + 1)
    ) s


/-- A Kayleigh graph path does not retreat too fast. -/
theorem kayleighBound_lower' {A : Type} {k : ℕ} (w : Fin (2 * k + 1) → A)
    (p : Fin (2 * k + 1 + 1) → Fin (k + 1)) (h : accepts_path (khδ w) 0 0 p)
    (s : Fin (2 * k + 1)) : (p s.succ).1 ≥ (p s.castSucc).1 - 1 :=
  @Fin.induction (2*k)
    (fun n : Fin (2*k+1) => (p n.castSucc).1 - 1 ≤ (p n.succ).1)
    (by simp; rw [h.1]; simp) (by
      intro n hn
      unfold accepts_path at h
      obtain ⟨a,ha⟩ := h.2.2 n.succ
      unfold khδ at ha
      simp at ha
      split_ifs at ha <;> cases ha <;> omega
    ) s



/-- If the Kayleigh graph ever uses the loop, we know when! -/
theorem hyde_loop_when' {A : Type} {k : ℕ} (w : Fin (2 * k + 1) → A)
    (p : Fin (2 * (k + 1)) → Fin (k + 1))
    (h : accepts_path (khδ w) 0 0 p) (t : Fin (2 * k + 1))
    (ht : p t.castSucc = Fin.last k ∧ p t.succ = Fin.last k) :
    t = ⟨k, by omega⟩ := by
  by_contra H
  cases lt_or_gt_of_ne fun hc => H <| Fin.eq_mk_iff_val_eq.mpr hc with
  | inl h' =>
    have : (p t.castSucc).1 < k := by
      have h₁ : (p t.castSucc).1 ≤ t.castSucc := by
        apply kayleighBound'; tauto
      simp at h₁
      calc
      _ ≤ _ := h₁
      _ < _ := h'
    rw [ht.1] at this
    simp at this
  | inr h' =>
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
      have : k = 0 := Fin.last_eq_zero_iff.mp this
      omega
    have : ∀ s : Fin (2*k+1), (p s.succ).1 ≥ p s.castSucc - 1 := by
      apply kayleighBound_lower'
      tauto
    have : ∀ s : Fin (2 * k+1 - t.1), (p (⟨t.1 + 1 + s, by omega⟩)).1 ≥ k - s := by
      intro s
      exact @Fin.induction (2*k-t.1)
        (fun n : Fin (2*k-t.1+1) =>
          (p (⟨t.1 + 1 + n, by omega⟩)).1 ≥ k - n ) (by
          simp;apply le_of_eq;symm;have :=ht.2
          exact Fin.mk.inj_iff.mp this) (by
          intro i hi
          have h₁ := this ⟨t.1 + 1 + i.1, by omega⟩
          simp_all
          simp_rw [← add_assoc (t.1 + 1)]
          omega
        ) ⟨s.1, by omega⟩
    have h₃ := this ⟨2*k+1-(t.1+1), by omega⟩
    simp at h₃
    have h₀ :  1 ≤ (p ⟨t.1 + 1 + (2 * k - t.1), by omega⟩).1 := by omega
    have h₁ : t.1 + 1 + (2 * k - t.1) = 2*k+1 := by omega
    have h₂ :  1 ≤ (p (Fin.last (2*k+1))).1 := by
      simp_rw [h₁] at h₀
      exact h₀
    unfold accepts_path at h
    simp_all



/-- If a Kayleigh graph path never uses the loop, then it preserves parity. -/
theorem hyde_parity' {A : Type} {k : ℕ} (w : Fin (2 * k + 1) → A) (p : Fin (2 * (k + 1)) → Fin (k + 1))
    (h : accepts_path (khδ w) 0 0 p)
    (H : ¬ ∃ t : Fin (2*k+1), p t.castSucc = Fin.last k ∧ p t.succ = Fin.last k) :
    ∀ (t : Fin (2 * (k + 1))), (p t).1 % 2 = t % 2 := by
  push_neg at H
  intro t
  exact @Fin.induction (2*k+1) (fun n => (p n).1 % 2 = n % 2)
    (by simp;rw [h.1];simp) (by
    intro n ih
    have ⟨a,h₁⟩ := h.2.2 n
    simp [khδ] at h₁ -- timed out
    split_ifs at h₁ with g₀ g₂ g₁
    · have : k = 0 := by omega
      subst this
      simp_all
      apply H 0
      · omega
      · apply Fin.mk.inj_iff.mpr
        simp
    · have why := h₁.2
      simp_rw [g₀] at why ih
      rw [why]
      aesop
    · cases h₁ with
    | inl h₁ =>
      have why := h₁.2
      rw [← why]
      specialize H n g₁
      exfalso
      apply H
      apply Fin.eq_of_val_eq
      rw [← why]
      aesop
    | inr h₁ =>
      have why := h₁.2
      simp_rw [g₁] at why
      cases mod_two_eq_zero_or_one (p n.succ).1 with
      | inl h_1 =>
        rw [h_1]
        apply congrArg (fun x => x % 2) at why
        rw [add_mod, h_1] at why
        simp at why
        rw [Fin.mk.inj_iff.mp g₁, ← why] at ih
        simp at ih ⊢
        rw [add_mod]
        simp_rw [ih]
        simp [← two_mul]
      | inr h_1 =>
        rw [h_1]
        apply congrArg (fun x => x % 2) at why
        rw [add_mod, h_1] at why
        simp at why
        rw [Fin.mk.inj_iff.mp g₁, ← why] at ih
        simp at ih ⊢
        rw [add_mod, ← ih]
    · cases h₁ with
    | inl h_1 =>
        have why := h_1.2
        rw [why, add_mod, ih, ← add_mod]
        simp
    | inr h_1 =>
        have why := h_1.2
        apply congrArg (fun x => x % 2) at why
        simp_rw [ih] at why
        symm at why
        simp
        rw [add_mod]
        simp at why
        simp [← why, add_assoc]
    ) t



theorem move_slowly_rev_aux' {A : Type} {k : ℕ} (w : Fin (2 * k + 1) → A)
(p : Fin (2 * (k + 1)) → Fin (k + 1))
    (h : accepts_path (khδ w) 0 0 p) (s : Fin k) :
    k ≤ k - (p ⟨s.1 + k + 1, by omega⟩).1 + 1
          + (p ⟨s.1 + 1 + k + 1, by omega⟩).1 := by
  suffices k ≤ k + 1 + (p ⟨s + 1 + k + 1, by omega⟩).1  - (p ⟨s + k + 1, by omega⟩).1 by omega
  simp_rw [show s + 1 + k + 1 = s + k + 1 + 1 by ring]
  have hmo' := @kayleighBound_lower' A k w p h ⟨s + k + 1, by omega⟩
  simp at hmo'
  have h : k + (1 + (p ⟨s + k + 1 + 1, by omega⟩).1 - (p ⟨s + k + 1, by omega⟩).1)
    = k + 1 + (p ⟨s + k + 1 + 1, by omega⟩).1 - (p ⟨s + k + 1, by omega⟩).1 := by
    apply Nat.eq_sub_of_add_eq'
    omega
  rw [← h]
  apply Nat.le_add_right

lemma flipCast {t k : ℕ} (h : ¬ t < k + 1) :
  2 * k + 1 - t < k + 1 := by omega

/-- Hyde's theorem (2013). -/
theorem hyde_unique_path' {A : Type} {k : ℕ} (w : Fin (2*k+1) → A)
  (p : Fin (2*(k+1)) → Fin (k+1))
  (h : accepts_path (khδ w) 0 0 p) :
  p = fun t : Fin (2*(k+1)) => dite (t.1 < k + 1)
    (fun ht => (⟨t.1, ht⟩ : Fin (k+1)))
    (fun ht => (⟨2*k+1-t.1, flipCast ht⟩ : Fin (k+1)))  := by
  by_cases H : ∃ t : Fin (2*k+1), p t.castSucc = Fin.last k ∧ p t.succ = Fin.last k -- we use the loop
  · obtain ⟨t,ht⟩ := H
    have : t = ⟨k,by omega⟩ := by apply hyde_loop_when' <;> tauto
    ext s
    split_ifs with g₀
    · by_cases hh : s.1 = k
      · have : s = ⟨k, by omega⟩ := Fin.eq_of_val_eq hh
        aesop
      have h₀':= @id_of_slow' k (fun x => p ⟨x.1,by have := x.2;linarith⟩)
        (by simp;unfold accepts_path at h;tauto) (by simp;aesop)
        (by
          intro s;simp
          exact @move_slowly' A k w p h (s.castLT (by omega))
        ) ⟨s, by omega⟩
      simp at this
      simp at h₀'
      rw [h₀']
    · -- the same as the other case but in opposite order...
      rw [this] at ht
      clear this
      simp at g₀
      by_cases hh : s.1 = 2 * k + 1
      · simp_rw [hh]
        simp
        have h₀ : s = Fin.last (2*k+1) := Fin.eq_of_val_eq hh
        rw [h₀]
        exact Fin.mk.inj_iff.mp h.2.1

      · let f : Fin ((k+1)) → Fin ((k+1)) :=
          fun u  => ⟨k - (p ⟨u + k + 1,by omega⟩).1, by omega⟩

        simp
        suffices (f ⟨s.1 - (k+1),by omega⟩).1 = s.1 - (k+1) by
          unfold f at this
          simp at this
          have h₀ : s.1 - (k+1) + k + 1 = s.1 := by omega
          simp_rw [h₀] at this
          change k - (p s).1 = s.1 - (k+1) at this
          omega
        have := @id_of_slow' k f (by
          unfold f;
          simp_all
        ) (by
          unfold f;
          unfold accepts_path at h
          have := h.2.1
          simp at this
          simp
          simp_rw [← two_mul]
          apply Fin.mk.inj_iff.mpr
          show  k - (p (Fin.last (2*k+1))).1 = k
          rw [this]
          simp
          ) (by
            intro s₁
            rw [tsub_le_iff_right]
            apply move_slowly_rev_aux' <;> tauto
          ) ⟨s - (k+1), by omega⟩
        simp_all
        unfold f at this
        simp at this
        exact this
  · have : ∀ (t : Fin (2 * (k+1))), (p t).1 % 2 = t % 2 := by
      apply hyde_parity' <;> tauto

    have : p (Fin.last (2*k+1)) ≠ 0 := by
      intro hc
      have := this (Fin.last (2*k+1))
      simp at this
      rw [hc] at this
      revert this
      simp
      intro hc
      symm at hc
      revert hc
      simp
      apply succ_mod_two_eq_one_iff.mpr
      simp
    exfalso
    unfold accepts_path at h
    tauto



/-- Hyde's theorem (2013). -/
theorem hyde_unique_path_reading_word {A : Type} {k : ℕ} {w v : Fin (2*k+1) → A}
  {p : Fin (2*(k+1)) → Fin (k+1)}
  (h : accepts_word_path (khδ w) v 0 0 p) :
  p = fun t : Fin (2*(k+1)) => dite (t.1 < k + 1)
    (fun ht => (⟨t.1,     by omega⟩ : Fin (k+1)))
    (fun ht => (⟨2*k+1-t.1,by omega⟩ : Fin (k+1)))  := by
  apply hyde_unique_path'
  apply accepts_path_of_accepts_word_path <;> tauto



theorem aux₀' {A : Type} {k : ℕ} {w v : Fin (2 * k + 1) → A}
  {i : Fin (2 * k + 1)} (g₀ : ¬ i.1 < k + 1)
  (g₆ : ⟨2 * k + 1 - i, flipCast g₀⟩ = Fin.last k)
  (h₂ :
    v i = w ⟨2 * k + 1 - i, by omega⟩ ∧ 2 * k + 1 - i = 2 * k - i ∨
      v i = w ⟨2 * k + 1 - (2 * k + 1 - i), by omega⟩ ∧ 2 * k - i + 1 = 2 * k + 1 - i) :
  w i = v i := by
    cases h₂ with
    | inl h => omega
    | inr h =>
      have : ⟨2 * k + 1 - i, by omega⟩ = (Fin.last k : Fin (k+1)) := by tauto
      have : 2 * k + 1 - i = k := Fin.mk.inj_iff.mp this
      simp_rw [this] at h
      have : i.1 = k + 1 := by omega
      symm
      have : 2 * k + 1 - k = k + 1 := by omega
      simp_rw [this] at h
      simp_all
      simp_rw [← this]


theorem hyde_unique_word {A : Type} {k : ℕ} {w v : Fin (2*k+1) → A}
    {p : Fin (2*(k+1)) → Fin (k+1)}
    (ha : accepts_word_path (khδ w) v 0 0 p) :
    w = v := by
  ext ⟨i,hi⟩
  have hup := hyde_unique_path_reading_word ha
  subst hup
  unfold accepts_word_path khδ at ha
  simp at ha
  have h₂ := ha.2 ⟨i, hi⟩
  clear ha
  have case1 (g₀ : i < k + 1) (g₁ : i=0) (g₂ : i=k) : w ⟨i,hi⟩ = v ⟨i,hi⟩ := by
    subst g₁
    simp_all
    exact h₂.symm
  have case3 (g₀ : i < k + 1) (g₁ : i≠ 0) (g₃ : ⟨i,by omega⟩= Fin.last k) : w ⟨i,hi⟩ = v ⟨i,hi⟩ := by
    have : i = k := Fin.mk.inj_iff.mp g₃
    subst this
    simp_all
    cases h₂ with
    | inl h => tauto
    | inr h => simp at h; omega
  have case4 (g₀ : i < k + 1) (g₁ : i≠ 0) (g₃ : ¬ ⟨i,by omega⟩= Fin.last k) : w ⟨i,hi⟩ = v ⟨i,hi⟩ := by
    have : i ≠ k := fun hc => g₃ <| Fin.mk.inj_iff.mpr hc
    have : i < k := by omega
    have : i < k + 1 := by omega
    simp_all
    cases h₂ with
    | inl h => tauto
    | inr h =>
      have := h.2
      simp at this
      omega
  have case5 (g₀ : ¬ i < k + 1) (g₄ : 2*k+1-i=0) (g₅: 2*k+1-i=k) : w ⟨i,hi⟩ = v ⟨i,hi⟩ := by
    have : ¬ i + 1 ≤ k := by omega
    simp_all
    omega
  have case6 (g₀ : ¬ i < k + 1) (g₄ : 2*k+1-i=0) (g₅: 2*k+1-i≠ k) : w ⟨i,hi⟩ = v ⟨i,hi⟩ := by
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
    have h₀ : ¬ i < k + 1 := by simp_all
    have h₁ : ¬ i < k := by omega
    have : ¬ i ≤ k := by omega
    simp_all
    apply aux₀'
    exact g₆
    exact h₂
    simp
    tauto
  · have h₀ : ¬ i < k + 1 := by simp_all
    have h₁ : ¬ i < k := by omega
    simp_all
    cases h₂ with
    | inl h =>
      have : 2 * k - i = 2 * k + 1 - i + 1 := h.2
      omega
    | inr h =>
      have : 2 * k + 1 - (2 * k + 1 - i) = i := by omega
      simp_rw [this] at h
      tauto


theorem hyde_accepts {A : Type} {k : ℕ}  (w : Fin (2*k+1) → A) :
  accepts_word_path (khδ w) w 0 0 fun t : Fin (2*(k+1)) => dite (t.1 < k + 1)
    (fun ht => (⟨t.1,      ht⟩ : Fin (k+1)))
    (fun ht => (⟨2*k+1-t.1,flipCast ht⟩ : Fin (k+1))) := by
  simp [khδ, accepts_word_path]
  constructor
  · omega
  · intro i
    split_ifs with g₀ g₁ g₂ g₃ g₄ g₅
    · trivial
    · have : 0 < k := by omega
      simp_all
      show w ⟨i,by omega⟩ = w 0 ∧ 1 = 1
      simp_all
    · simp_rw [Fin.mk.inj_iff.mp g₃]
      simp
      left
      show k = 2 * k - k
      omega
    · have : ¬ i.1 = k := fun hc => g₃ <| Fin.mk.inj_iff.mpr hc
      have : i.1 < k := by omega
      simp_all
      simp at g₁
      rw [Set.mem_def]
      simp
    · -- new
      simp at g₄ g₅
      simp_all
      subst g₄
      have : i = 0 := Fin.eq_of_val_eq <| by omega
      subst this
      rfl

    · simp_all
      omega
    · have : 2 * k + 1 - i.1  = k := Fin.mk.inj_iff.mp (by tauto)
      simp_rw [show i.1 = k + 1 by omega]
      right
      constructor
      · congr
        apply Fin.mk.inj_iff.mpr
        omega
      · simp
        have : ¬ k + 1 + 1 ≤ k := by omega
        omega
    · rw [dif_neg (show ¬ i.1 < k by omega)]
      right
      constructor
      · simp_rw [show 2 * k + 1 - (2 * k + 1 - i) = i by omega]
      · show 2 * k + 1 - i.1 = 2 * k - i.1 + 1
        omega

def A_N_at_most {A : Type} {n : ℕ} (w : Fin n → A) (q : ℕ): Prop :=
  ∃ Q : Type, ∃ _ : Fintype Q, card Q = q ∧
    ∃ δ init final p, accepts_word_path δ w init final p
    ∧ ∀ v : Fin n → A, ∀ p' : Fin (n+1) → Q,
      accepts_word_path δ v init final p' → p = p' ∧ w = v

def A_at_most {A : Type} {n : ℕ} (w : Fin n → A) (q : ℕ): Prop :=
  ∃ Q : Type, ∃ _ : Fintype Q, card Q = q ∧
    ∃ δ init final p, (∀ a q, Fintype.card (δ a q) = 1) ∧ accepts_word_path δ w init final p
    ∧ ∀ v : Fin n → A, ∀ p' : Fin (n+1) → Q,
      accepts_word_path δ v init final p' → p = p' ∧ w = v

def ringδ {A : Type} {n : ℕ} (w : Fin n → A) : A → Fin (n+1) → Set (Fin (n+1)) := by
      intro a q
      by_cases H₀ : q = Fin.last n
      · exact {Fin.last n} -- Fin.last n is a dead state
      · by_cases H₁ : q.1 < n - 1
        · by_cases H₂ : a = w ⟨q.1, by omega⟩
          · exact {⟨q.1 + 1, by omega⟩} -- continue around the cycle
          · exact {Fin.last n} -- go to dead state
        · by_cases H₂ : a = w ⟨q.1, by
            have : q.1 ≠ n := fun hc => H₀ <| Fin.eq_of_val_eq hc
            omega
          ⟩
          · exact {0} -- complete the cycle
          · exact {Fin.last n} -- go to dead state

theorem deadRingδ₀  {A : Type} {n : ℕ} (w v : Fin n → A) (p : Fin (n+1) → (Fin (n+1)))
  (h : accepts_word_path (ringδ w) v 0 0 p)
  (t : Fin n)
  (ht : p t.castSucc = Fin.last n) :
  p t.succ = Fin.last n := by
    unfold accepts_word_path at h
    have := h.2.2 t
    unfold ringδ at this
    simp at this
    simp_all

theorem deadRingδ₂  {A : Type} {n : ℕ} (w v : Fin n → A) (p : Fin (n+1) → (Fin (n+1)))
  (h : accepts_word_path (ringδ w) v 0 0 p)
  (t : Fin (n+1))
  (ht : p t = Fin.last n) (s : Fin (n+1)) (hs : t.1 ≤ s.1) :
    p s = Fin.last n := by
  have := @Fin.induction n (fun k => t.1 ≤ k.1 → p k = Fin.last n) (by
    simp;intro hh;rw [← ht];congr;symm;exact Fin.eq_of_val_eq hh
  ) (by
  simp
  intro i h₀ h₁
  by_cases H : t.1 ≤ i.1
  · have := h₀ (by omega)
    apply deadRingδ₀
    exact h
    exact this
  · have : t.1 = i.1 + 1 := by omega
    rw [← ht]
    congr
    symm at this
    exact Fin.eq_of_val_eq this
  )
  simp at this
  tauto

theorem deadRingδ₁  {A : Type} {n : ℕ} (hn : n ≠ 0) (w v : Fin n → A) (p : Fin (n+1) → (Fin (n+1)))
  (h : accepts_word_path (ringδ w) v 0 0 p)
  (t : Fin (n+1)) :
  p t ≠ Fin.last n := by
  intro hc
  have : p (Fin.last n) = Fin.last n := by
    apply deadRingδ₂
    exact h
    exact hc
    simp
    omega
  unfold accepts_word_path at h
  rw [h.2.1] at this
  apply hn
  symm at this
  exact Fin.last_eq_zero_iff.mp this

theorem liveRingδ₁  {A : Type} {n : ℕ} (hn : n ≠ 0) (w v : Fin n → A) (p : Fin (n+1) → (Fin (n+1)))
  (h : accepts_word_path (ringδ w) v 0 0 p)
  (t : Fin (n+1)) : t ≠ Fin.last n → p t = t := by
  have := @Fin.induction n (fun k  => k ≠ Fin.last n → p k = k) (by
    simp;intro;unfold accepts_word_path at h;tauto
  ) (by
    intro i h₀ h₁
    have := h₀ (by
      have := i.2; have : i.1 ≠ n := Nat.ne_of_lt this;exact
      Ne.symm (Fin.ne_of_val_ne (id (Ne.symm this)));)
    have hdead := @deadRingδ₁ A n hn w v p (by tauto) i.succ
    unfold accepts_word_path at h
    have := h.2.2 ⟨i.1, by omega⟩
    unfold ringδ at this
    simp at this
    split_ifs at this with g₀ g₁ g₂
    · simp_all
    · simp_all;rfl
    · simp at this
      tauto
    · simp_all
      symm
      exfalso
      have : i.1 + 1 = n := by omega
      apply h₁
      exact Eq.symm (Fin.eq_of_val_eq (id (Eq.symm this)))
    · simp at this
      tauto
  )
  simp at this
  intro hl
  exact this t (by tauto)

theorem ringδ_unique_word {A : Type} {n : ℕ} (hn : n ≠ 0) (w v : Fin n → A)
(h : accepts_word_path (ringδ w) v 0 0 ((by
      intro t
      by_cases t = Fin.last n
      · exact 0
      · exact ⟨t.1, by omega⟩
    ))) : w = v := by
  have hdead := @deadRingδ₁ A n hn w v ((by
      intro t
      by_cases H : t = Fin.last n
      · exact 0
      · exact ⟨t.1, by omega⟩
    )) h
  have ⟨m,hm⟩ : ∃ m, n = m+1 := by exact exists_eq_succ_of_ne_zero hn
  subst hm
  ext t
  have := @Fin.induction m (fun k => w k = v k) (by
    simp
    unfold accepts_word_path ringδ at h
    have := h.2.2 0
    simp at this
    split_ifs at this with g₀ g₁ g₂ g₃
    · exfalso
      simp at this
    · tauto
    · simp at this
    · simp at this
      tauto
    · tauto
    · simp at this
    · simp at this
    · simp_all
  ) (by
    simp
    intro i hi
    unfold accepts_word_path ringδ at h
    simp at h
    have := h i.succ
    simp at this
    split_ifs at this with g₀ g₁ g₂ g₃ g₄ g₅ g₆
    · exfalso;simp at this
    · exfalso; simp at g₁
    ·
      simp at this
      have hmi' : i.1 + 1 = m + 1 := by simp at g₀;exact Fin.mk.inj_iff.mp g₀
      have hmi : m = i.1 := by omega

      have h₀ : i.succ ≠ Fin.last m := by
        intro hc
        have : i.1 + 1 = m := Fin.mk.inj_iff.mp hc
        omega
      rw [if_neg h₀] at this
      by_cases H : v i.succ = w 0
      simp_all
      have : i.1 + 1 + 1 = 1 := Fin.mk.inj_iff.mp this
      omega
      have hey := h ⟨i.1,by omega⟩
      split_ifs at hey with g₉ g₁₀ g₁₁ g₁₂
      · have : i.1 = m + 1 := by simp at g₉;exact Fin.mk.inj_iff.mp g₉
        omega
      · simp at hey
      · exfalso; apply g₁₁;exact False.elim (g₉ g₁₀)
      · simp_rw [hmi] at g₁₂;simp at g₁₂
      · have hio : ⟨i.1, by omega⟩ = Fin.last m := Fin.eq_mk_iff_val_eq.mpr hmi.symm
        rw [hio] at hey
        simp at hey
        rw [if_neg H] at this
        simp at this
        have : i.1 + 1 + 1 = m + 1 := Fin.mk.inj_iff.mp this
        omega
    · have : m = 0 := by simp_all
      subst this
      have := i.2
      simp_all
    · simp at this
    · have hmi: m = i.1 := by simp at g₄;exact False.elim (g₀ g₄)
      simp_all;have : i.1 + 1 + 1 = m + 1 := by exact False.elim (g₀ g₄)
      omega
    · have him : i.succ ≠ Fin.last m := by
        intro hc
        have : i.1 + 1 = m := Fin.mk.inj_iff.mp hc
        simp at g₆
        omega
      rw [if_neg him] at this
      simp at this
      symm
      by_contra H
      have hw : w i.succ = w ⟨i.1 + 1, by omega⟩ := by congr
      simp_rw [← hw] at this
      rw [if_neg H] at this
      simp at this
      have : i.1 + 1 + 1 = m + 1 := Fin.mk.inj_iff.mp this
      simp at g₆
      omega
    · have him : i.succ = Fin.last m := by exact Fin.eq_last_of_not_lt g₆
      rw [if_pos him] at this
      simp at this
      symm
      by_contra H
      have hw : w i.succ = w ⟨i.1 + 1, by omega⟩ := by congr
      simp_rw [← hw] at this
      rw [if_neg H] at this
      simp at this
  )
  tauto


theorem A_bound₀ {A : Type} {n : ℕ} (hn : n ≠ 0) (w : Fin n → A) : A_at_most w (n+1) := by
  use Fin (n+1)
  use (Fin.fintype (n + 1))
  constructor
  · exact Fintype.card_fin (n + 1)
  · use ringδ w
    use 0, 0
    use (by
      intro t
      by_cases H : t = Fin.last n
      · exact 0
      · exact ⟨t.1, by omega⟩
    )
    constructor
    · intros
      unfold ringδ
      split_ifs <;> rfl
    ·
      have hac :  accepts_word_path (ringδ w) w 0 0 fun t ↦ if H : t = Fin.last n then 0 else ⟨↑t, by omega⟩ := by
        constructor
        · simp
        · unfold ringδ
          simp
          intro i
          split_ifs with g₀ g₁ g₂ g₃ g₄ g₅ g₆
          · simp
            exact Fin.last_eq_zero_iff.mp g₁.symm
          · have : n = 0 := Fin.last_eq_zero_iff.mp g₁.symm
            subst this
            simp_all
          · have : i.1 = n := Fin.mk.inj_iff.mp g₀
            omega -- contradiction with i.2
          · have : i.1 = n := Fin.mk.inj_iff.mp g₀
            have : n = 1 := by
              apply le_antisymm
              · contrapose g₃
                simp_all
              · contrapose g₁
                simp_all
            subst this
            simp_all
          · tauto
          · tauto
          · simp_all
            intro h
            revert g₆
            simp
            have : i.1 + 1 = n := Fin.mk.inj_iff.mp h
            omega
          · simp_all
            intro h
            have : i.1 = n := by
              apply le_antisymm
              · omega
              · exfalso
                apply h <| Fin.last_le_iff.mp g₆
            simp_rw [this] at g₄
            exfalso
            apply g₄ rfl
      constructor
      · apply hac
      · intro v p' h
        have hdead: ∀ s, p' s ≠ Fin.last n := by
          intro s
          apply deadRingδ₁
          exact hn
          exact h

        have hp : (fun t ↦ if H : t = Fin.last n then 0 else ⟨↑t, by omega⟩) = p' := by
          ext i
          split_ifs with g₀
          · have := h.2.1
            rw [← g₀] at this
            symm
            simp
            exact Fin.mk.inj_iff.mp this
          · simp
            symm
            have := @liveRingδ₁ A n hn w v p' h i g₀
            exact congrArg Fin.val this

        constructor
        · apply hp
        · exact @ringδ_unique_word A n hn w v (by
            rw [← hp] at h
            tauto
          )

theorem A_bound {A : Type} {n : ℕ} (w : Fin n → A) : A_at_most w (n+1) := by
  by_cases hn : n = 0
  · subst hn
    simp
    unfold A_at_most
    use Fin 1
    use (Fin.fintype 1)
    constructor
    · rfl
    · use (fun a q => Set.univ)
      use 0
      use 0
      use (by simp;intro z;exact z)
      constructor
      · intro a z
        have : (Set.univ : Set (Fin 1)) = {0} := by aesop
        aesop
      · constructor
        · constructor
          · simp
          · constructor
            · simp
            · intro i
              have := i.2
              omega
        · intro v p' h
          constructor
          · simp;ext i; calc
            _ = 0 := by exact Fin.val_eq_zero i
            _ = _ := by exact Eq.symm (Fin.val_eq_zero (p' i))
          · ext i
            have := i.2
            omega
  · apply A_bound₀;tauto

/-- The relation behind exact nondeterministic automatic complexity. -/
def A_Ne_at_most {A : Type} {n : ℕ} (w : Fin n → A) (q : ℕ): Prop :=
  ∃ Q : Type, ∃ _ : Fintype Q, card Q = q ∧
    ∃ δ init final p, accepts_word_path δ w init final p
    ∧ ∀ v : Fin n → A, ∀ p' : Fin (n+1) → Q,
      accepts_word_path δ v init final p' → w = v

open Fin

theorem restricting_construction {A Q : Type} {δ : A → Q → Set Q} {init final : Q} {n : ℕ}
    {w₁ : Fin (n + 1) → A} {p₁ : Fin (n + 1 + 1) → Q} (h₁ : accepts_word_path δ w₁ init final p₁)
    {w₀ : Fin n → A}       {p₀ : Fin (n + 1)     → Q} (h₀ : accepts_word_path δ w₀ init (p₁ (last n).castSucc) p₀) :
    accepts_word_path δ (snoc w₀ (w₁ (last n))) init final (snoc p₀ (p₁ (last (n + 1)))) := by
  constructor
  · rw [← h₀.1, ← castSucc_zero]
    apply snoc_castSucc
  · constructor
    · rw [← h₁.2.1, snoc_last]
    · intro i
      by_cases hi : i = last n
      · subst hi
        have := h₀.2.1 ▸ h₁.2.2 (last n)
        simp only [snoc_last, snoc_castSucc, succ_last, succ_eq_add_one]
        exact this
      · have hi': i.succ ≠ last (n+1) := fun hc => hi <| succ_eq_last_succ.mp hc
        rw            [← i.succ.castSucc_castPred hi']
        nth_rewrite 1 [←      i.castSucc_castPred hi]
        repeat rw [snoc_castSucc]
        exact h₀.2.2 (i.castPred hi)

/-- Jan 3, 2024: subword inequality -/
theorem restricting
 {A : Type} {n q : ℕ} {w : Fin (n+1) → A}
 (h : A_N_at_most w q) : A_N_at_most (Fin.init w) q := by
  obtain ⟨Q,hQ⟩ := h
  obtain ⟨x,hx⟩ := hQ
  use Q, x
  obtain ⟨δ,init,final,p,hp⟩ := hx.2
  constructor
  · tauto
  · use δ, init, p (Fin.last n).castSucc, Fin.init p
    constructor
    · constructor
      · rw [← hp.1.1]
        rfl
      · constructor
        · rfl
        · exact fun i => hp.1.2.2 i.castSucc
    · intro v p' h
      have h₀ : accepts_word_path δ (Fin.snoc v (w (Fin.last n))) init final
        (Fin.snoc p' (p (Fin.last (n + 1)))) := by
        apply restricting_construction <;> tauto
      have use := hp.2 (Fin.snoc v (w (Fin.last n)))
        (Fin.snoc p' (p (Fin.last (n+1)))) h₀
      constructor
      · rw [use.1];simp
      · rw [use.2];simp

theorem hydetheorem_odd {A : Type} {k : ℕ} (w : Fin (2*k+1) → A) :
 A_N_at_most w (k+1) := by
 use Fin (k+1), Fin.fintype (k + 1)
 constructor
 · exact Fintype.card_fin (k + 1)
 · use khδ w, 0, 0, fun t : Fin (2*(k+1)) => dite (t.1 < k + 1)
    (fun ht => (⟨t.1,     ht⟩ : Fin (k+1)))
    (fun ht => (⟨2*k+1-t.1,flipCast ht⟩ : Fin (k+1)))
   constructor
   · exact hyde_accepts w
   · exact fun _ _ h => ⟨(hyde_unique_path_reading_word h).symm, hyde_unique_word h⟩

theorem A_Ne_le_A_N {A : Type} {n q : ℕ} {w : Fin n → A}
    (h : A_N_at_most w q) : A_Ne_at_most w q := by
  obtain ⟨Q, fQ, hQ⟩ := h
  obtain ⟨δ, init, final, p, hδ⟩ := hQ.2
  use Q, fQ
  constructor
  · exact hQ.1
  · use δ, init, final, p
    constructor
    · exact hδ.1
    · intro v p' hp'
      exact (hδ.2 v p' hp').2

/-- A word cannot have complexity 0,
 because then there'd be no initial state. -/
theorem nfa_complexity_ge_one {A : Type} {n : ℕ} (w : Fin n → A) : ¬ A_N_at_most w 0 := by
  intro ⟨Q,x,hx⟩
  obtain ⟨_, init, _⟩ := hx.2
  have : Inhabited Q := { default := init }
  simp_all

/-- The empty word has A_N at most 1.
This version does not require the alphabet A to be nonempty,
hence does not follow using `restricting`.
-/
theorem hyde_emp {A : Type} (w : Fin 0 → A) :
A_N_at_most w 1 := by
  unfold A_N_at_most
  use Fin 1, (Fin.fintype 1), rfl, (fun a q => ∅), 0, 0, (fun t => 0)
  constructor
  · constructor
    · simp
    · constructor
      · rfl
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

theorem hyde_pos_length {A : Type} {n : ℕ} (hn : n ≠ 0) (w : Fin n → A) :
A_N_at_most w (n/2+1) := by
  by_cases he : Odd n
  · obtain ⟨k,hk⟩ := he
    subst hk
    have : (2 * k + 1) / 2 + 1 = k + 1 := by omega
    exact this ▸ hydetheorem_odd _
  · simp at he
    obtain ⟨k, hk⟩ := he
    rw [← two_mul] at hk
    subst hk
    have : (2 * k)/2 + 1 = k + 1 := by omega
    rw [this]
    have a := (Classical.inhabited_of_nonempty <| (Nonempty.intro <| w ⟨0,by omega⟩)).default
    let w' := @Fin.snoc (2*k) (fun _ => A) w a
    exact (Fin.init_snoc _ _) ▸ restricting <| hydetheorem_odd w'

theorem hyde_all_lengths {A : Type} {n : ℕ} (w : Fin n → A) :
    A_N_at_most w (n/2+1) := by
  by_cases H : n = 0
  · subst H
    exact hyde_emp w
  · exact hyde_pos_length H w

theorem A_bounded {A : Type} {n : ℕ} (w : Fin n → A) :
  ∃ q, A_at_most w q := by
  use n+1
  exact A_bound w


theorem A_N_bounded {A : Type} {n : ℕ} (w : Fin n → A) :
  ∃ q, A_N_at_most w q := by
  use n/2+1
  apply hyde_all_lengths

theorem A_Ne_bounded {A : Type} {n : ℕ} (w : Fin n → A) :
  ∃ q, A_Ne_at_most w q := by
  use n/2+1
  exact A_Ne_le_A_N <| hyde_all_lengths w

noncomputable def A_N {A : Type} : {n : ℕ} → (Fin n → A) → ℕ :=
  fun w => Nat.find (A_N_bounded w)

/-- Exact nondeterministic automatic complexity. -/
noncomputable def A_Ne {A : Type} : {n : ℕ} → (Fin n → A) → ℕ :=
  fun w => Nat.find (A_Ne_bounded w)

theorem A_N_bound {A : Type} {n : ℕ} (w : Fin n → A) :
  A_N w ≤ n/2+1 := find_le <| hyde_all_lengths w

-- #print axioms A_N_bound
