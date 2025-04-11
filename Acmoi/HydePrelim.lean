import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.Algebra.Order.Floor
import Mathlib.Data.Nat.Log
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fin.Tuple.Take
set_option maxHeartbeats 2000000
/-!

  # Preliminaries for Hyde's Theorem


-/

open Finset Fintype Nat Classical

section General

/-- If we are not yet half-way there, then if we started at the destination,
we would not yet be half-way home. -/
lemma flipCast {t k : ℕ} (h : ¬ t < k + 1) :
  2 * k + 1 - t < k + 1 := by omega

/-- A strange auxiliary lemma about odd-length tuples. -/
lemma odd_tuples_aux {A : Type*} {k : ℕ} {w v : Fin (2 * k + 1) → A}
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

/--  Discrete version of the Racecar Principle. -/
lemma racecar {k : ℕ} {f : Fin (k+1) → Fin (k+1)} {a b : Fin (k+1)}
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



/-- Bidirectional version of the Discrete Racecar Principle. -/
lemma exact_racecar {k : ℕ} {f : Fin (k+1) → Fin (k+1)}
    (h₀ : f 0 = 0) (hk : f (Fin.last k) = (Fin.last k))
    (h : ∀ (s : Fin k),
      (f s.succ).1
    ≤ (f s.castSucc).1 + 1) {a : Fin k} :
    f a.castSucc = a.castSucc := by
    by_contra H
    have hr := racecar h₀ h a.1 (by
      simp only [Fin.val_zero, add_zero];omega
    )
    simp only [Fin.val_zero, add_zero] at hr
    have : (f a.castSucc).1 < a := by
      contrapose H
      simp_all only [gt_iff_lt, not_lt, Decidable.not_not]
      exact Fin.eq_of_val_eq <| Nat.le_antisymm hr H
    let b := (f a.castSucc)
    have : (f (Fin.last k)).1 < k := by
      have := @racecar k f a.castSucc b rfl h (k-a)
        (by simp)
      simp only [Fin.coe_castSucc, Fin.is_le', Nat.sub_add_cancel] at this
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

/-- p is an accepting path for the NFA δ. -/
def accepts_path {Q A : Type*} {n : ℕ}
    (δ : A → Q → Set Q) (init final : Q) (path : Fin (n+1) → Q) :=
  path 0 = init ∧ path (Fin.last n) = final
  ∧ ∀ i : Fin n, ∃ a : A, path i.succ ∈ δ a (path i.castSucc)

/-- If an NFA accepts a word along a path `p`, then `p` is an accepting path. -/
lemma accepts_path_of_accepts_word_path {Q A : Type*} {n : ℕ}
    (δ : A → Q → Set Q) (w : Fin n → A) (init final : Q) (path : Fin (n+1) → Q)
    (h : accepts_word_path δ w init final path) :
    accepts_path δ init final path :=
  ⟨h.1, h.2.1, fun i => ⟨w i, by simp_all [accepts_word_path]⟩⟩

/-- Nondeterministic automatic complexity, relational form. -/
def A_N_at_most {A : Type*} {n : ℕ} (w : Fin n → A) (q : ℕ): Prop :=
  ∃ Q : Type, ∃ _ : Fintype Q, card Q = q ∧
    ∃ δ init final p, accepts_word_path δ w init final p
    ∧ ∀ v : Fin n → A, ∀ p' : Fin (n+1) → Q,
      accepts_word_path δ v init final p' → p = p' ∧ w = v

/-- Total automatic complexity, relational form. -/
def A_at_most {A : Type*} {n : ℕ} (w : Fin n → A) (q : ℕ): Prop :=
  ∃ Q : Type, ∃ _ : Fintype Q, card Q = q ∧
    ∃ δ init final p, (∀ a q, Fintype.card (δ a q) = 1) ∧ accepts_word_path δ w init final p
    ∧ ∀ v : Fin n → A, ∀ p' : Fin (n+1) → Q,
      accepts_word_path δ v init final p' → p = p' ∧ w = v

/-- The incomplete deterministic automatic complexity `A⁻`. -/
def A_minus_at_most {A : Type*} {n : ℕ} (w : Fin n → A) (q : ℕ): Prop :=
  ∃ Q : Type, ∃ _ : Fintype Q, card Q = q ∧
    ∃ δ init final p, (∀ a q, Fintype.card (δ a q) ≤ 1) ∧ accepts_word_path δ w init final p
    ∧ ∀ v : Fin n → A, ∀ p' : Fin (n+1) → Q,
      accepts_word_path δ v init final p' → p = p' ∧ w = v

/-- Total nondeterministic automatic complexity, relational form.  -/
def A_N_tot_at_most {A : Type*} {n : ℕ} (w : Fin n → A) (q : ℕ): Prop :=
  ∃ Q : Type, ∃ _ : Fintype Q, card Q = q ∧
    ∃ δ init final p, (∀ a q, Fintype.card (δ a q) ≥ 1) ∧ accepts_word_path δ w init final p
    ∧ ∀ v : Fin n → A, ∀ p' : Fin (n+1) → Q,
      accepts_word_path δ v init final p' → p = p' ∧ w = v

/-- A word cannot have complexity 0,
 because then there'd be no initial state. -/
theorem A_N_ge_one {A : Type*} {n : ℕ} (w : Fin n → A) : ¬ A_N_at_most w 0 := by
  intro ⟨Q,x,hx⟩
  obtain ⟨_, init, _⟩ := hx.2
  have : Inhabited Q := { default := init }
  simp_all

/-- The empty word has A_N at most 1.
This version does not require the alphabet A to be nonempty,
hence does not follow using `restricting`.
-/
theorem hyde_emp {A : Type*} (w : Fin 0 → A) :
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


open Fin in
/-- If an NFA accepts a word then by changing the final state we can also accept its prefixes. -/
theorem restricting_construction {A : Type*} {Q : Type} {δ : A → Q → Set Q} {init final : Q} {n : ℕ}
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

/-- Subword inequality for A_N. -/
theorem restricting
 {A : Type*} {n q : ℕ} {w : Fin (n+1) → A}
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


/-- The relation behind exact nondeterministic automatic complexity. -/
def A_Ne_at_most {A : Type} {n : ℕ} (w : Fin n → A) (q : ℕ): Prop :=
  ∃ Q : Type, ∃ _ : Fintype Q, card Q = q ∧
    ∃ δ init final p, accepts_word_path δ w init final p
    ∧ ∀ v : Fin n → A, ∀ p' : Fin (n+1) → Q,
      accepts_word_path δ v init final p' → w = v

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

theorem A_N_le_A_minus {A : Type} {n q : ℕ} {w : Fin n → A}
    (h : A_minus_at_most w q) : A_N_at_most w q := by
  obtain ⟨Q, fQ, hQ⟩ := h
  obtain ⟨δ, init, final, p, hδ⟩ := hQ.2
  use Q, fQ
  constructor
  · exact hQ.1
  · use δ, init, final, p
    constructor
    · exact hδ.2.1
    · intro v p' hp'
      exact hδ.2.2 v p' hp'

theorem A_Ne_le_A_minus {A : Type} {n q : ℕ} {w : Fin n → A}
    (h : A_minus_at_most w q) : A_Ne_at_most w q := by
  obtain ⟨Q, fQ, hQ⟩ := h
  obtain ⟨δ, init, final, p, hδ⟩ := hQ.2
  use Q, fQ
  constructor
  · exact hQ.1
  · use δ, init, final, p
    constructor
    · exact hδ.2.1
    · intro v p' hp'
      exact (hδ.2.2 v p' hp').2

theorem A_minus_le_A {A : Type} {n q : ℕ} {w : Fin n → A}
    (h : A_at_most w q) : A_minus_at_most w q := by
  obtain ⟨Q, fQ, hQ⟩ := h
  obtain ⟨δ, init, final, p, hδ⟩ := hQ.2
  use Q, fQ
  constructor
  · exact hQ.1
  · use δ, init, final, p
    constructor
    · intro a q
      rw [hδ.1 a q]
    · tauto


theorem A_Ne_le_A {A : Type} {n q : ℕ} {w : Fin n → A}
    (h : A_at_most w q) : A_Ne_at_most w q := by
  obtain ⟨Q, fQ, hQ⟩ := h
  obtain ⟨δ, init, final, p, hδ⟩ := hQ.2
  use Q, fQ
  constructor
  · exact hQ.1
  · use δ, init, final, p
    constructor
    · exact hδ.2.1
    · intro v p' hp'
      exact (hδ.2.2 v p' hp').2
