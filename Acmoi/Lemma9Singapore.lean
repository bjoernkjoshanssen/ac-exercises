import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.Algebra.Order.Floor
import Mathlib.Data.Nat.Log
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fin.Tuple.Take
import Acmoi.HydeTheorem
set_option maxHeartbeats 2000000
/-!

  # Lemma 9 in NUS paper 2025

The file Theorem1_49.lean combines the ring construction with the
dead state completion. Here we try to separate them.
-/

open Finset Fintype Nat Classical

def ringδ {A : Type} {n : ℕ} (hn : n ≠ 0) (w : Fin n → A) : A → Fin n → Set (Fin n) := by
      intro a q
      by_cases H : a = w q
      · exact {⟨(q.1 + 1) % n, by refine mod_lt (↑q + 1) ?a;omega⟩}
      · exact ∅

theorem liveRingδ  {A : Type} {m n : ℕ} (hn : n ≠ 0)
    (v : Fin m → A) (w : Fin n → A) (p : Fin (m+1) → Fin n) {final : Fin n}
    (h : @accepts_word_path (Fin n) A m (ringδ hn w) v ⟨0, by omega⟩ final p)
    (t : Fin (m+1)) : p t = ⟨t.1 % n, by
      refine mod_lt ↑t ?a
      omega
    ⟩ := by
  have := @Fin.induction m (fun k  => p k = ⟨k.1 % n, by
      apply mod_lt k.1
      omega
    ⟩ ) (by
    simp;unfold accepts_word_path at h;tauto
  ) (by
    intro i hi
    simp [accepts_word_path, ringδ] at h
    rw [(h.2.2 i).2, hi]
    simp
  )
  apply this

lemma ringpathhelper {m n : ℕ} (hn : n ≠ 0)
    (t : Fin (m + 1)) : t.1 % n < n := by
    apply mod_lt ↑t
    omega

def ringpath {m n : ℕ} (hn : n ≠ 0) : Fin (m+1) → Fin n := fun t =>
    ⟨t.1 % n, @ringpathhelper m n hn t⟩

theorem ringδ_uniqueWord {A : Type} {m n : ℕ} (hn : n ≠ 0) (hm : m ≠ 0)
    (v : Fin m → A) (w : Fin n → A)
    {start final : Fin (n)}
    (h : accepts_word_path (ringδ hn w) v start final (ringpath hn)) :
    ∀ i : Fin m, v i = w ⟨i.1 % n, mod_lt ↑i <| by omega⟩ := by
  intro t
  have ⟨b,hb⟩ : ∃ b, m = b+1 := by exact exists_eq_succ_of_ne_zero hm
  subst hb
  have := @Fin.induction b (fun k => v k = w ⟨k.1 % n, by
    apply mod_lt ↑k
    omega
  ⟩) (by
    simp
    unfold accepts_word_path ringδ ringpath at h
    simp at h
    have := (h.2.2 0)
    simp at this
    tauto
    ) (by
      intro i hi
      have h₀ := h.2.2 ⟨i.1 + 1, by omega⟩
      unfold accepts_word_path ringδ ringpath at h₀
      simp at h₀
      tauto
    )
  apply this

def extendMod {A : Type} {n : ℕ} (hn : n ≠ 0) (w : Fin n → A) (m : ℕ) : Fin m → A :=
  fun i => w ⟨i.1 % n, by refine mod_lt ↑i ?a;omega;⟩

/-- This is Lemma 9 in NUS paper (even stronger since it is for A_minus). -/
theorem A_minus_bound₀'extendMod {A : Type} {n : ℕ} (hn : n ≠ 0) (w : Fin n → A)
    (m : ℕ)  (hm : m ≠ 0) : A_minus_at_most (extendMod hn w m) (n) := by
  use Fin (n), (Fin.fintype (n))
  let final : Fin (n) := ⟨m % n, by
      suffices m % n < n by omega
      apply mod_lt m
      omega
    ⟩
  constructor
  · exact Fintype.card_fin (n)
  · use ringδ hn w, ⟨0, by omega⟩, final, (fun t : Fin (m+1) => ⟨t.1 % n, by apply ringpathhelper hn⟩)
    constructor
    · intro a q
      unfold ringδ
      split_ifs <;> aesop
    · constructor
      · constructor
        · rfl
        · constructor
          · simp
          · intro i
            unfold extendMod
            simp
            unfold ringδ
            split_ifs with g₀
            · simp
            · simp; exfalso; apply g₀
              by_cases h : i.1 < n
              · simp_all
              · congr
      · intro v p' h
        have hr : p' = ringpath hn := by
          unfold ringpath
          ext i
          have := @liveRingδ A m n hn v w p' final h i
          rw [this]
        constructor
        · symm;tauto
        · rw [hr] at h
          have := @ringδ_uniqueWord A m n hn hm v w ⟨0,by omega⟩ final h
          ext i
          rw [this i]
          unfold extendMod
          simp

/-- The non-state / one-state / dead-state / trash-state completion of `δ`. -/
def complet {A Q : Type} (δ : A → Q → Set Q) : A → Option Q → Set (Option Q) :=
  fun a o => by
    by_cases H₀ : o = none
    · exact {none}
    · by_cases H₁ : δ a (o.get (Option.isSome_iff_ne_none.mpr H₀)) = ∅
      · exact {none}
      · exact some '' (δ a (o.get (Option.isSome_iff_ne_none.mpr H₀)))

open Option

lemma complet_card {A Q : Type} [Fintype Q] {δ : A → Q → Set Q} (q : Q) (a : A):
    Fintype.card ((complet δ) a q) = max (Fintype.card ((δ) a q)) 1 := by
  unfold complet
  have : some q ≠ none := by simp
  rw [dif_neg this]
  split_ifs with g₀
  · simp at g₀; rw [g₀]; simp
  · simp at g₀
    have h₀: Fintype.card ↑(some '' δ a ((some q).get rfl)) = (Fintype.card ↑(δ a q)) := by
      apply Fintype.card_congr
      simp
      unfold Set.Elem at *
      use (fun x => ⟨by exact x.1.get (by
        have := x.2
        obtain ⟨b,hb⟩ := this
        refine isSome_iff_exists.mpr ?a
        use b
        tauto), by
        obtain ⟨b,hb⟩ := x.2
        simp_rw [← hb.2]
        tauto⟩)
      · intro x
        exact ⟨x.1, by simp⟩
      · intro x
        simp
      · intro x;
        simp
    have h₂: (Fintype.card ↑(δ a q)) ≠ 0 := by
      intro hc
      apply g₀
      have := (@card_eq_zero_iff ↑(δ a q) _).mp hc
      exact Set.isEmpty_coe_sort.mp this
    have h₁: (Fintype.card ↑(δ a q)) ≥ 1 := by omega
    rw [h₀];exact Eq.symm (Nat.max_eq_left h₁)


lemma complet_extends_paths {A Q : Type} {δ : A → Q → Set Q} {n : ℕ} {w : Fin n → A}
    {init final : Q} {p : Fin (n+1) → Q}
    (hδ : accepts_word_path          δ  w init final                 p   ) :
          accepts_word_path (complet δ) w init final (fun x => some (p x)) := by
  constructor
  · simp
    exact hδ.1
  · constructor
    · simp
      exact hδ.2.1
    · intro i
      simp [complet]
      have : ¬ δ (w i) (p i.castSucc) = ∅ := by
        intro hc
        have := hδ.2.2 i
        rw [hc] at this
        simp at this
      rw [if_neg this]
      simp
      exact hδ.2.2 i

lemma complet_conservative {A Q : Type} {δ : A → Q → Set Q} {n : ℕ} {w : Fin n → A}
    {init final : Q} {p : Fin (n+1) → Q}
    (hδ : accepts_word_path (complet δ) w init final (fun x => some (p x)) ) :
          accepts_word_path δ w init final p := by
  constructor
  · have :=hδ.1
    simp at this
    tauto
  · constructor
    · have := hδ.2.1
      simp_all
    · intro i
      have := hδ.2.2 i
      simp [complet] at this
      split_ifs at this <;> simp_all
lemma complet_preserves_unique_path' {A Q : Type} {δ : A → Q → Set Q} {n : ℕ}
    {init final : Q} {p : Fin (n+1) → Q} {v : Fin n → A}
    (hv : ∀  p', accepts_word_path          δ  v init final  p' →                 p     =  p') :
          ∀ op', accepts_word_path (complet δ) v init final op' → (fun x => some (p x)) = op'  := by
  intro op' h
  have H : ¬ ∃ j, op' j = none := by
    intro hc
    obtain ⟨j₀,hj₀⟩ := hc
    have h₀ : ∀ j, j₀.1 ≤ j.1 → op' j = none :=
      @Fin.induction n (fun j => j₀.1 ≤ j.1 → op' j = none) (by
        simp
        intro h;have : j₀ = 0 := Eq.symm (Fin.eq_of_val_eq (id (Eq.symm h)))
        rw [this] at hj₀
        exact hj₀
      ) (by
        intro i;simp;intro ih hi
        by_cases H : j₀.1 = i.1 + 1
        · rw [← hj₀]
          congr
          symm
          exact Eq.symm (Fin.eq_of_val_eq (id (Eq.symm H)))
        · have h₀ : op' i.castSucc = none := by apply ih;omega
          have h₁ := h.2.2 i
          simp [complet] at h₁
          split_ifs at h₁
          exact h₁
      )
    have h₁ := h₀ (Fin.last n) (by simp;omega)
    -- dead lemma
    have := h.2.1
    simp_all
  push_neg at H
  let f (j : Fin (n+1)) : Q :=
    (op' j).get (isSome_iff_ne_none.mpr (H j))
  have h₀ : op' = fun j => some (f j) := by ext; simp [f]
  have h₁ := (hv f (by
    unfold f
    unfold accepts_word_path at h ⊢
    constructor
    · have h₁ := h.1
      simp_rw [h₁]
      simp
    · constructor
      · simp_rw [h.2.1]
        simp
      · simp [complet] at h
        intro i
        have h₂ := h.2.2 i
        split_ifs at h₂ <;> simp_all
      ))
  rw [h₀, h₁]


lemma complet_preserves_unique {A Q : Type} {δ : A → Q → Set Q} {n : ℕ} {w : Fin n → A}
    {init final : Q} {p : Fin (n+1) → Q}
    (hδ :
            ∀ (v : Fin n → A) (p' : Fin (n + 1) → Q),
            accepts_word_path δ v init final p' → p = p' ∧ w = v) :
            ∀ (v : Fin n → A) (op' : Fin (n + 1) → Option Q),
            accepts_word_path (complet δ) v init final op' →
            (fun x => some (p x)) = op' ∧ w = v

             := by
    · intro v op' h
      have h₀ := @complet_preserves_unique_path' A Q δ n init final p v (fun p' h => (hδ v p' h).1) op' (by tauto)
      constructor
      · exact h₀
      have h₂ := @complet_conservative A Q δ n v init final p (by rw [← h₀] at h;exact h)
      have h₁ := @complet_extends_paths A Q δ n v init final p h₂
      exact (hδ v p h₂).2


/-- Silly, but used twice. -/
lemma complet_and {A Q : Type} {δ : A → Q → Set Q} {n : ℕ} {w : Fin n → A}
    {init final : Q} {p : Fin (n+1) → Q}
    (hδ : accepts_word_path δ w init final p ∧
            ∀ (v : Fin n → A) (p' : Fin (n + 1) → Q),
            accepts_word_path δ v init final p' → p = p' ∧ w = v) :
          accepts_word_path (complet δ) w init final (fun x => some (p x)) ∧
            ∀ (v : Fin n → A) (op' : Fin (n + 1) → Option Q),
            accepts_word_path (complet δ) v init final op' →
            (fun x => some (p x)) = op' ∧ w = v
             := by
  · constructor
    · apply complet_extends_paths
      exact hδ.1
    · apply complet_preserves_unique
      exact hδ.2


theorem none_state_completion' {A : Type} {n : ℕ} (w : Fin n → A) :
A_N_at_most w q → A_N_tot_at_most w (q+1) := by
  intro ⟨Q,x,hQ⟩
  use Option Q, instFintypeOption
  constructor
  rw [← hQ.1]
  exact card_option
  obtain ⟨δ,init,final,p,hδ⟩ := hQ.2
  use complet δ, some init, some final, fun x => some (p x)
  constructor
  · intro a o
    unfold complet
    split_ifs with g₀ g₁
    · rfl
    · rfl
    · by_contra H
      simp at H
      apply H
      exact Set.nonempty_iff_ne_empty.mpr g₁
  · apply complet_and
    exact hδ


-- #print A_minus_at_most

/-- Dead-state completion lemma. -/
theorem none_state_completion {A : Type} {n : ℕ} (w : Fin n → A) :
A_minus_at_most w q →  A_at_most w (q+1) := by
  intro ⟨Q,x,hQ⟩
  use Option Q, instFintypeOption
  constructor
  rw [← hQ.1]
  exact card_option
  obtain ⟨δ,init,final,p,hδ⟩ := hQ.2
  use complet δ, some init, some final, fun x => some (p x)
  constructor
  · intro a o
    unfold complet
    split_ifs with g₀ g₁
    · rfl
    · rfl
    · have h₀ := hδ.1 a (o.get (isSome_iff_ne_none.mpr g₀))
      -- ALTERNATIVE PROOF:
      -- have hcl := @complet₁ A Q _ δ (o.get (isSome_iff_ne_none.mpr g₀)) a
      -- unfold complet at hcl
      -- simp only [some_get, dite_eq_ite, ne_eq] at hcl
      -- rw [dif_neg g₀] at hcl
      -- rw [if_neg g₁] at hcl
      -- simp_all
      -- rw [← hcl]
      -- congr
      -- ext u
      -- simp
      cases Or.symm (Nat.eq_or_lt_of_le h₀) with
      | inl h₄ =>
        have h₁ : Fintype.card (δ a (o.get (isSome_iff_ne_none.mpr g₀))) = 0 :=
          lt_one_iff.mp h₄
        rw [Fintype.card_eq_zero_iff] at h₁
        exfalso
        apply g₁ <| Set.isEmpty_coe_sort.mp h₁
      | inr h₄ =>
        rw [← h₄]
        apply Set.card_image_of_inj_on
        intro x hx y hy h
        apply some_injective _ h
  · apply complet_and
    tauto

/-- This is the main result of Theorem1_49.lean with a more modular proof. -/
theorem A_bound₀'extendMod {A : Type} {n : ℕ} (hn : n ≠ 0) (w : Fin n → A)
  (m : ℕ)  (hm : m ≠ 0) : A_at_most (extendMod hn w m) (n+1) := by
    refine none_state_completion (extendMod hn w m) ?a
    exact A_minus_bound₀'extendMod hn w m hm
