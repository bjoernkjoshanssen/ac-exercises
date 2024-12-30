import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.Algebra.Order.Floor
import Mathlib.Data.Nat.Log
import Mathlib.InformationTheory.Hamming
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fin.Tuple.Take
import Acmoi.dimVC
set_option tactic.hygienic false

/-!

  # VC-dimensions of nondeterministic finite automata for words of equal length
    Theorem 4 on Kathleen Romanik's testing dimension.


-/
open Finset Fintype

lemma fixBits {V : Type*} [DecidableEq V] [Fintype V] (C D : Finset V) (hD : D ⊆ C) :
    #(filter (fun H ↦ C ∩ H = D) univ) = #(univ \ C).powerset := by
          apply card_bij _ (by simp : ∀ H hH, (filter (fun x => x ∈ H) (univ \ C)) ∈ (univ \ C).powerset)
          · simp
            intro A hA B hB h
            have : A \ C = B \ C := by
              ext x
              have : x ∈ filter (fun x ↦ x ∈ A) (univ \ C)
                   ↔ x ∈ filter (fun x ↦ x ∈ B) (univ \ C) := by rw [h]
              simp at this
              simp_all
            have h₀ : A = A \ C ∪ C ∩ A := by ext;simp;tauto
            have h₁ : B = B \ C ∪ C ∩ B := by ext;simp;tauto
            rw [h₀, h₁, this, hA, hB]

          · simp
            intro A hA
            have h₀ : C ∩ A = ∅ := by
              ext
              simp
              intro _ h
              have := hA h
              simp_all
            use A ∪ (C ∩ D)
            constructor
            · have h₁ : C ∩ D = D := inter_eq_right.mpr hD
              rw [inter_union_distrib_left, h₀, h₁, h₁, empty_union]
            · ext x
              simp
              constructor
              · simp_all
              · intro h
                have := hA h
                simp_all

open Fintype

-- lemma shatter_fix {V : Type*} [DecidableEq V] [Fintype V] {C : Finset V}
--     (g₀ : ¬filter (fun H ↦ H ∩ C ≠ ∅) univ = ∅) :
--     (filter (fun k ↦ shatters_all (filter (fun H ↦ ¬H ∩ C = ∅) univ) k) (range (Fintype.card V + 1))).Nonempty := by
--   use 0
--   simp
--   rw [← shatters_all₀]
--   exact g₀


-- theorem four'  {V : Type*} [DecidableEq V] [Fintype V] (c m : ℕ)
--     (hm : m > card V):
--     (∀ 𝓗 : Finset (Finset V), #𝓗 > c → dimTest 𝓗 ≥ m) ↔ c ≥ 2^(card V) - 2^(card V - m) := by
--   sorry

/-- Theorem 4 from "VC-dimensions". -/
theorem four  {V : Type*} [DecidableEq V] [Fintype V] (c m : ℕ)
    (hm : m ≤ card V):
    (∀ 𝓗 : Finset (Finset V), #𝓗 > c → dimTest 𝓗 ≥ m) ↔ c ≥ 2^(card V) - 2^(card V - m) := by
  constructor
  · intro h₀
    by_contra hc
    have h₁ : c < 2 ^ Fintype.card V - 2 ^ (Fintype.card V - m) := by omega
    obtain ⟨C,hC⟩ := @subset_of_size V (univ : Finset V) m #(univ : Finset V) rfl hm
    have h₂ : 2 ^ Fintype.card V - 2 ^ (Fintype.card V - m) = #(filter (fun H => H ∩ C ≠ ∅) univ) := by
        have h₀ : #(filter (fun H => C ∩ H = ∅) univ) = #(univ \ C).powerset := by apply fixBits; simp
        have h₁ : #(filter (fun H => C ∩ H = ∅) univ) = 2^(card V - m) := by
            rw [h₀, card_powerset, card_sdiff hC.1, hC.2]
            rfl
        rw [← h₁, ← compl_filter, card_compl]
        simp_all
        simp_rw [← card_powerset, ← fixBits C ∅ (by simp), inter_comm]
    have h₃ := h₀ (filter (fun H => H ∩ C ≠ ∅) univ) (by omega)
    simp only [dimTest] at h₃
    split_ifs at h₃ with g₀
    · have : m = 0 := by omega
      subst this
      simp_all
    · have h₄ := (le_max'_iff (filter (fun k ↦ shatters_all (filter (fun H ↦ ¬H ∩ C = ∅) univ) k) (range (Fintype.card V + 1)))
        (by use 0; simp; rw [← shatters_all₀]; exact g₀) m).mp h₃
      simp at h₄
      obtain ⟨m',hm'⟩ := h₄
      have : shatters_all (filter (fun H ↦ ¬H ∩ C = ∅) univ) m := by
        apply shatters_all_mono hm'.1.2 hm'.2
        show m' ≤ card V
        omega
      have := this C hC.2 ∅ (by tauto)
      revert this
      simp
      intro x hx
      contrapose hx
      simp_all
      rw [← hx]
      exact inter_comm x C
  · intro h₀ 𝓗 hc
    unfold dimTest
    simp
    split_ifs with g₀
    · subst g₀
      simp at hc
    · apply le_max'
      simp
      constructor
      · omega
      · intro C hC D hD         -- lines 1 and 2 of the proof in the paper
        have h₀: #(univ : Finset (Finset V)) = 2^(card V) := by aesop
        have : #(filter (fun H => C ∩ H = D) (univ : Finset (Finset V)))
             = #((univ : Finset V) \ C).powerset := by apply fixBits; exact hD
        have : #(filter (fun H => C ∩ H = D) (univ : Finset (Finset V)))
          = 2^(card V - m) := by -- line 3 of the proof in the paper
            rw [this, card_powerset, card_sdiff (subset_univ _), hC]
            rfl
        have by₂ : #𝓗 > 2^(card V) - 2^(card V - m) := by omega-- line 3 of the proof in the paper
        have : #𝓗ᶜ = 2^card V - #𝓗 := by
          rw [card_compl]
          congr
        have : 2^card V - #𝓗 < 2^(card V - m) := by
          have fact (H u c : ℕ) (h : H > u - c) (h₀ : c ≤ u) (h₁ : H ≤ u) : u - H < c :=
            Nat.sub_lt_right_of_lt_add h₁ <| (Nat.sub_lt_iff_lt_add h₀).mp h
          exact fact #𝓗 (2^card V) (2^(card V - m)) by₂ (by
            apply Nat.pow_le_pow_of_le_right
            simp
            exact Nat.sub_le (Fintype.card V) m) (by
              rw [← h₀]
              exact card_le_card <| subset_univ 𝓗
            )
        have : #𝓗ᶜ < 2^(card V - m) := by omega -- line 4 of the proof in the paper
        have : ¬ (filter (fun H => C ∩ H = D) (univ : Finset (Finset V))) ⊆ 𝓗ᶜ := by
          intro hc
          have : #(filter (fun H => C ∩ H = D) (univ : Finset (Finset V))) ≤ #𝓗ᶜ := card_le_card hc
          omega
        -- done with line 5 of the paper
        have h₁ : (filter (fun H => C ∩ H = D) (univ : Finset (Finset V))) \ 𝓗ᶜ ≠ ∅ := by
          contrapose this
          simp_all
          apply sdiff_eq_empty_iff_subset.mp
          simp
          tauto
        contrapose h₁
        simp_all
        ext A
        simp
        exact fun h hc => h₁ _ hc h

lemma towards_lowerbound₀  {V : Type*} [DecidableEq V] [Fintype V] (c m : ℕ) :
    2^(card V - m) ≥ 2^(card V) - c →
    c ≥ 2^(card V) - 2^(card V - m) := by intro h; omega

lemma towards_lowerbound₁  {V : Type*} [DecidableEq V] [Fintype V] (c m : ℕ) :
       card V - m ≥ Nat.clog 2 (2^(card V) - c) →
    2^(card V - m) ≥ 2^(Nat.clog 2 (2^(card V) - c)) := by
  apply Nat.pow_le_pow_of_le_right
  simp

lemma towards_lowerbound₂  {V : Type*} [DecidableEq V] [Fintype V] (c : ℕ) :
    2^(Nat.clog 2 (2^(card V) - c))
    ≥ 2^(card V) - c := by
  refine Nat.le_pow_clog ?hb (2 ^ Fintype.card V - c)
  simp

lemma towards_lowerbound₃  {V : Type*} [DecidableEq V] [Fintype V] (c m : ℕ) :
       card V - m ≥ Nat.clog 2 (2^(card V) - c) →
    2^(card V - m) ≥ 2^(card V) - c := by
  intro h
  apply ge_trans (towards_lowerbound₁ c m h)
  apply towards_lowerbound₂


-- lemma towards_lowerbound₄  {V : Type*} [DecidableEq V] [Fintype V] (c m : ℕ)
--     (h₀ : m ≤ card V):
--        m ≤ card V - Nat.clog 2 (2^(card V) - c)  →

--        Nat.clog 2 (2^(card V) - c) ≤ card V - m  := by
--   intro h
--   exact (@le_tsub_iff_le_tsub ℕ _ _ _ _ _ _ m (card V) (Nat.clog 2 (2 ^ Fintype.card V - c)) _
--     h₀ (by
--       -- have : card V ≤ 2^(Nat.clog 2 (card V)) := by sorry
--       suffices  2^(Nat.clog 2 (2 ^ Fintype.card V - c)) ≤ 2^(card V) by
--         apply (Nat.le_pow_iff_clog_le _).mp
--         suffices card V - c ≤ card V by exact Nat.sub_le (2 ^ Fintype.card V) c
--         omega
--         simp
--       sorry
--     )).mp h
