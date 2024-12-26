import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.Algebra.Order.Floor
import Mathlib.Data.Nat.Log
import Mathlib.InformationTheory.Hamming
import Mathlib.Data.Finset.Basic

set_option tactic.hygienic false

/-!

  # VC-dimensions of nondeterministic finite automata for words of equal length
    Part 1: Define VC dimension and VC index and prove
    `dimVC = indexVC - 1` (even in the case of the empty family)

    Definition 10, Lemma 11, and Lemma 12 from the paper.
    (Bonus material for ac-exercises)

-/
section Basics
variable {V : Type*} [DecidableEq V] [Fintype V]

/-- To make this computable, restrict A ⊆ ⋃ 𝓕 -/
def shatters_some (𝓕 : Finset (Finset V)) (d : ℕ) : Prop :=
    ∃ A, A.card = d ∧ ∀ B ⊆ A, ∃ C ∈ 𝓕, A ∩ C = B

def shatters_all (𝓕 : Finset (Finset V)) (d : ℕ) : Prop :=
    ∀ A, A.card = d → ∀ B ⊆ A, ∃ C ∈ 𝓕, A ∩ C = B

instance (A B C : Finset V) : Decidable (A ∩ C = B) := decEq (A ∩ C) B

instance (𝓕 𝓖 : Finset (Finset V)) : Decidable (𝓕 = 𝓖) := decEq 𝓕 𝓖

instance (A B : Finset V) (𝓕 : Finset (Finset V)) : Decidable (∃ C ∈ 𝓕, A ∩ C = B) := by
  exact Multiset.decidableExistsMultiset

instance (A : Finset V) (𝓕 : Finset (Finset V)) : Decidable (∀ B ⊆ A, ∃ C ∈ 𝓕, A ∩ C = B) := by
  exact Fintype.decidableForallFintype

instance (A : Finset V) (𝓕 : Finset (Finset V)) (d : ℕ) : Decidable (A.card = d ∧ ∀ B ⊆ A, ∃ C ∈ 𝓕, A ∩ C = B) := by
  exact instDecidableAnd

instance (𝓕 : Finset (Finset V)) (d : ℕ) : Decidable (shatters_some 𝓕 d) := by
  unfold shatters_some
  exact Fintype.decidableExistsFintype

instance (𝓕 : Finset (Finset V)) (d : ℕ) : Decidable (shatters_all 𝓕 d) := by
  unfold shatters_all
  exact Fintype.decidableForallFintype


end Basics

theorem empty_does_not_shatter {V : Type*} [DecidableEq V] (k : ℕ) :
    ¬ shatters_some (∅ : Finset (Finset V)) k :=
  fun ⟨s,hs⟩ => by
    simp at hs
    obtain ⟨_, _⟩ := hs.2 ∅ (Finset.empty_subset s)

theorem nonempty_shatters {V : Type*} [DecidableEq V]  (𝓕 : Finset (Finset V)) {A : Finset V} (hA : A ∈ 𝓕) :
    shatters_some 𝓕 0 := by
  use ∅
  simp
  intro B hB
  constructor
  use A
  symm
  exact Finset.subset_empty.mp hB

open Finset


theorem equivVC {V : Type*} [DecidableEq V] [Fintype V] (F: Finset (Finset V)) :
    0 < F.card ↔ shatters_some F 0 := by
  constructor
  · intro h
    have h₀ : F.card ≠ 0 := Nat.not_eq_zero_of_lt h
    have : F ≠ ∅ := Ne.symm (ne_of_apply_ne card fun a ↦ h₀ (a.symm))
    exact nonempty_shatters F (nonempty_iff_ne_empty.mpr this).exists_mem.choose_spec
  · intro h
    suffices F ≠ ∅ by
      have : F.card ≠ 0 := by
        apply card_ne_zero.mpr
        exact nonempty_iff_ne_empty.mpr this
      exact Nat.zero_lt_of_ne_zero this
    intro hc
    exact empty_does_not_shatter (V := V) (k := 0) <| hc ▸ h

/-- The VC dimension of a finite set family. -/
def dimVC {V : Type*} [DecidableEq V] [Fintype V]
    (𝓕 : Finset (Finset V)) : ℕ := by
  by_cases H : 𝓕 = ∅
  exact 0 -- dummy value, should really be -1 but that is inconvenient in Lean
  exact Finset.max'
    (filter (shatters_some 𝓕) (range (𝓕.card + 1))) (by
      use 0
      simp
      refine (equivVC 𝓕).mp ?h.a
      refine card_pos.mpr ?h.a.a
      exact nonempty_iff_ne_empty.mpr H
      )

def dimVC! {V : Type*} [DecidableEq V] [Fintype V]
    (𝓕 : Finset (Finset V)) : ℕ := by
  by_cases H : 𝓕 = ∅
  exact 0 -- dummy value, should really be -1 but that is inconvenient in Lean
  exact Finset.max'
    (filter (shatters_some 𝓕) (range ((univ : Finset V).card + 1))) (by
      use 0
      simp
      refine (equivVC 𝓕).mp ?h.a
      refine card_pos.mpr ?h.a.a
      exact nonempty_iff_ne_empty.mpr H
      )

open Finset

/-- Obtain a smaller subset of a given set. -/
theorem subset_of_size {α : Type*} {s : Finset α} (a b : ℕ)
    (h_card : s.card = b) (h_le : a ≤ b) :
    ∃ t : Finset α, t ⊆ s ∧ t.card = a := by
  classical
  -- Extract the list representation of `s`
  let l := s.toList
  have h_length : l.length = b := by
    have := @List.toFinset_card_of_nodup α _ l (nodup_toList s)
    aesop
  -- Take the first `a` elements of the list
  let l' := l.take a

  -- Convert the list back into a finset
  let t := l'.toFinset

  -- Prove that `t` is a subset of `s`
  have h_subset : t ⊆ s := by
    intro x hx

    rw [List.mem_toFinset] at hx
    have : x ∈ List.take a s.toList := hx
    simp at this
    refine mem_toList.mp ?_
    exact List.mem_of_mem_take hx

  -- Prove that the cardinality of `t` is `a`
  have h_card_t : t.card = a := by
    rw [Finset.card_def]

    show (List.take a s.toList).toFinset.val.card = a
    have : a ≤ s.card := by aesop
    simp
    have : #s.toList.toFinset = l.length := @List.toFinset_card_of_nodup α _ l (nodup_toList s)
    have := @List.length_take α a s.toList
    have : (List.take a s.toList).dedup = (List.take a s.toList) :=
      ((s.toList.take_sublist a).nodup <| nodup_toList s).dedup

    rw [this]
    simp
    tauto

  -- Combine the results
  exact ⟨t, h_subset, h_card_t⟩

lemma of_size_subset (V : Type*) [Fintype V] (S : Finset V) (k l : ℕ) (h₀ : k ≤ l)
    (h : Finset.card S = l) : ∃ T, Finset.card T = k ∧ T ⊆ S := by
  have := @subset_of_size V S k l h h₀
  aesop

/-- A family can also shatter a smaller set. -/
lemma shatters_monotone {V : Type*} [DecidableEq V] [Fintype V]
    (𝓕 :  Finset (Finset V)) (h𝓕 : ∃ f, f ∈ 𝓕) (k l : ℕ) (h : k ≤ l)
    (h₀ : shatters_some 𝓕 l) : shatters_some 𝓕 k := by
  obtain ⟨A₀,hA₀⟩ := h₀
  obtain ⟨A,hA⟩ := of_size_subset V  A₀ k l h hA₀.1
  use A
  simp_all
  intro B hB
  have := hA₀.2 (B) (by tauto)
  obtain ⟨C₀,hC₀⟩ := this
  use C₀
  simp_all
  ext x
  constructor
  · intro H
    simp at H
    rw [← hC₀.2]
    simp
    tauto
  · intro H
    simp_all
    constructor
    · tauto
    · rw [← hC₀.2] at H
      simp at H
      tauto


lemma le_max'_iff (S : Finset ℕ) (h : S.Nonempty) (k : ℕ) :
  k ≤ S.max' h ↔ ∃ y ∈ S, k ≤ y := le_sup'_iff _

-- #eval @dimVC (Fin 2) _ _ ⟨{{0}},by simp⟩
-- #eval @dimVC (Fin 2) _ _ ⟨{{0,1}},by simp⟩
-- #eval @dimVC (Fin 2) _ _ ⟨{{1}},by simp⟩
-- #eval @dimVC (Fin 2) _ _ ⟨{∅},by simp⟩

theorem shattering_skolem {V : Type*} [DecidableEq V] [Fintype V] (F : Finset (Finset V)) (k : ℕ)
    (h : shatters_some F k) :
    ∃ A : Finset V, A.card = k ∧ ∃ φ : {B // B ⊆ A} → {C // C ∈ F},
        ∀ B : {B // B ⊆ A}, A ∩ (φ B) = B :=
    Exists.elim h (fun A h₀ => ⟨A, h₀.1, Exists.intro
        (fun B => ⟨(h₀.2 B.1 B.2).choose, (h₀.2 B.1 B.2).choose_spec.1⟩)
         fun B =>  (h₀.2 B.1 B.2).choose_spec.2⟩)

theorem VC_injective_function {V : Type*} [DecidableEq V] [Fintype V] (F : Finset (Finset V)) (A : Finset V)
    (φ : {B // B ⊆ A} → {C : Finset V // C ∈ F})
    (h : ∀ B : {B // B ⊆ A}, A ∩ (φ B) = B) :
    Function.Injective φ :=
  fun B₁ B₂ h0 => by
  have h3: A ∩ (φ B₁) = A ∩ (φ B₂) := by rw [h0]
  have : B₁.val = B₂.val := Eq.trans (Eq.trans (h B₁).symm h3) (h B₂)
  cases B₂
  cases B₁
  dsimp at *
  induction this
  rfl

/-- Lean 3 version thanks to Adam Topaz. -/
theorem card_of_injective {V : Type*} [DecidableEq V] [Fintype V] (F : Finset (Finset V)) (A : Finset V)
    (φ : {B // B ⊆ A} → {C : Finset V // C ∈ F})
    (h : Function.Injective φ) : A.powerset.card ≤ F.card := by

  have h₁: #A.powerset = Fintype.card { B // B ⊆ A } := by
    refine Eq.symm (Fintype.card_of_subtype A.powerset ?H)
    simp only [mem_powerset, implies_true]
  rw [h₁, ← Fintype.card_coe]
  exact Fintype.card_le_of_injective φ h

theorem pow_le_of_shatters {V : Type*} [DecidableEq V] [Fintype V] (F : Finset (Finset V)) (k : ℕ)
  (h : shatters_some F k) : 2^k ≤ F.card :=
  Exists.elim (shattering_skolem F k h) (fun A g => Exists.elim g.2 (fun φ hphi =>
      calc
           _ = 2^A.card := by rw [← g.left]
           _ = A.powerset.card := (card_powerset A).symm
           _ ≤ F.card := card_of_injective F A φ <|VC_injective_function F A φ hphi
    )
  )

theorem pow_le_of_shatters₂ {V : Type*} [DecidableEq V] [Fintype V] (F : Finset (Finset V)) (k : ℕ)
    (h : shatters_some F k) : k ≤ Nat.log 2 F.card := by
  have := pow_le_of_shatters F k h
  refine (Nat.pow_le_iff_le_log ?hb ?hy).mp this
  simp
  intro hc
  rw [hc] at this
  simp at this


lemma pow_le (m : ℕ) : m < 2 ^ m := by
  induction m with
        | zero => simp
        | succ n ih =>
          calc
          n + 1 < 2^n + 1 := by linarith
          _ ≤ _ := by ring_nf;linarith

theorem VC_works {V : Type*} [DecidableEq V] [Fintype V] (𝓕 : Finset (Finset V))
    (h𝓕 : ∃ f, f ∈ 𝓕) (k : ℕ) :
  k ≤ dimVC 𝓕 ↔ shatters_some 𝓕 k := by
  have hemp : 𝓕 ≠ ∅ := nonempty_iff_ne_empty.mp h𝓕
  constructor
  · intro h
    apply shatters_monotone 𝓕 h𝓕 k _ h
    have := Finset.max'_mem (filter (shatters_some 𝓕) (range (#𝓕 + 1)))
      (by
        apply filter_nonempty_iff.mpr
        use 0
        constructor
        · simp
        · obtain ⟨f,hf⟩ := h𝓕
          exact nonempty_shatters _ hf
      )
    simp at this
    unfold dimVC
    simp_all
  intro h₁
  have := le_max' (filter (shatters_some 𝓕) (range (#𝓕 + 1))) k
  unfold dimVC
  simp_all
  apply this
  linarith [pow_le_of_shatters 𝓕 k h₁, pow_le k]

theorem VC!_works {V : Type*} [DecidableEq V] [Fintype V] (𝓕 : Finset (Finset V))
    (h𝓕 : ∃ f, f ∈ 𝓕) (k : ℕ) :
  k ≤ dimVC! 𝓕 ↔ shatters_some 𝓕 k := by
  have hemp : 𝓕 ≠ ∅ := nonempty_iff_ne_empty.mp h𝓕
  constructor
  · intro h
    apply shatters_monotone 𝓕 h𝓕 k _ h
    have := Finset.max'_mem (filter (shatters_some 𝓕) (range (#(univ : Finset V) + 1)))
      (by
        apply filter_nonempty_iff.mpr
        use 0
        constructor
        · simp
        · obtain ⟨f,hf⟩ := h𝓕
          exact nonempty_shatters _ hf
      )
    simp at this
    unfold dimVC!
    simp_all
  intro h₁
  have := le_max' (filter (shatters_some 𝓕) (range (#(univ : Finset V) + 1))) k
  unfold dimVC!
  simp_all
  apply this
  show k < #univ + 1
  suffices k ≤ #univ by linarith
  obtain ⟨t,ht⟩ := h₁
  rw [← ht.1]
  refine card_le_card ?mpr.intro.a
  exact subset_univ t

/-- The VC dimension is bounded by the logarithm of the cardinality.
 This is one of the bounds listed in Wikipedia. -/
theorem pow_le_of_shatters₃ {V : Type*} [DecidableEq V] [Fintype V]
    (𝓕 : Finset (Finset V)) (h𝓕 : ∃ f, f ∈ 𝓕) :
    dimVC 𝓕 ≤ Nat.log 2 𝓕.card := by
  suffices ∀ k, k ≤ dimVC 𝓕 → k ≤ Nat.log 2 𝓕.card by
    apply this <| dimVC 𝓕
    simp
  intro k hk
  rw [VC_works] at hk
  exact @pow_le_of_shatters₂ V _ _ 𝓕 k hk
  exact h𝓕

theorem pow_le_of_shatters₃! {V : Type*} [DecidableEq V] [Fintype V]
    (𝓕 : Finset (Finset V)) (h𝓕 : ∃ f, f ∈ 𝓕) :
    dimVC! 𝓕 ≤ Nat.log 2 𝓕.card := by
  suffices ∀ k, k ≤ dimVC! 𝓕 → k ≤ Nat.log 2 𝓕.card by
    apply this <| dimVC! 𝓕
    simp
  intro k hk
  rw [VC!_works] at hk
  exact @pow_le_of_shatters₂ V _ _ 𝓕 k hk
  exact h𝓕

lemma indexVC!_defined {V : Type*} [DecidableEq V] [Fintype V] {𝓕 : Finset (Finset V)} :
    (filter (fun k ↦ ¬shatters_some 𝓕 k) (range (#(univ:Finset V) + 2))).Nonempty := by
  use #(univ : Finset V) + 1
  simp
  unfold shatters_some
  push_neg
  intro A hA
  exfalso
  contrapose hA
  rw [show Fintype.card V = #univ by rfl]
  suffices #A ≤ #(univ:Finset V) by
    linarith
  refine card_le_card ?h.a
  exact subset_univ A




lemma indexVC_defined {V : Type*} [DecidableEq V] [Fintype V] {𝓕 : Finset (Finset V)} :
    (filter (fun k ↦ ¬shatters_some 𝓕 k) (range (#𝓕 + 1))).Nonempty := by
  use #𝓕
  simp
  intro h
  have := @pow_le_of_shatters V _ _ 𝓕 #𝓕 h
  have := pow_le #𝓕
  linarith

lemma not_shatter {V : Type*} [DecidableEq V] [Fintype V] {𝓕 : Finset (Finset V)} :
    (filter (fun k ↦ ¬shatters_some 𝓕 k) (range (#𝓕 + 1))).Nonempty := indexVC_defined

lemma not_shatter! {V : Type*} [DecidableEq V] [Fintype V] {𝓕 : Finset (Finset V)} :
    (filter (fun k ↦ ¬shatters_some 𝓕 k) (range (#(univ : Finset V) + 2))).Nonempty := indexVC!_defined

/-- The VC index is the VC dimension +1 for nonempty finite families, but can be defined for
families of all cardinalities. -/
def indexVC {V : Type*} [DecidableEq V] [Fintype V] (𝓕 : Finset (Finset V)) : ℕ :=
  Finset.min' (filter (fun k => ¬ shatters_some 𝓕 k) (range (𝓕.card + 1))) indexVC_defined


def indexVC! {V : Type*} [DecidableEq V] [Fintype V] (𝓕 : Finset (Finset V)) : ℕ :=
  Finset.min' (filter (fun k => ¬ shatters_some 𝓕 k) (range ((univ : Finset V).card + 2))) indexVC!_defined



lemma indexVC_emp {V : Type*} [DecidableEq V] [Fintype V] :
    indexVC (∅ : Finset (Finset V)) = 0 := by
      unfold indexVC
      simp
      apply le_antisymm
      · have := @min'_le ℕ _ (filter (fun k ↦ ¬shatters_some (∅ : Finset (Finset V)) k) {0})
          0 (by simp;exact empty_does_not_shatter 0)
        aesop
      have := @le_min' ℕ _ (filter (fun k ↦ ¬shatters_some (∅ : Finset (Finset V)) k) {0}) (by
        apply filter_nonempty_iff.mpr
        simp
        exact empty_does_not_shatter 0
      ) 0 (by intro y hy; simp at hy; aesop)
      simp_all

lemma indexVC!_emp {V : Type*} [DecidableEq V] [Fintype V] :
    indexVC! (∅ : Finset (Finset V)) = 0 := by
      unfold indexVC!
      simp
      apply le_antisymm
      · exact min'_le (filter (fun k ↦ ¬shatters_some (∅ : Finset (Finset V)) k) (range (Fintype.card V + 2)))
          0 (by simp;exact empty_does_not_shatter 0)
      have := @le_min' ℕ _ (filter (fun k ↦ ¬shatters_some (∅ : Finset (Finset V)) k) {0}) (by
        apply filter_nonempty_iff.mpr
        simp
        exact empty_does_not_shatter 0
      ) 0 (by intro y hy; simp at hy; aesop)
      simp_all


lemma dimVC_emp {V : Type*} [DecidableEq V] [Fintype V] :
    dimVC (∅ : Finset (Finset V)) = 0 := by simp [dimVC]

lemma dimVC!_emp {V : Type*} [DecidableEq V] [Fintype V] :
    dimVC! (∅ : Finset (Finset V)) = 0 := by simp [dimVC!]



theorem dim_index!  {V : Type*} [DecidableEq V] [Fintype V]
    (𝓕 : Finset (Finset V)) : dimVC! 𝓕 = indexVC! 𝓕 - 1 := by

  by_cases H : 𝓕 = ∅
  · subst H
    rw [dimVC!_emp,indexVC!_emp]
  · have h𝓕 : ∃ f, f ∈ 𝓕 := by
      apply Nonempty.exists_mem
      exact nonempty_iff_ne_empty.mpr H

    unfold dimVC! indexVC!
    simp_all
    apply le_antisymm
    · apply Nat.le_sub_one_of_lt
      by_contra hc
      simp at hc
      obtain ⟨x,hx⟩ := hc
      obtain ⟨y,hy⟩ := hx.2.2
      exact hx.2.1 <| shatters_monotone 𝓕 h𝓕 x y hy.2.2 hy.2.1
    · apply le_max'
      simp
      constructor
      · have h₀ : (filter (fun k ↦ ¬shatters_some 𝓕 k) (range (#(univ : Finset V) + 2))).min' not_shatter! <
          #(univ : Finset V) + 2 := by
            have := @min'_le ℕ _ (filter (fun k ↦ ¬shatters_some 𝓕 k) (range (#(univ : Finset V) + 2))) (#(univ : Finset V) + 1)
              (by
              simp; unfold shatters_some;push_neg;intro A hA
              exfalso
              contrapose hA
              suffices #A ≤ Fintype.card V by linarith
              show #A ≤ #univ
              apply card_le_card
              exact subset_univ A
            )
            linarith
        show (filter (fun k ↦ ¬shatters_some 𝓕 k) (range (#univ + 2))).min' _ - 1 < #univ + 1
        omega
      · by_contra H₀
        simp at H₀
        have h₀ : (filter (fun k ↦ ¬shatters_some 𝓕 k) (range (#(univ : Finset V) + 2))).min' not_shatter! - 1
          < (filter (fun k ↦ ¬shatters_some 𝓕 k) (range (#(univ : Finset V) + 2))).min' not_shatter! := by
          apply Nat.sub_one_lt
          intro hc
          have : ¬shatters_some 𝓕 0 := by
            have := min'_mem (filter (fun k ↦ ¬shatters_some 𝓕 k) (range (#(univ : Finset V) + 2))) not_shatter!
            simp at this
            have := this.2
            simp at *
            rw [hc] at this
            tauto
          exact this <| (equivVC 𝓕).mp <| Nat.zero_lt_of_ne_zero <| card_ne_zero.mpr <| nonempty_iff_ne_empty.mpr H
        have := (@lt_min'_iff ℕ _ (filter (fun k ↦ ¬shatters_some 𝓕 k) (range (#(univ : Finset V) + 2))) not_shatter!
          ((filter (fun k ↦ ¬shatters_some 𝓕 k) (range (#(univ : Finset V) + 2))).min' not_shatter! - 1)).mp h₀
          ((filter (fun k ↦ ¬shatters_some 𝓕 k) (range (#(univ : Finset V) + 2))).min' not_shatter! - 1)
          (by
            simp
            constructor
            · suffices (filter (fun k ↦ ¬shatters_some 𝓕 k) (range (#(univ : Finset V) + 2))).min' not_shatter! < #(univ : Finset V) + 2 by
                have : Fintype.card V = #(univ : Finset V) := rfl
                simp_rw [this]
                linarith
              have := min'_mem (filter (fun k ↦ ¬shatters_some 𝓕 k) (range (#(univ : Finset V) + 2))) not_shatter!
              simp at this
              exact this.1
            exact H₀
          )
        simp at this


/-- Obtain dimVC from indexVC.
 Since dimVC ∅ = 0 and indexVC ∅ x= 0, this relies on 0 - 1 = 0.
-/
theorem dim_index  {V : Type*} [DecidableEq V] [Fintype V]
    (𝓕 : Finset (Finset V)) : dimVC 𝓕 = indexVC 𝓕 - 1 := by
  by_cases H : 𝓕 = ∅
  · subst H
    rw [dimVC_emp,indexVC_emp]
  · have h𝓕 : ∃ f, f ∈ 𝓕 := by
      apply Nonempty.exists_mem
      exact nonempty_iff_ne_empty.mpr H

    unfold dimVC indexVC
    simp_all
    apply le_antisymm
    · apply Nat.le_sub_one_of_lt
      by_contra hc
      simp at hc
      obtain ⟨x,hx⟩ := hc
      obtain ⟨y,hy⟩ := hx.2.2
      exact hx.2.1 <| shatters_monotone 𝓕 h𝓕 x y hy.2.2 hy.2.1
    · apply le_max'
      simp
      constructor
      · suffices (filter (fun k ↦ ¬shatters_some 𝓕 k) (range (#𝓕 + 1))).min' not_shatter < #𝓕 + 1 by
          calc
          _ ≤ (filter (fun k ↦ ¬shatters_some 𝓕 k) (range (#𝓕 + 1))).min' not_shatter := by omega
          _ < _ := this
        suffices (filter (fun k ↦ ¬shatters_some 𝓕 k) (range (#𝓕 + 1))).min' not_shatter ≤ #𝓕 by linarith
        apply @min'_le ℕ _
        simp
        intro h
        linarith [pow_le_of_shatters 𝓕 #𝓕 h, pow_le #𝓕]
      · by_contra H₀
        simp at H₀
        have h₀ : (filter (fun k ↦ ¬shatters_some 𝓕 k) (range (#𝓕 + 1))).min' not_shatter - 1
          < (filter (fun k ↦ ¬shatters_some 𝓕 k) (range (#𝓕 + 1))).min' not_shatter := by
          apply Nat.sub_one_lt
          intro hc
          have : ¬shatters_some 𝓕 0 := by
            have := min'_mem (filter (fun k ↦ ¬shatters_some 𝓕 k) (range (#𝓕 + 1))) not_shatter
            simp at this
            rw [hc] at this
            exact this.2
          exact this <| (equivVC 𝓕).mp <| Nat.zero_lt_of_ne_zero <| card_ne_zero.mpr <| nonempty_iff_ne_empty.mpr H
        have := (@lt_min'_iff ℕ _ (filter (fun k ↦ ¬shatters_some 𝓕 k) (range (#𝓕 + 1))) not_shatter
          ((filter (fun k ↦ ¬shatters_some 𝓕 k) (range (#𝓕 + 1))).min' not_shatter - 1)).mp h₀
          ((filter (fun k ↦ ¬shatters_some 𝓕 k) (range (#𝓕 + 1))).min' not_shatter - 1)
          (by
            simp
            constructor
            · suffices (filter (fun k ↦ ¬shatters_some 𝓕 k) (range (#𝓕 + 1))).min' not_shatter < #𝓕 + 1 by
                linarith
              have := min'_mem (filter (fun k ↦ ¬shatters_some 𝓕 k) (range (#𝓕 + 1))) not_shatter
              simp at this
              exact this.1
            exact H₀
          )
        simp at this


lemma VC_mono {V : Type*} [DecidableEq V] [Fintype V] (𝓕 𝓖 : Finset (Finset V))
 (h𝓕 : ∃ f, f ∈ 𝓕) (h𝓖 : ∃ g, g ∈ 𝓖)
  (h : 𝓕 ⊆ 𝓖) : dimVC 𝓕 ≤ dimVC 𝓖 := by
    suffices ∀ k, k ≤ dimVC 𝓕 → k ≤ dimVC 𝓖 by
      exact this (dimVC 𝓕) (le_refl _)
    intro k hf
    rw [VC_works] at hf ⊢
    obtain ⟨A,hA⟩ := hf
    use A
    simp_all
    intro B hB
    obtain ⟨C,hC⟩ := hA.2 B hB
    use C
    tauto
    exact h𝓖
    exact h𝓕

lemma VC!_mono {V : Type*} [DecidableEq V] [Fintype V] (𝓕 𝓖 : Finset (Finset V))
  (h : 𝓕 ⊆ 𝓖) : dimVC! 𝓕 ≤ dimVC! 𝓖 := by
    by_cases h𝓕 : ∃ f, f ∈ 𝓕
    have h𝓖 : ∃ g, g ∈ 𝓖 := by aesop
    suffices ∀ k, k ≤ dimVC! 𝓕 → k ≤ dimVC! 𝓖 by
      exact this (dimVC! 𝓕) (le_refl _)
    intro k hf
    rw [VC!_works] at hf ⊢
    obtain ⟨A,hA⟩ := hf
    use A
    simp_all
    intro B hB
    obtain ⟨C,hC⟩ := hA.2 B hB
    use C
    tauto
    exact h𝓖
    exact h𝓕
    · have : 𝓕 = ∅ := by aesop
      subst this
      rw [show dimVC! ∅ = 0 by rfl]
      simp

lemma VC_trivBound  {V : Type*} [DecidableEq V] [Fintype V]
    (𝓕 : Finset (Finset V)) (h𝓕 : ∃ f, f ∈ 𝓕) :
    dimVC 𝓕 ≤ (univ : Finset V).card := by
  suffices ∀ k, k ≤ dimVC 𝓕 → k ≤ (univ : Finset V).card by
    exact this (dimVC 𝓕) (le_refl _)
  intro k hk
  rw [VC_works] at hk
  obtain ⟨A,hA⟩ := hk
  rw [← hA.1]
  exact card_le_univ A
  exact h𝓕

lemma VC!_trivBound  {V : Type*} [DecidableEq V] [Fintype V]
    (𝓕 : Finset (Finset V)) (h𝓕 : ∃ f, f ∈ 𝓕) :
    dimVC! 𝓕 ≤ (univ : Finset V).card := by
  suffices ∀ k, k ≤ dimVC! 𝓕 → k ≤ (univ : Finset V).card by
    exact this (dimVC! 𝓕) (le_refl _)
  intro k hk
  rw [VC!_works] at hk
  obtain ⟨A,hA⟩ := hk
  rw [← hA.1]
  exact card_le_univ A
  exact h𝓕

/-- Kathleen Romanik's testing dimension, index version. -/
def indexTest {V : Type*} [DecidableEq V] [Fintype V] (𝓕 : Finset (Finset V))
  (hf : ∃ B, B ∉ 𝓕) : ℕ :=
    Finset.min' (filter (fun k => ¬ shatters_all 𝓕 k) (range ((univ:Finset V).card + 1))) (by
  unfold shatters_all
  push_neg
  simp
  use #(univ : Finset V)
  simp
  use univ
  simp
  tauto
)

/-- Kathleen Romanik's testing dimension. -/
def dimTest {V : Type*} [DecidableEq V] [Fintype V] (𝓕 : Finset (Finset V)) : ℕ := by
  by_cases H : 𝓕 = ∅
  · exact 0
  ·
    have : ∃ f, f ∈ 𝓕 := by
      refine Nonempty.exists_mem ?h
      exact nonempty_iff_ne_empty.mpr H
    exact Finset.max' (filter (fun k => shatters_all 𝓕 k) (range ((univ:Finset V).card + 1))) (by
    use 0
    simp
    intro A hA B hB
    obtain ⟨t,ht⟩ := this
    use t
    constructor
    tauto
    have : A = ∅ := by aesop
    have : B = ∅ := by
      apply subset_empty.mp
      simp_all
    aesop
  )


/-- The VC dimension of the powerset is the cardinality of the underlying set.
 Note that this does not require [Nonempty V]. -/
lemma dimVC_powerset  {V : Type*} [DecidableEq V] [Fintype V] :
    dimVC (univ : Finset (Finset V)) =
           (univ : Finset V).card := by
  suffices ∀ k, k ≤ dimVC (univ : Finset (Finset V)) ↔ k ≤ (univ : Finset V).card by
    apply le_antisymm
    apply (this (dimVC (univ : Finset (Finset V)))).mp
    simp
    rw [VC_works]
    use Finset.univ
    simp
    use univ
    simp
  intro k
  constructor
  · intro h
    calc
    _ ≤ _ := h
    _ ≤ _ := VC_trivBound (univ : Finset (Finset V)) (by use univ;simp)
  · intro h
    rw [VC_works]
    apply shatters_monotone
    use univ
    simp
    exact h
    use Finset.univ
    simp
    use univ
    simp

lemma dimVC!_powerset  {V : Type*} [DecidableEq V] [Fintype V] :
    dimVC! (univ : Finset (Finset V)) =
           (univ : Finset V).card := by
  suffices ∀ k, k ≤ dimVC! (univ : Finset (Finset V)) ↔ k ≤ (univ : Finset V).card by
    apply le_antisymm
    apply (this (dimVC! (univ : Finset (Finset V)))).mp
    simp
    rw [VC!_works]
    use Finset.univ
    simp
    use univ
    simp
  intro k
  constructor
  · intro h
    calc
    _ ≤ _ := h
    _ ≤ _ := VC!_trivBound (univ : Finset (Finset V)) (by use univ;simp)
  · intro h
    rw [VC!_works]
    apply shatters_monotone
    use univ
    simp
    exact h
    use Finset.univ
    simp
    use univ
    simp



lemma dimVC_eq  {V : Type*} [DecidableEq V] [Fintype V]
    (𝓕 : Finset (Finset V))
    (h𝓕 : ∃ f, f ∈ 𝓕 )
    (k : ℕ) :
    @shatters_some V _ 𝓕 k ∧ ¬ @shatters_some V _  𝓕 (k + 1) → dimVC 𝓕 = k := by
  intro ⟨h₀,h₁⟩
  rw [← VC_works _ h𝓕] at h₀ h₁
  linarith

lemma dimVC!_eq  {V : Type*} [DecidableEq V] [Fintype V]
    (𝓕 : Finset (Finset V))
    (h𝓕 : ∃ f, f ∈ 𝓕 )
    (k : ℕ) :
    @shatters_some V _ 𝓕 k ∧ ¬ @shatters_some V _  𝓕 (k + 1) → dimVC! 𝓕 = k := by
  intro ⟨h₀,h₁⟩
  rw [← VC!_works _ h𝓕] at h₀ h₁
  linarith


open Nat

section clog
theorem rescue_lemma_12 {m : ℕ} : (2 * m.succ).succ < 2 ^ (clog 2 (2 * m.succ).succ) := by
  cases (lt_or_eq_of_le (le_pow_clog one_lt_two _)) with
  | inl g => exact g
  | inr g =>
    exfalso
    obtain ⟨k,hk⟩ : ∃ k, clog 2 (succ (2 * m.succ)) = succ k :=
      exists_eq_succ_of_ne_zero <| pos_iff_ne_zero.mp <| clog_pos one_lt_two <| by linarith
    have : 2 ^ clog 2 (succ (2 * m.succ)) = 2 * 2^ (clog 2 (succ (2 * m.succ)) - 1) := by
      rw [hk, pow_succ]
      simp
      ring
    have h₀: Even ((2 * m.succ).succ) := g ▸ this ▸ even_two_mul _
    simp at h₀

end clog

section ν₂

/-- ν₂ is called t in the paper.  -/
def ν₂ := padicValNat 2


theorem ν₂_odd (n:ℕ) : ν₂ (2 * n+1) = 0 :=
  padicValNat.eq_zero_of_not_dvd fun ⟨k,hk⟩ =>
    (not_even_iff_odd).mpr (hk ▸ odd_two_mul_add_one n) <|even_two_mul k

theorem ν₂_2 (n:ℕ) (h:0<n) : ν₂ (2 * n) = ν₂ n + 1:= by
  rw [ν₂, padicValNat.mul (by linarith) (by linarith), add_comm]
  simp

end ν₂

section w

theorem bits_odd {n:ℕ} : bits (2 * n+1) = true :: bits n :=
  bits_append_bit n true (fun _ => rfl) ▸ rfl

theorem bits_even {n:ℕ} (h : n ≠ 0) : bits (2 * n) = false :: bits n :=
  bits_append_bit n false (False.elim ∘ h) ▸ rfl

theorem length_map_sum : ∀ l : List Bool, (l.map Bool.toNat).sum ≤ l.length
| [] => by simp
| head :: tail => by rw [List.length_cons,List.map_cons,List.sum_cons]; calc
  _ ≤ 1 + List.sum (List.map Bool.toNat tail) := add_le_add_right (Bool.toNat_le head) _
  _ ≤ 1 + List.length tail                    := add_le_add_left (length_map_sum _) _
  _ = succ (List.length tail)                 := by linarith

-- w = binaryHammingWeight (Lemma 11 of VC paper)
def hammingBits (n : ℕ) : ℕ := ((bits n).map Bool.toNat).sum

theorem hammingBits_2 (n:ℕ) : hammingBits (2 * n) = hammingBits n := by
  by_cases h : n = 0
  · simp [h]
  · unfold hammingBits
    rw [bits_even h]
    unfold Bool.toNat
    simp

theorem hammingBits_odd (n:ℕ) : hammingBits (2 * n+1) = hammingBits n + 1 := by
  unfold hammingBits
  rw [bits_odd]
  simp [add_comm]

theorem mentioned_in_lemma_12 {n s : ℕ} (h : n < 2^s) : hammingBits n ≤ s := calc
  _ ≤ List.length (bits n) := length_map_sum _
  _ ≤ _                    := by rw [size_eq_bits_len,size_le];exact h

theorem andhence {m : ℕ} : hammingBits (2 * m.succ) < clog 2 (2 * m.succ).succ := calc
  _ < hammingBits (2 * m.succ + 1) := by rw [hammingBits_odd,hammingBits_2]; simp
  _ ≤ _                            := mentioned_in_lemma_12 rescue_lemma_12

end w

theorem ν₂_hammingBits (n : ℕ) : ν₂ (n + 1) + hammingBits (n + 1) = hammingBits n + 1 := by
  induction' n using Nat.strong_induction_on with n ih -- https://leanprover-community.github.io/mathematics_in_lean/mathematics_in_lean.pdf
  by_cases hn : n = 0
  · simp [hn, ν₂, hammingBits]
  by_cases he : Even n
  · obtain ⟨k,hk⟩ := he
    have h₁ : 0 < k := Nat.pos_of_ne_zero fun _ => hn <| by linarith
    have h₂ : k < n := calc k < k + k := add_lt_add_left h₁ k
                            _ = n     := hk.symm
    have : hammingBits n = hammingBits k := by rw [← hammingBits_2 k, two_mul, hk]
    rw [this, ← ih k h₂] -- use ind.hyp.
    subst hk
    apply succ_injective
    conv =>
      right
      rw [succ_eq_add_one, add_assoc]
    rw [← two_mul,hammingBits_odd k, ← ih k h₂, ν₂_odd _]
    linarith

  · obtain ⟨k,hk⟩ := not_even_iff_odd.mp he
    subst hk
    rw [
      show 2 * k + 1 + 1 = 2 * (k + 1) by ring,
      hammingBits_2, hammingBits_odd, ν₂_2, add_comm, ← add_assoc
    ]
    apply (add_left_inj _).mpr
    rw [add_comm, ih k] -- use ind.hyp.
    linarith
    linarith

/-- This function is called `a` at https://oeis.org/A005187 and we
name it in honor of Jörg Arndt. -/
def arndt : ℕ → ℕ
| 0 => 0
| succ k => arndt k + 1 + ν₂ (k+1)

/-- Jörg Arndt (2019) claimed this without proof
  as a resolution of a conjecture of Benoit Cloitre (2003).
  Cloitre is a coauthor of Shallit (2023) and Jean-Paul Allouche.
-/
lemma lemma11 : ∀ m, arndt m + hammingBits (2 * m) = 2 * m
| 0 => by
  simp
  · constructor
    · rfl
    · simp [hammingBits]
| succ n => add_right_cancel <|
  calc
    _ = arndt n + 1 + ν₂ n.succ + hammingBits (2*(n.succ))+ hammingBits (2 * n)  := rfl
    _ = arndt n + hammingBits (2 * n) + 1 + ν₂ n.succ + hammingBits (2 * n.succ) := by ring
    _ = (2 * n)         + 1 + ν₂ n.succ + hammingBits (2 * n.succ) := by rw [lemma11 n]
    _ = (2 * n) + 1 + (ν₂ n.succ + hammingBits (2 * n.succ))       := by ring
    _ = (2 * n) + 1 + (hammingBits (2 * n) + 1) := by rw [hammingBits_2, hammingBits_2, ν₂_hammingBits]
    _ = _                                       := by linarith

lemma lemma12 (n:ℕ) : arndt n + clog 2 n.succ ≥ 2 * n := by
  by_cases h: n = 0
  · subst h
    simp
  obtain ⟨m,hm⟩ := exists_eq_succ_of_ne_zero h
  subst hm
  have : 2 ≤ (2 * m.succ).succ := le_of_ble_eq_true rfl
  have hkey: clog 2 (succ m.succ) + 1 ≥ clog 2 (succ (2 * m.succ)) := by
    rw [clog_of_two_le one_lt_two this] -- strange but wonderful!
    simp
  have : arndt m.succ + clog 2 (succ m.succ) + 1 > 2 * m.succ := calc
     _ ≥ arndt m.succ + clog 2 (succ (2 * m.succ)) := add_le_add_left hkey _
     _ > arndt m.succ + hammingBits (2 * m.succ)   := add_lt_add_left (@andhence m) _
     _ = 2 * m.succ                                := lemma11 m.succ
  exact lt_succ.mp this
