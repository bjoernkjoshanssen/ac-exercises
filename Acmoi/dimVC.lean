import Mathlib.NumberTheory.Padics.PadicNumbers
-- import Mathlib.Algebra.Order.Floor
import Mathlib.Data.Nat.Log
import Mathlib.InformationTheory.Hamming
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fin.Tuple.Take
import Mathlib

/-!

  # VC-dimensions of nondeterministic finite automata for words of equal length
    Part 1: Define VC dimension and VC index and prove
    `dimVC = indexVC - 1` (even in the case of the empty family)


-/
section Basics
variable {V : Type*} [DecidableEq V] [Fintype V]

/-- To make this computable, restrict A ⊆ ⋃ 𝓕 -/
def shatters_some (𝓕 : Finset (Finset V)) (d : ℕ) : Prop :=
    ∃ A, A.card = d ∧ ∀ B ⊆ A, ∃ C ∈ 𝓕, A ∩ C = B

/-- Perhaps more natural to say: there is such a set, and 𝓕 shatters them all. -/
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
  use A

open Finset


/-- Shattering some set of size 0 or 1 is equivalent to having cardinality at least 2^0 or 2^1, respectively. -/
theorem shatters_some₀ {V : Type*} [DecidableEq V] [Fintype V] (F: Finset (Finset V)) :
    F ≠ ∅ ↔ shatters_some F 0 := by
  constructor
  · intro h
    exact nonempty_shatters F (nonempty_iff_ne_empty.mpr h).exists_mem.choose_spec
  · intro h hc
    exact empty_does_not_shatter (V := V) (k := 0) <| hc ▸ h


/-- Shattering some set of size 0 or 1 is equivalent to having cardinality at least 2^0 or 2^1, respectively. -/
theorem shatters_some₁ {V : Type*} [DecidableEq V] [Fintype V] (𝓕: Finset (Finset V)) :
    (∃ A ∈ 𝓕, ∃ B ∈ 𝓕, A ≠ B) ↔ shatters_some 𝓕 1 := by
  constructor
  · intro h
    obtain ⟨A,hA⟩ := h
    obtain ⟨B,hB⟩ := hA.2
    have : ∃ u, ¬ (u ∈ A ↔ u ∈ B) := by
      by_contra hc
      push Not at hc
      simp_all [Finset.ext_iff.mpr hc]
    obtain ⟨u,hu⟩ := this
    use {u}
    constructor
    · simp
    · intro X hX
      simp at hX
      cases hX
      · push Not at hu
        cases hu
        · use B
          simp_all
        · use A
          simp_all
      · push Not at hu
        cases hu
        · use A
          simp_all
        · use B
          simp_all
  · intro ⟨S,hS⟩
    obtain ⟨A,hA⟩ := hS.2 ∅ (by tauto)
    obtain ⟨B,hB⟩ := hS.2 S (by tauto)
    use A
    simp_all
    use B
    simp_all
    intro hc
    subst hc
    have : S = ∅ := by
      ext s
      simp
      intro hc
      have h₀ : s ∈ S ∩ A := by simp;tauto
      simp_all [hA.2]
    simp_all



/-- The VC dimension of a finite set family. -/
def dimVC {V : Type*} [DecidableEq V] [Fintype V]
    (𝓕 : Finset (Finset V)) : ℕ := by
  by_cases H : 𝓕 = ∅
  exact 0 -- dummy value, should really be -1 but that is inconvenient in Lean
  exact Finset.max'
    (filter (shatters_some 𝓕) (range ((univ : Finset V).card + 1))) (by
      use 0
      simp
      exact (shatters_some₀ 𝓕).mp H
      )

open Finset

/-- Obtain a smaller subset of a given set. -/
theorem subset_of_size {α : Type*} {s : Finset α} (a b : ℕ)
    (h_card : s.card = b) (h_le : a ≤ b) :
    ∃ t ⊆ s, t.card = a := by
  classical
  -- Extract the list representation of `s`
  let l := s.toList
  have h_length : l.length = b := by
    have := @List.toFinset_card_of_nodup α _ l (nodup_toList s)
    aesop
  let t := (l.take a).toFinset
  have h_subset : t ⊆ s := by
    intro x hx
    rw [List.mem_toFinset] at hx
    have : x ∈ List.take a s.toList := hx
    refine mem_toList.mp ?_
    exact List.mem_of_mem_take hx
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
  exact ⟨t, h_subset, h_card_t⟩

theorem not_shatters_all_empty {V : Type*} [DecidableEq V] [Fintype V]
    (k : ℕ) (hk : k ≤ Fintype.card V):
    ¬ shatters_all (∅:Finset (Finset V)) k := by
  intro hc
  obtain ⟨t,ht⟩ := @subset_of_size V univ k #(univ : Finset V) rfl hk
  have f := hc t ht.2
  have : shatters_some (∅ : Finset (Finset V)) k := by use t; simp_all
  exact @empty_does_not_shatter V _ k this

theorem not_shatters_all_emp {V : Type*} [DecidableEq V] [Fintype V] :
    ¬shatters_all (∅:Finset <|Finset V) 0 := by
  apply not_shatters_all_empty
  simp


theorem shatters_all₀ {V : Type*} [DecidableEq V] [Fintype V] (F: Finset (Finset V)) :
    F ≠ ∅ ↔ shatters_all F 0 := by
  constructor
  · intro h A hA B hB
    simp at hA
    subst hA
    simp
    constructor
    exact Nonempty.exists_mem <| nonempty_iff_ne_empty.mpr h
    exact .symm <| subset_empty.mp hB
  · exact fun h hc => not_shatters_all_empty 0 (zero_le) <| hc ▸ h



/-- A family can also shatter a smaller set. -/
lemma shatters_monotone {V : Type*} [DecidableEq V] [Fintype V]
    (𝓕 : Finset (Finset V)) (k l : ℕ) (h : k ≤ l)
    (h₀ : shatters_some 𝓕 l) : shatters_some 𝓕 k := by
  obtain ⟨A₀,hA₀⟩ := h₀
  obtain ⟨A,hA⟩ := @subset_of_size V A₀ k l hA₀.1 h
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
  sorry
  -- refine (Nat.pow_le_iff_le_log ?hb ?hy).mp this
  -- simp
  -- intro hc
  -- rw [hc] at this
  -- simp at this


lemma pow_le (m : ℕ) : m < 2 ^ m := by
  induction m with
        | zero => simp
        | succ n ih =>
          calc
          n + 1 < 2^n + 1 := by linarith
          _ ≤ _ := by ring_nf;linarith


theorem dimVC_def {V : Type*} [DecidableEq V] [Fintype V] (𝓕 : Finset (Finset V))
    (h𝓕 : ∃ f, f ∈ 𝓕) (k : ℕ) :
  k ≤ dimVC 𝓕 ↔ shatters_some 𝓕 k := by
  have hemp : 𝓕 ≠ ∅ := nonempty_iff_ne_empty.mp h𝓕
  constructor
  · intro h
    apply shatters_monotone 𝓕 k _ h
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
    unfold dimVC
    simp_all
  intro h₁
  have := le_max' (filter (shatters_some 𝓕) (range (#(univ : Finset V) + 1))) k
  unfold dimVC
  simp_all
  apply this
  obtain ⟨t,ht⟩ := h₁
  rw [← ht.1]
  refine card_le_card ?mpr.intro.a
  exact subset_univ t



/-- The VC dimension is bounded by the logarithm of the cardinality.
 This is one of the bounds listed in Wikipedia. -/
theorem pow_le_of_shatters₃! {V : Type*} [DecidableEq V] [Fintype V]
    (𝓕 : Finset (Finset V)) (h𝓕 : ∃ f, f ∈ 𝓕) :
    dimVC 𝓕 ≤ Nat.log 2 𝓕.card := by
  suffices ∀ k, k ≤ dimVC 𝓕 → k ≤ Nat.log 2 𝓕.card by
    apply this <| dimVC 𝓕
    simp
  intro k hk
  rw [dimVC_def] at hk
  exact @pow_le_of_shatters₂ V _ _ 𝓕 k hk
  exact h𝓕

lemma indexVC_as_min'_defined {V : Type*} [DecidableEq V] [Fintype V] {𝓕 : Finset (Finset V)} :
    (filter (fun k ↦ ¬shatters_some 𝓕 k) (range (#(univ:Finset V) + 2))).Nonempty := by
  use #(univ : Finset V) + 1
  simp
  unfold shatters_some
  push Not
  intro A hA
  exfalso
  contrapose hA
  rw [show Fintype.card V = #univ by rfl]
  suffices #A ≤ #(univ:Finset V) by
    linarith
  refine card_le_card ?h.a
  exact subset_univ A


lemma not_shatter_ {V : Type*} [DecidableEq V] [Fintype V] {𝓕 : Finset (Finset V)} :
    (filter (fun k ↦ ¬shatters_some 𝓕 k) (range (#𝓕 + 1))).Nonempty := by
  use #𝓕
  simp
  intro h
  have := @pow_le_of_shatters V _ _ 𝓕 #𝓕 h
  have := pow_le #𝓕
  linarith


/-- The VC index is the VC dimension +1 for nonempty finite families, but can be defined for
families of all cardinalities. -/
def indexVC {V : Type*} [DecidableEq V] [Fintype V] (𝓕 : Finset (Finset V)) : ℕ := by
  by_cases H : shatters_some 𝓕 (univ : Finset V).card
  · exact (univ : Finset V).card + 1
  exact Finset.min' (filter (fun k => ¬ shatters_some 𝓕 k) (range ((univ : Finset V).card + 1))) (by
    use #(univ : Finset V);simp;exact H
  )

def indexVC_as_min' {V : Type*} [DecidableEq V] [Fintype V] (𝓕 : Finset (Finset V)) : ℕ :=
  Finset.min' (filter (fun k => ¬ shatters_some 𝓕 k) (range ((univ : Finset V).card + 2))) indexVC_as_min'_defined


theorem too_big_to_shatter {V : Type*} [DecidableEq V] [Fintype V]
(𝓕 : Finset (Finset V)) : ¬shatters_some 𝓕 (Fintype.card V + 1) := by
  unfold shatters_some
  push Not
  intro A hA
  exfalso
  have : #A ≤ Fintype.card V := by
    show #A ≤ #univ
    apply card_le_card
    exact subset_univ A
  omega

theorem shatters_some_mono {k l : ℕ} (h₀ : k ≤ l)
    {V : Type*} [DecidableEq V] [Fintype V] {𝓕 : Finset (Finset V)}
    (h : shatters_some 𝓕 l) : shatters_some 𝓕 k := by
  obtain ⟨s,hs⟩ := h
  obtain ⟨t,ht⟩ := @subset_of_size V s k l hs.1 h₀
  use t
  constructor
  exact ht.2
  intro B hB
  obtain ⟨C,hC⟩ := hs.2 (B) (subset_trans hB ht.1)
  use C
  constructor
  tauto
  ext;simp
  constructor
  intro h
  rw [← hC.2]
  simp
  tauto

  intro h
  constructor
  tauto
  rw [← hC.2] at h
  simp at h
  tauto


theorem indexVC_as_min'_eq_indexVC {V : Type*} [DecidableEq V] [Fintype V] (𝓕 : Finset (Finset V)) :
    indexVC_as_min' 𝓕 = indexVC 𝓕 := by
  unfold indexVC_as_min' indexVC
  simp
  split_ifs with g₀
  · apply le_antisymm
    · apply min'_le
      simp
      apply too_big_to_shatter
    · apply le_min'
      intro y hy
      simp at hy
      by_contra H
      simp at H
      have : y ≤ Fintype.card V := by omega
      apply hy.2
      apply shatters_some_mono this g₀
  · apply le_antisymm
    · apply min'_le
      simp
      constructor
      · calc
        _ ≤ Fintype.card V := by
          apply min'_le
          simp
          exact g₀
        _ < _ := by omega
      · have := @min'_mem ℕ _
          (filter (fun k ↦ ¬shatters_some 𝓕 k) (range (Fintype.card V + 1)))
          (by use Fintype.card V;simp;exact g₀)
        simp at this
        exact this.2
    · apply le_min'
      intro y hy
      simp at hy
      -- "apply min'_le" would lead to False here.
      by_cases H : y = Fintype.card V + 1
      · subst H
        show (filter (fun k ↦ ¬shatters_some 𝓕 k) (range (Fintype.card V + 1))).min' _ ≤ Fintype.card V + 1
        suffices (filter (fun k ↦ ¬shatters_some 𝓕 k) (range (Fintype.card V + 1))).min' _ ≤ Fintype.card V by
          omega
        apply min'_le
        simp
        tauto
      · have : y ≤ Fintype.card V := by omega
        apply min'_le
        simp
        constructor
        omega
        tauto


lemma indexVC_as_min'_emp {V : Type*} [DecidableEq V] [Fintype V] :
    indexVC_as_min' (∅ : Finset (Finset V)) = 0 := by
      unfold indexVC_as_min'
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


/-- Obtain dimVC from indexVC.
 Since dimVC ∅ = 0 and indexVC ∅ x= 0, this relies on 0 - 1 = 0.
-/
theorem dim_index_VC {V : Type*} [DecidableEq V] [Fintype V]
    (𝓕 : Finset (Finset V)) : dimVC 𝓕 = indexVC 𝓕 - 1 := by
  rw [← indexVC_as_min'_eq_indexVC]
  by_cases H : 𝓕 = ∅
  · subst H
    rw [dimVC_emp,indexVC_as_min'_emp]
  · have h𝓕 : ∃ f, f ∈ 𝓕 := by
      apply Nonempty.exists_mem
      exact nonempty_iff_ne_empty.mpr H

    unfold dimVC indexVC_as_min'
    simp_all
    apply le_antisymm
    · apply Nat.le_sub_one_of_lt
      by_contra hc
      simp at hc
      obtain ⟨x,hx⟩ := hc
      obtain ⟨y,hy⟩ := hx.2.2
      exact hx.2.1 <| shatters_monotone 𝓕 x y hy.2.2 hy.2.1
    · apply le_max'
      simp
      constructor
      · have h₀ : (filter (fun k ↦ ¬shatters_some 𝓕 k) (range (#(univ : Finset V) + 2))).min' indexVC_as_min'_defined <
          #(univ : Finset V) + 2 := by
            have := @min'_le ℕ _ (filter (fun k ↦ ¬shatters_some 𝓕 k) (range (#(univ : Finset V) + 2))) (#(univ : Finset V) + 1)
              (by
              simp; unfold shatters_some;push Not;intro A hA
              exfalso
              contrapose hA
              suffices #A ≤ Fintype.card V by linarith
              show #A ≤ #univ
              apply card_le_card
              exact subset_univ A
            )
            linarith
        simp at h₀ ⊢
        omega
      · by_contra H₀
        -- simp at H₀
        have h₀ : (filter (fun k ↦ ¬shatters_some 𝓕 k) (range (#(univ : Finset V) + 2))).min' indexVC_as_min'_defined - 1
          < (filter (fun k ↦ ¬shatters_some 𝓕 k) (range (#(univ : Finset V) + 2))).min' indexVC_as_min'_defined := by
          apply Nat.sub_one_lt
          intro hc
          have : ¬shatters_some 𝓕 0 := by
            have := min'_mem (filter (fun k ↦ ¬shatters_some 𝓕 k) (range (#(univ : Finset V) + 2))) indexVC_as_min'_defined
            simp at this
            have := this.2
            simp at *
            rw [hc] at this
            tauto
          have := (shatters_some₀ 𝓕).mp H
          tauto
        have := (@lt_min'_iff ℕ _ (filter (fun k ↦ ¬shatters_some 𝓕 k) (range (#(univ : Finset V) + 2))) indexVC_as_min'_defined
          ((filter (fun k ↦ ¬shatters_some 𝓕 k) (range (#(univ : Finset V) + 2))).min' indexVC_as_min'_defined - 1)).mp h₀
          ((filter (fun k ↦ ¬shatters_some 𝓕 k) (range (#(univ : Finset V) + 2))).min' indexVC_as_min'_defined - 1)
          (by
            simp
            constructor
            · suffices (filter (fun k ↦ ¬shatters_some 𝓕 k) (range (#(univ : Finset V) + 2))).min' indexVC_as_min'_defined < #(univ : Finset V) + 2 by
                have : Fintype.card V = #(univ : Finset V) := rfl
                simp_rw [this]
                linarith
              have := min'_mem (filter (fun k ↦ ¬shatters_some 𝓕 k) (range (#(univ : Finset V) + 2))) indexVC_as_min'_defined
              simp at this
              exact this.1
            exact H₀
          )
        simp at this





lemma VC_mono {V : Type*} [DecidableEq V] [Fintype V] (𝓕 𝓖 : Finset (Finset V))
  (h : 𝓕 ⊆ 𝓖) : dimVC 𝓕 ≤ dimVC 𝓖 := by
    by_cases h𝓕 : ∃ f, f ∈ 𝓕
    have h𝓖 : ∃ g, g ∈ 𝓖 := by aesop
    suffices ∀ k, k ≤ dimVC 𝓕 → k ≤ dimVC 𝓖 by
      exact this (dimVC 𝓕) (le_refl _)
    intro k hf
    rw [dimVC_def] at hf ⊢
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
      rw [show dimVC ∅ = 0 by rfl]
      simp


lemma VC_trivBound  {V : Type*} [DecidableEq V] [Fintype V]
    (𝓕 : Finset (Finset V)) (h𝓕 : ∃ f, f ∈ 𝓕) :
    dimVC 𝓕 ≤ (univ : Finset V).card := by
  suffices ∀ k, k ≤ dimVC 𝓕 → k ≤ (univ : Finset V).card by
    exact this (dimVC 𝓕) (le_refl _)
  intro k hk
  rw [dimVC_def] at hk
  obtain ⟨A,hA⟩ := hk
  rw [← hA.1]
  exact card_le_univ A
  exact h𝓕

/-- Kathleen Romanik's testing dimension, index version. -/
def indexTest {V : Type*} [DecidableEq V] [Fintype V] (𝓕 : Finset (Finset V))
  : ℕ := by
  by_cases hf : ∃ B, B ∉ 𝓕
  exact Finset.min' (filter (fun k => ¬ shatters_all 𝓕 k) (range ((univ:Finset V).card + 1))) (by
    unfold shatters_all
    push Not
    simp
    use #(univ : Finset V)
    simp
    use univ
    simp
    tauto
  )
  exact (univ : Finset V).card + 1

/-- Kathleen Romanik's testing dimension,
 Source: Definition 2 of "VC-dimensions of nondeterministic finite automata for words of equal length".
 -/
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

theorem dimTest_le_dimVC {V : Type*} [DecidableEq V] [Fintype V] (𝓕 : Finset (Finset V)) :
  dimTest 𝓕 ≤ dimVC 𝓕 := by
  unfold dimVC dimTest
  by_cases H : 𝓕 = ∅
  · subst H
    simp
  · simp_all
    by_cases G : Fintype.card V = 0
    simp_rw [G]
    simp
    intro y hy h₀
    obtain ⟨t,ht⟩ := @subset_of_size V univ y (Fintype.card V) rfl (by linarith)
    exact @le_max' ℕ _ (filter (shatters_some 𝓕) (range (Fintype.card V + 1))) y
      (by
      simp
      constructor
      tauto
      use t
      constructor
      tauto
      unfold shatters_all at h₀
      tauto
    )


theorem shatters_all_mono  {V : Type*} [DecidableEq V] [Fintype V] {𝓕 : Finset (Finset V)}
    {k l : ℕ} (h : shatters_all 𝓕 l) (h₀ : k ≤ l) (h₁ : l ≤ (univ : Finset V).card) :
    shatters_all 𝓕 k := by
  unfold shatters_all at *
  intro A hA B hB
  -- now we need to extend A to size l !
  -- take A ∪ X where X is a set of size l-k in univ \ A.
  obtain ⟨X,hX⟩ := @subset_of_size V (univ \ A) (l-k) (univ \ A).card rfl (by
    have : #(univ \ A) = #(univ : Finset V) - #A := by
      rw [card_sdiff]
      simp
    rw [this]
    rw [hA]
    exact Nat.sub_le_sub_right h₁ k
  )
  have hAX : X ∩ A = ∅ := by
    have := hX.1
    ext x
    simp
    intro hx
    have := this hx
    apply mem_compl.mp
    exact this
  have hXA : A ∩ X = ∅ := by rw [inter_comm] at hAX;exact hAX
  obtain ⟨C,hC⟩ := h (A ∪ X) (by
    rw [card_union]

    rw [hXA];simp;rw [hA,hX.2,add_comm];exact Nat.sub_add_cancel h₀
  ) (B ∪ X) (by intro x hx;simp at hx;cases hx <;> (simp;tauto))
  use C
  constructor
  tauto
  have h₂ := hC.2
  have : ((A ∪ X) ∩ C) ∩ A = (B ∪ X) ∩ A := by rw[h₂]
  simp at this
  have : (B ∪ X) ∩ A = B := by rw [union_inter_distrib_right, hAX];simp_all
  have : (A ∪ X) ∩ (A ∩ C) = A ∩ C := by
    rw [union_inter_distrib_right];simp_all
  aesop

lemma please_nemp {V : Type*} [DecidableEq V] [Fintype V] {𝓕 : Finset (Finset V)} (G : ∃ B, B ∉ 𝓕) :
    (filter (fun k ↦ ¬shatters_all 𝓕 k) (range (Fintype.card V + 1))).Nonempty := by
  use #(univ : Finset V)
  simp
  unfold shatters_all
  push Not
  use univ
  simp
  tauto





theorem indexTest_le_indexVC {V : Type*} [DecidableEq V] [Fintype V] (𝓕 : Finset (Finset V)) :
    indexTest 𝓕 ≤ indexVC 𝓕 := by
  unfold indexTest indexVC
  by_cases hf : ∃ B, B ∉ 𝓕
  · simp_all
    apply min'_le
    simp
    constructor
    · split_ifs with g₀
      · obtain ⟨u,hu⟩ := g₀
        have hu₀ : u = univ := by
          have h₀ : u ⊆ univ := by aesop
          have h₁ : #u = #(univ : Finset V) := by tauto
          exact (card_eq_iff_eq_univ u).mp h₁
        obtain ⟨B,hB⟩ := hf
        subst hu₀
        have hu₁ := hu.2 B (by aesop)
        simp at hu₁
        tauto
      · --show (filter (fun k ↦ ¬shatters_some 𝓕 k) (range (Fintype.card V + 1))).min' _ < Fintype.card V + 1
        suffices (filter (fun k ↦ ¬shatters_some 𝓕 k) (range (Fintype.card V + 1))).min' (by use Fintype.card V;simp;tauto) ≤ Fintype.card V by
          omega
        apply min'_le
        simp
        tauto
    · by_cases h : shatters_some 𝓕 (Fintype.card V)
      simp_all
      exfalso
      obtain ⟨s,hs⟩ := h
      have hu : s = univ := by
          have h₀ : s ⊆ univ := by aesop
          have h₁ : #s = #(univ : Finset V) := by tauto
          exact (card_eq_iff_eq_univ s).mp h₁
      have := hs.2
      rw [hu] at this
      simp at this
      tauto
      contrapose h


      have := h univ
      simp_all
      split_ifs at * with g₀
      · tauto
      · simp_all
        clear this
        have h₀ := @subset_of_size V univ
        let g : ℕ := ((filter (fun k ↦ ¬shatters_some 𝓕 k) (range (Fintype.card V + 1))).min' (by
          use Fintype.card V; simp; tauto
        ))
        have := h₀ ((filter (fun k ↦ ¬shatters_some 𝓕 k) (range (Fintype.card V + 1))).min' (by
          use Fintype.card V; simp; tauto
        )) #(univ : Finset V) rfl (by apply min'_le;simp;exact g₀)
        obtain ⟨t,ht⟩ := this
        have := h t (by rw [ht.2])
        have : shatters_some 𝓕 #t := by use t
        have : ¬ shatters_some 𝓕 #t := by
          have := ht.2
          have h₀ := min'_mem (filter (fun k ↦ ¬shatters_some 𝓕 k) (range (Fintype.card V + 1)))
            (by use Fintype.card V;simp_all)
          simp at h₀
          have := h₀.2
          aesop
        tauto
  split_ifs with g₀
  · simp
  exfalso
  apply g₀
  use univ
  simp
  aesop


theorem dim_index_test {V : Type*} [DecidableEq V] [Fintype V] (𝓕 : Finset (Finset V)) :
    dimTest 𝓕 = indexTest 𝓕 - 1 := by
  unfold dimTest indexTest
  by_cases H : 𝓕 = ∅
  · subst H
    simp
    suffices (filter (fun k ↦ ¬shatters_all (∅ : Finset <|Finset V) k) (range (Fintype.card V + 1))).min' _ = 0 by
      omega
    apply le_antisymm
    exact @min'_le ℕ _ (filter (fun k ↦ ¬shatters_all (∅ : Finset <|Finset V) k) (range (Fintype.card V + 1))) 0
      (by simp;apply not_shatters_all_emp)
    simp
  by_cases G : ∃ B, B ∉ 𝓕
  · simp_all
    -- certainly true...
    apply le_antisymm
    apply Nat.le_sub_one_of_lt
    by_contra H
    simp at H
    obtain ⟨x,hx⟩ := H
    obtain ⟨y,hy⟩ := hx.2.2
    exact hx.2.1 <| shatters_all_mono hy.2.1 hy.2.2
      (by simp;exact hy.1)
    apply le_max'
    simp
    have h₀ := min'_mem (filter (fun k ↦ ¬shatters_all 𝓕 k) (range (Fintype.card V + 1)))
      (please_nemp G)
    have H₀: (filter (fun k ↦ ¬shatters_all 𝓕 k) (range (Fintype.card V + 1))).min' (please_nemp G) ≠ 0 := by
      intro hc
      rw [hc] at h₀
      simp at h₀
      apply h₀
      intro A hA B hB
      rw [card_eq_zero.mp hA] at *
      rw [subset_empty.mp hB]
      simp
      exact (nonempty_iff_ne_empty.mpr H).exists_mem
    constructor
    · simp at h₀
      omega
    · intro A hA
      let please := (filter (fun k ↦ ¬shatters_all 𝓕 k) (range (Fintype.card V + 1)))
      let g := ((filter (fun k ↦ ¬shatters_all 𝓕 k) (range (Fintype.card V + 1))).min' (please_nemp G))
      have h₁ : IsLeast please g := isLeast_min' please (please_nemp G)
      have h₆ : ¬ #A ∈ please := by
        intro hc
        have := h₁.2 hc
        omega
      have h₁ : #A < Fintype.card V + 1 := by
        suffices #A ≤ Fintype.card V by linarith
        exact card_le_card <| subset_univ A
      have h₃ : shatters_all 𝓕 #A := by
        suffices ¬ (#A ∈ filter (fun k ↦ ¬shatters_all 𝓕 k) (range (Fintype.card V + 1))) by
          simp at this;
          exact this (by omega)
        aesop
      exact h₃ A rfl
  simp_all
  apply le_antisymm
  · apply max'_le
    intro y hy
    simp at hy
    omega
  · apply le_max'
    simp
    intro A hA B hB
    use B
    constructor
    · exact G B
    · exact inter_eq_right.mpr hB


/-- The VC dimension of the powerset is the cardinality of the underlying set.
 Note that this does not require [Nonempty V]. -/
lemma dimVC_powerset  {V : Type*} [DecidableEq V] [Fintype V] :
    dimVC (univ : Finset (Finset V)) =
           (univ : Finset V).card := by
  suffices ∀ k, k ≤ dimVC (univ : Finset (Finset V)) ↔ k ≤ (univ : Finset V).card by
    apply le_antisymm
    apply (this (dimVC (univ : Finset (Finset V)))).mp
    simp
    rw [dimVC_def]
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
    rw [dimVC_def]
    apply shatters_monotone
    exact h
    use univ
    simp
    use Finset.univ
    simp

lemma dimVC_eq  {V : Type*} [DecidableEq V] [Fintype V] (𝓕 : Finset (Finset V))
    (h𝓕 : ∃ f, f ∈ 𝓕 )
    (k : ℕ) :
    shatters_some 𝓕 k ∧ ¬ shatters_some  𝓕 (k + 1) → dimVC 𝓕 = k := by
  intro ⟨h₀,h₁⟩
  rw [← dimVC_def _ h𝓕] at h₀ h₁
  linarith


/--
A diamond:

    indexVC
dimVC     indexTest
    dimTest


-/
theorem summarize {V : Type*} [DecidableEq V] [Fintype V] (𝓕 : Finset (Finset V)) :
    dimTest 𝓕 ≤ dimVC 𝓕     ∧     dimVC 𝓕 ≤ indexVC 𝓕 ∧
    dimTest 𝓕 ≤ indexTest 𝓕 ∧ indexTest 𝓕 ≤ indexVC 𝓕 := by
  constructor
  exact dimTest_le_dimVC 𝓕
  constructor
  rw [dim_index_VC]
  omega
  constructor
  rw [dim_index_test]
  omega
  exact indexTest_le_indexVC 𝓕

theorem counter₁ : ∃ V : Type, ∃ _ : DecidableEq V, ∃ _ : Fintype V, ∃ 𝓕 : Finset (Finset V),
    dimVC 𝓕 < indexTest 𝓕 := by
  use Fin 2
  use (instDecidableEqFin 2)
  use (Fin.fintype 2)
  use {{0},{1}}
  decide

theorem counter₂ : ∃ V : Type, ∃ _ : DecidableEq V, ∃ _ : Fintype V, ∃ 𝓕 : Finset (Finset V),
    dimVC 𝓕 > indexTest 𝓕 := by
  use Fin 3
  use (instDecidableEqFin 3)
  use (Fin.fintype 3)
  use {∅,{0},{1},{0,1}}
  decide
