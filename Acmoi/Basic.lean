import Mathlib.Data.Nat.Size
import Mathlib.NumberTheory.Padics.PadicVal.Basic
/-!

  # VC-dimensions of nondeterministic finite automata for words of equal length

    Definition 10, Lemma 11, and Lemma 12 from the paper.
    (Bonus material for ac-exercises)

-/

open Nat

section clog
theorem rescue_lemma_12 {m : ℕ} : (2 * (m+1)) + 1 < 2 ^ (clog 2 (2 * m.succ).succ) := by
  cases (lt_or_eq_of_le (le_pow_clog one_lt_two _)) with
  | inl g => exact g
  | inr g =>
    exfalso
    obtain ⟨k,hk⟩ : ∃ k, clog 2 ((2 * (m+1)) + 1) = k + 1 :=
      exists_eq_succ_of_ne_zero <| pos_iff_ne_zero.mp <| clog_pos one_lt_two <| by linarith
    have : 2 ^ clog 2 (succ (2 * m.succ)) = 2 * 2^ (clog 2 (succ (2 * m.succ)) - 1) := by
      rw [hk, pow_succ]
      exact (Nat.mul_comm _ _).symm
    exact not_even_bit1 _ <| g ▸ this ▸ even_two_mul _

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
