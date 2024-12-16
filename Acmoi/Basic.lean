import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.Algebra.Order.Floor
import Mathlib.Data.Nat.Log
import Mathlib.InformationTheory.Hamming

set_option tactic.hygienic false

/-!

  # VC-dimensions of nondeterministic finite automata for words of equal length
    Definition 10, Lemma 11, and Lemma 12 from the paper.
    (Bonus material for ac-exercises)

-/

open Nat

section clog
theorem rescue_lemma_12 {n : ℕ} (h: n ≠ 0) : (2 * n).succ < 2 ^ (clog 2 (2 * n).succ) := by
  cases (lt_or_eq_of_le (le_pow_clog one_lt_two _)) with
  | inl g => exact g
  | inr g =>
    exfalso
    obtain ⟨m,hm⟩ := exists_eq_succ_of_ne_zero h
    obtain ⟨k,hk⟩ : ∃ k, clog 2 (succ (2 * n)) = succ k :=
      exists_eq_succ_of_ne_zero <| pos_iff_ne_zero.mp <| clog_pos one_lt_two <| by linarith
    have : 2 ^ clog 2 (succ (2 * n)) = 2 * 2^ (clog 2 (succ (2 * n)) - 1) := by
      rw [hk, pow_succ]
      simp
      ring
    have h₀: Even ((2 * n).succ) := g ▸ this ▸ even_two_mul _
    simp at h₀

end clog

section t

def t := padicValNat 2


theorem t_odd (n:ℕ) : t (2 * n+1) = 0 :=
  padicValNat.eq_zero_of_not_dvd fun ⟨k,hk⟩ =>
    (not_even_iff_odd).mpr (hk ▸ odd_two_mul_add_one n) <|even_two_mul k

theorem t_odd' (n:ℕ) : t (n+n+1) = 0:= by
  rw [← t_odd]
  congr
  ring

theorem t_2 (n:ℕ) (h:0<n) : t (2 * n) = t n + 1:= by
  unfold t
  rw [padicValNat.mul (by linarith) (by linarith)]
  rw [add_comm]
  simp

end t

section w

theorem bits_odd {n:ℕ} : bits (2 * n+1) = true :: bits n :=
  bits_append_bit n true (fun _ => rfl) ▸ rfl

theorem bits_even {n:ℕ} (h : n ≠ 0) : bits (2 * n) = false :: bits n :=
  bits_append_bit n false (False.elim ∘ h) ▸ rfl

theorem length_map_sum : ∀ l : List Bool, (l.map Bool.toNat).sum ≤ l.length
| [] => by simp
| head :: tail => by rw [List.length_cons,List.map_cons,List.sum_cons]; calc
  Bool.toNat head + List.sum (List.map Bool.toNat tail) ≤ 1 + List.sum (List.map Bool.toNat tail) := add_le_add_right (Bool.toNat_le head) _
  _                                   ≤ 1 + List.length tail           := add_le_add_left (length_map_sum _) _
  _                                   = succ (List.length tail)    := by linarith

-- w = binaryHammingWeight (Lemma 11 of VC paper)
def w (n : ℕ) : ℕ := ((bits n).map Bool.toNat).sum

theorem w_2 (n:ℕ) : w (2 * n) = w n := by
  unfold w
  by_cases h : n = 0
  · subst h
    rfl
  · rw [bits_even h]
    unfold Bool.toNat
    simp


theorem w_odd (n:ℕ) : w (2 * n+1) = w n + 1 := by
  unfold w Bool.toNat
  rw [bits_odd]
  simp
  rw [add_comm]

theorem w_odd' (n:ℕ) : w (n+n + 1) = w n + 1:= by rw [← w_odd n]; congr; ring

theorem mentioned_in_lemma_12 {n s : ℕ} (h : n < 2^s) : w n ≤ s := calc
  _ ≤ List.length (bits n) := length_map_sum _
  _ ≤ _                    := by rw [size_eq_bits_len,size_le];exact h

theorem andhence {n : ℕ} (h:n ≠ 0) : w (2 * n) < clog 2 (2 * n).succ := calc
  w (2 * n) < w (2 * n + 1) := by rw [w_odd,w_2]; simp
  _         ≤ _             := mentioned_in_lemma_12 (rescue_lemma_12 h)

end w

lemma t2 : t 2 = 1 := by unfold t;simp
lemma t3 : t 3 = 0 := by unfold t;simp
lemma w0 : w 0 = 0 := by unfold w;simp
lemma w1 : w 1 = 1 := by unfold w;simp
lemma w2 : w 2 = 1 := by rw [← mul_one 2,w_2];exact w1
lemma w3 : w 3 = 2 := by rw [show 3 = 2 * 1 + 1 by ring, w_odd, w1]

theorem lemma11_01 (n:ℕ) : t (n + 1) + w (n + 1) = w n + 1 := by
    induction' n using Nat.strong_induction_on with n ih -- https://leanprover-community.github.io/mathematics_in_lean/mathematics_in_lean.pdf
    by_cases hn : n = 0
    · subst hn
      unfold t w
      simp
    by_cases he : Even n
    · obtain ⟨k,hk⟩ := he
      have h₁ : 0 < k := Nat.pos_of_ne_zero fun _ => hn <| by linarith
      have h₂ : k < n := calc
        k < k + k := add_lt_add_left h₁ k
        _ = n     := hk.symm
      have : w n = w k := by rw [← w_2 k, two_mul, hk]
      rw [this, ← ih k h₂]
      subst hk
      apply succ_injective
      conv =>
        right
        rw [succ_eq_add_one,add_assoc]
      rw [w_odd' k, ← ih k h₂, t_odd' _]
      linarith

    · obtain ⟨k,hk⟩ := not_even_iff_odd.mp he
      subst hk
      rw [
        show 2 * k + 1 + 1 = 2 * (k + 1) by ring,
        w_2, w_odd, t_2, add_comm, ← add_assoc
      ]
      apply (add_left_inj _).mpr
      rw [add_comm, ih k]
      linarith
      linarith

theorem lemma11_1 (n:ℕ) : t n.succ + w (2 * (n + 1)) = w (2 * n) + 1 := by
  rw [w_2,w_2]
  exact lemma11_01 _

def a : ℕ → ℕ
| 0 => 0
| succ k => a k + 1 + t (k+1)

lemma lemma11 : ∀ m, a m + w (2 * m) = 2 * m
| 0 => by
  simp
  · constructor
    · rfl
    · unfold w;simp
| succ n => add_right_cancel <|
  calc
    _ = a n + 1 + t n.succ + w (2*(n.succ))+ w (2 * n)  := rfl
    _ = a n + w (2 * n) + 1 + t n.succ + w (2 * n.succ) := by ring
    _ = (2 * n)         + 1 + t n.succ + w (2 * n.succ) := by rw [lemma11 n]
    _ = (2 * n) + 1 + (t n.succ + w (2 * n.succ))       := by ring
    _ = (2 * n) + 1 + (w (2 * n) + 1)                   := by rw [lemma11_1]
    _ = _                                               := by linarith

lemma lemma12 (n:ℕ) : a n + clog 2 n.succ ≥ 2 * n := by
  by_cases h: n = 0
  · subst h
    simp
  have : 2 ≤ (2 * n).succ := le_of_lt (calc
         2 ≤ 2 * n        := mul_le_mul_left 2 (one_le_iff_ne_zero.mpr h)
         _ < (2 * n).succ := lt.base (2 * n))
  have hkey: clog 2 (succ n) + 1 ≥ clog 2 (succ (2 * n)) := by
    rw [clog_of_two_le one_lt_two this] -- strange but wonderful!
    simp
  have : a n + clog 2 (succ n) + 1   ≥ (2 * n).succ := calc
     _ ≥ a n + clog 2 (succ (2 * n)) := add_le_add_left hkey _
     _ > a n + w (2 * n) := add_lt_add_left (andhence h) _
     _ = 2 * n           := lemma11 n
  exact lt_succ.mp this
