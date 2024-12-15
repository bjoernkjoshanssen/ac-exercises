import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.Algebra.Order.Floor
import Mathlib.Data.Nat.Log

set_option tactic.hygienic false

/-!

  # VC-dimensions of nondeterministic finite automata for words of equal length
    Definition 10, Lemma 11, and Lemma 12 from the paper.
    (Bonus material for ac-exercises)

-/

def t : ℕ → ℕ := padicValNat 2

def a : ℕ → ℕ
| 0 => 0
| Nat.succ k => a k + 1 + t (k+1)


-- Instead of using Mathlib.Data.Nat.Digits we use:
def F : Bool → ℕ
| true => 1
| false => 0


-- w = binaryHammingWeight (Lemma 11 of VC paper)
def w (n : ℕ) : ℕ :=  List.sum <| List.map F <| Nat.bits n

theorem bits_bool (b:Bool) {n : ℕ} (h : n ≠ 0) : Nat.bits (Nat.bit b n) = b :: Nat.bits n :=
  Nat.bits_append_bit n b (False.elim ∘ h)


theorem bits_odd {n:ℕ} : Nat.bits (2*n+1) = true :: Nat.bits n :=
  Nat.bits_append_bit n true (fun _ => rfl) ▸ rfl

theorem bits_even {n:ℕ} (h : n ≠ 0) : Nat.bits (2*n) = false :: Nat.bits n := by
  rw [← bits_bool false h]
  congr

theorem w_2 (n:ℕ) : w (2*n) = w n := by
  unfold w
  by_cases h : n = 0
  · subst h
    rfl
  · rw [bits_even h]
    unfold F
    simp

theorem t_odd (n:ℕ) : t (2*n+1) = 0:= padicValNat.eq_zero_of_not_dvd fun ⟨k,hk⟩ =>
  (Nat.not_even_iff_odd).mpr (hk ▸ odd_two_mul_add_one n) <|even_two_mul k

theorem t_odd' (n:ℕ) : t (n+n+1) = 0:= by
  rw [← t_odd]
  congr
  ring

theorem t_2 (n:ℕ) (h:0<n) : t (2*n) = t n + 1:= by
  unfold t
  rw [padicValNat.mul (by linarith) (by linarith)]
  rw [add_comm]
  simp

theorem w_odd (n:ℕ) : w (2*n+1) = w n + 1 := by
  unfold w
  rw [bits_odd]
  simp
  rw [add_comm]
  unfold F
  simp

theorem w_odd' (n:ℕ) : w (n+n + 1) = w n + 1:= by {rw [← w_odd n]; congr; ring}

theorem lemma11_01 (n:ℕ) : t n.succ + w (n + 1) = w n + 1 := by
    induction' n using Nat.strong_induction_on with n ih -- https://leanprover-community.github.io/mathematics_in_lean/mathematics_in_lean.pdf
    by_cases he: (Even n)
    · obtain ⟨k,hk⟩ := he
      by_cases hn: (n=0)
      · subst hn; simp; unfold t; simp; unfold w; simp; rfl

      have h₁: 0 < k := Nat.pos_of_ne_zero (fun hc => hn <| by
        rw [hc] at hk; exact hk)
      have h₃: k < n := calc
        k < k + k := Nat.add_lt_add_left h₁ k
        _ = n := hk.symm
      let G := ih k h₃
      have : w n = w k := by rw [← w_2 k,two_mul,hk]
      rw [this, ← ih k h₃]
      subst hk
      by_cases hk : k = 1
      · subst hk
        repeat rw [Nat.succ_eq_add_one]
        rw [
          ←two_mul,
          w_2,
          w_odd,
          t_odd,
          t_2,
          t_odd 0
        ]
        ring; linarith
      · have : 1 < k := by
          by_contra hc
          cases Nat.not_lt.mp hc
          contrapose hk
          · simp
          · cases a
            simp at h₁
        apply Nat.succ_injective
        conv =>
          right
          rw [Nat.succ_eq_add_one,add_assoc]
        have hw: w (k + k + 1) = w k + 1 := w_odd' _
        rw [hw,← G,t_odd' _]
        simp
        linarith

    obtain ⟨k,hk⟩ := Nat.not_even_iff_odd.mp he
    subst hk
    have : w (2*k+1+1) = w (k+1) := w_2 (k+1) ▸ congr_arg w (by linarith)
    rw [this]
    have h₀: w (2*k+1) = w k + 1 := w_odd k
    rw [h₀]
    by_cases hk : k = 0
    · subst hk; simp
      simp at h₀
      rw [h₀]
      suffices t (2*1) = 1 by linarith
      rw [two_mul]
      rw [← Nat.succ_eq_add_one]
      unfold t
      simp
    · have : t ((2*(k+1))) = t (k+1) + 1 := t_2 _ (by linarith)
      have : t ((2*k+1).succ) = t (k+1) + 1 := by rw [←this]; congr
      rw [this,add_comm,← add_assoc]
      simp
      rw [add_comm]
      exact ih k (by linarith)

theorem lemma11_1 (n:ℕ) : t n.succ + w (2 * (n + 1)) = w (2 * n) + 1 := by
  rw [w_2,w_2]
  exact lemma11_01 _

theorem lemma11 : ∀ m, a m + w (2 * m) = 2 * m
| 0 => by
  simp
  · constructor
    · rfl
    · unfold w;simp
| Nat.succ n => Nat.add_right_cancel <|
  calc
    _ = a n + 1 + t n.succ + w (2*(n.succ))+ w (2*n) := rfl
    _ = a n + w (2*n) + 1 + t n.succ + w (2*n.succ)  := by ring
    _ = (2*n)         + 1 + t n.succ + w (2*n.succ)  := by rw [lemma11 n]
    _ = (2*n) + 1 + (t n.succ + w (2*n.succ))        := by ring
    _ = (2*n) + 1 + (w (2*n) + 1)                    := by rw [lemma11_1]
    _ = _                                            := by linarith

theorem boolBound (b:Bool) : F b ≤ 1 := by cases b <;> decide

theorem length_map_sum : ∀ l,  List.sum (List.map F (l)) ≤ List.length l
| [] => by simp
| head :: tail => by rw [List.length_cons,List.map_cons,List.sum_cons]; calc
  F head + List.sum (List.map F tail) ≤ 1 + List.sum (List.map F tail) := Nat.add_le_add_right (boolBound head) _
  _                                   ≤ 1 + List.length tail           := Nat.add_le_add_left (length_map_sum _) _
  _                                   = Nat.succ (List.length tail)    := by linarith


theorem rescue_lemma_12 (n:ℕ) (h: n ≠ 0) : (2*n).succ < 2 ^ (Nat.clog 2 (2*n).succ) := by
  cases (Nat.lt_or_eq_of_le (Nat.le_pow_clog Nat.one_lt_two _))
  · assumption
  · exfalso
    obtain ⟨m,hm⟩ := Nat.exists_eq_succ_of_ne_zero h
    have : Nat.clog 2 2 ≤ Nat.clog 2 (Nat.succ (2 * n)) := Nat.clog_mono_right 2 (by linarith)
    have : ∃ k, Nat.clog 2 (Nat.succ (2 * n)) = Nat.succ k := by
      apply Nat.exists_eq_succ_of_ne_zero
      apply Nat.pos_iff_ne_zero.mp
      have : Nat.clog 2 2 = 1 := by
        refine Nat.clog_eq_one ?hn ?h
        linarith;linarith
      linarith
    obtain ⟨k,hk⟩ := this
    have : 2 ^ Nat.clog 2 (Nat.succ (2 * n)) = 2 * 2^ (Nat.clog 2 (Nat.succ (2 * n)) - 1) := by
      rw [hk,pow_succ]
      simp
      ring
    have h₀: Even ((2*n).succ) := by {rw [h_1,this];exact even_two_mul _}
    revert h₀
    simp

theorem mentioned_in_lemma_12 {n s:ℕ} (h:n < 2^s) : w n ≤ s := calc
_ ≤ List.length (Nat.bits n) := by {unfold w; exact length_map_sum _}
_ ≤ _                        := by {rw [Nat.size_eq_bits_len,Nat.size_le,];assumption}

theorem andhence {n : ℕ} (h:n ≠ 0) : w (2*n) < Nat.clog 2 (2*n).succ := calc
  w (2*n) < w (2*n + 1) := by {rw [w_odd,w_2];simp;}
  _       ≤ _           := mentioned_in_lemma_12 (rescue_lemma_12 _ h)

theorem almost_lemma12 {n:ℕ} (h:n ≠ 0) : a n + Nat.clog 2 (2*n).succ > 2*n := calc
  _ > a n + w (2*n) := Nat.add_lt_add_left (andhence h) _
  _ = 2 * n := lemma11 n

theorem lemma12 (n:ℕ) : a n + Nat.clog 2 (n).succ ≥ 2*n := by
  by_cases h:(n=0); subst h;simp
  have : 2 ≤ (2*n).succ := le_of_lt (calc
         2 = 2*1        := by ring
         _ ≤ 2*n        := Nat.mul_le_mul_left 2 (Nat.one_le_iff_ne_zero.mpr h)
         _ < (2*n).succ := Nat.lt.base (2 * n))
  have hkey: Nat.clog 2 (Nat.succ n) + 1 ≥ Nat.clog 2 (Nat.succ (2 * n)) := by
    rw [Nat.clog_of_two_le one_lt_two this] -- strange but wonderful!
    simp
  have : a n + Nat.clog 2 (Nat.succ n) + 1   ≥ (2 * n).succ := calc
     _ ≥ a n + Nat.clog 2 (Nat.succ (2 * n)) := Nat.add_le_add_left hkey _
     _ ≥ _                                   := almost_lemma12 h
  exact Nat.lt_succ.mp this
