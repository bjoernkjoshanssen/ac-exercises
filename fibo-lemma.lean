import Mathlib.Data.Int.ModEq

theorem lemma_1_92
  (fib:ℕ→ℕ)
  (fib_add_two: ∀ {n:ℕ}, fib (n+2)=fib (n)+fib (n+1) )
  (t p s : ℕ)
  (h : fib (t+1) ≡ 0 [MOD p]) :
  2*s ≤ t → (fib (t+1+2*s) + fib (t+1-2*s) ≡ 0 [MOD p]) ∧ fib (t + 2+2*s) ≡ fib (t  - 2*s) [MOD p] :=
  Nat.recOn s (λ _ ↦
    And.intro
    ( -- Base case
      calc  fib (t+1) + fib (t+1)
          ≡ 0 +         fib (t+1) [MOD p] := Nat.ModEq.add h rfl
      _ = fib (t+1)                       := by ring_nf
      _ ≡ 0                     [MOD p]  := h
    ) (
      calc fib (t+2) = fib t + fib (t+1)        := fib_add_two
      _ ≡ fib t + 0         [MOD p] := Nat.ModEq.add rfl h
      _ = fib t                     := by ring_nf
    )
  ) (λ s h_ind hs ↦ -- Inductive step
      have hsk: ∀ k:ℕ, k ≤ 2 → k+2*s ≤ t := λ k hk ↦ calc
        k+2*s ≤ 2+2*s := add_le_add_right hk (2*s)
        _ = 2*(1+s) := (mul_one_add 2 s).symm
        _ = 2*(s+1) := by rw[add_comm]
        _ = 2*(s.succ) := rfl
        _ = 2*(Nat.succ s) := by ring
        _ ≤ t := hs
      have hs2: 2+2*s ≤ t := hsk 2 (le_refl 2)
      have hs1: 1+2*s ≤ t := hsk 1 (one_le_two)
      have hs0: 2*s ≤ t :=
(      calc
      2*s = 0+2*s := (zero_add (2*s)).symm
      _ ≤ t       := hsk 0 (zero_le_two)
)
      have ht2: 2 ≤ t-2*s := (le_tsub_iff_right hs0).mpr hs2
      have hs1: 1≤ t-2*s := (le_tsub_iff_right hs0).mpr hs1

      have help1: t-2*s-1=t+1-2*Nat.succ s :=
      (calc
      _ = t-2*s+1-2   := by exact rfl
      _ = t-2*s-2+1   := by rw [tsub_add_eq_add_tsub ht2]
      _ = t-2*(s+1)+1 := by exact rfl
      _ = t+1-2*(s+1) := by rw [tsub_add_eq_add_tsub hs])

      have help2: t + 1 - 2 * Nat.succ s = t - 2 * s - 1 :=
(      calc
      t + 1 - 2 * Nat.succ s = t + 1 - 2 * s - 2 := rfl
      _ = t - 2 * s + 1 - 2 := by rw [tsub_add_eq_add_tsub hs0]
      _ = t - 2 * s - 1    := rfl
)
      have help3: t - 2 * s - 1 + 2 = t + 1 - 2 * s :=
(      calc
      t - 2 * s - 1 + 2 = t - 2 * s + 2 - 1 := by rw [tsub_add_eq_add_tsub hs1]
      _  = t - 2 * s + 1     := rfl
      _  = t + 1 - 2 * s     := by rw [tsub_add_eq_add_tsub hs0]
)
      have H1_help: fib (t + 1 + 2 * Nat.succ s) = fib (t + 2 + 2 * s) + fib (t + 1 + 2 * s) :=
(      calc
      fib (t + 1 + 2 * Nat.succ s) = fib (t + 1 + 2 * (s + 1)) := by ring
      _ = fib (t + 1 + 2 * s + 2)                       := by ring_nf
      _ = fib (t + 1 + 2 * s) + fib (t + 1 + 2 * s+1)   := by rw [fib_add_two]
      _ = fib (t + 2 + 2 * s) + (fib (t + 1 + 2 * s)  ) := by ring_nf
)
      have H1:fib (t + 1 + 2 * Nat.succ s)               + fib (t + 1 - 2 * Nat.succ s)≡ 0 [MOD p] :=
(      calc
        fib (t + 1 + 2 * Nat.succ s)                   + fib (t + 1 - 2 * Nat.succ s) = fib (t + 2 + 2 * s) + fib (t + 1 + 2 * s)  + fib (t + 1 - 2 * Nat.succ s) := by rw [H1_help]
        _ = fib (t + 2 + 2 * s) + (fib (t + 1 + 2 * s) + fib (t + 1 - 2 * Nat.succ s)) := by ring
        _ ≡ fib (t - 2 * s)     + (fib (t + 1 + 2 * s) + fib (t + 1 - 2 * Nat.succ s)) [MOD p] := Nat.ModEq.add_right _ (h_ind hs0).2
        _ = fib (t + 1 + 2 * s) + fib (t + 1 - 2 * Nat.succ s) + fib (t - 2 * s)           := by ring_nf
        _ = fib (t + 1 + 2 * s) + fib (t + 1 - 2 * Nat.succ s) + fib (t - 2 * s + 1 - 1)   := rfl
        _ = fib (t + 1 + 2 * s) + fib (t + 1 - 2 * Nat.succ s) + fib (t - 2 * s - 1 + 1)   := by rw [(tsub_add_eq_add_tsub hs1).symm]
        _ = fib (t + 1 + 2 * s) + (fib (t + 1 - 2 * Nat.succ s) + fib (t - 2 * s - 1 + 1)) := by ring_nf
        _ = fib (t + 1 + 2 * s) + (fib (t - 2 * s - 1)  + fib (t - 2 * s - 1 + 1)) := by {rw [help2]}
        _ = fib (t + 1 + 2 * s) + fib (t - 2 * s - 1 + 2)                          := by rw [fib_add_two]
        _ = fib (t + 1 + 2 * s) + fib (t + 1 - 2 * s)                              := by rw [help3]
        _ ≡ 0 [MOD p] := (h_ind hs0).1
)    
    have H2: fib (t + 2 + 2 * Nat.succ s)≡ fib (t - 2 * Nat.succ s) [MOD p] :=
      have : fib (t+2+2*Nat.succ s) +fib (t-2*s-1) ≡ fib (t-2*Nat.succ s)+fib (t-2*s-1) [MOD p] :=
      (calc
      fib (t+2+2*Nat.succ s) +fib (t-2*s-1) = fib (t+2*Nat.succ s+2) +fib (t-2*s-1) := by ring_nf
      _ = fib (t+2*Nat.succ s)   +fib (t+2*Nat.succ s+1)+fib (t-2*s-1)              := by rw [fib_add_two]
      _ = fib (t+2*(s+1))    +(fib (t-2*s-1)+fib (t+2*Nat.succ s+1)) := by ring
      _ = fib (t+2+2* s)     +(fib (t-2*s-1)+fib (t+2*Nat.succ s+1))  := by ring_nf
      _ ≡ fib (t-2* s)       +(fib (t-2*s-1)     +fib (t+2*Nat.succ s+1)) [MOD p] := Nat.ModEq.add_right _ (h_ind hs0).2
      _ = fib (t-2* s)       +(fib (t+1-2*Nat.succ s)+fib (t+2*Nat.succ s+1)) := by rw [help1]
      _ = fib (t-2* s)       +(fib (t+1+2*Nat.succ s)+fib (t+1-2*Nat.succ s)) := by ring_nf
      _ ≡ fib (t-2* s)       + 0        [MOD p] := Nat.ModEq.add_left _ H1
      _ = fib (t-2* s+2-2)                   := rfl
      _ = fib (t-2*s-2+2)                    := by rw [tsub_add_eq_add_tsub ht2]
      _ = fib (t-2*s-2)    + fib (t-2*s-2+1) := by rw [fib_add_two]
      _ = fib (t-2*s-2)    + fib (t-2*s+1-2) := by rw [tsub_add_eq_add_tsub ht2]
      _ = fib (t-(2*s+2))  + fib (t-2*s-1)   := rfl
      _ = fib (t-2*(s+1))  + fib (t-2*s-1)   := by ring_nf
      _ = fib (t-2*Nat.succ s) + fib (t-2*s-1)   := by ring)
      (calc
      fib (t + 2 + 2 * Nat.succ s) ≡ fib (t - 2 * Nat.succ s) [MOD p]
      := Nat.ModEq.add_right_cancel' (fib (t - 2 * s - 1)) this)
  And.intro H1 H2
  )
