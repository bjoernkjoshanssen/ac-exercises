import Mathlib.Computability.DFA

-- Solution to Exercise 4.1.

def collatz_function (n : ℕ) : ℕ :=
  if n % 2 = 0 then n / 2 else 3 * n + 1

def hailstone (init:ℕ): ℕ →  ℕ :=
λ pow ↦ Nat.recOn pow init (
  λ _ theval ↦ collatz_function theval
)

def steps_required (bound:ℕ) (init:ℕ) : ℤ := -- https://oeis.org/A006577
dite (∃ k, k<bound ∧ hailstone init k = 1) (
  λ h ↦ ((Nat.find h ):ℤ)
) (
  λ _ ↦ -1
)

def steps_required_sequence (bound len:ℕ) : List ℤ :=
Nat.recOn len List.nil (λ n seq_ind ↦ seq_ind ++ [steps_required bound n])

#eval steps_required_sequence 1000 14
