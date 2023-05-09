import computability.DFA --computability.NA
open_locale classical

def collatz_function (n : ℕ) : ℕ :=
  if n % 2 = 0 then n / 2 else 3 * n + 1

def hailstone (init:ℕ): ℕ →  ℕ :=
λ pow, nat.rec_on pow init (
  λ thepow theval, collatz_function theval
)

def steps_required (bound:ℕ) (init:ℕ) : ℤ := -- https://oeis.org/A006577
dite (∃ k, k<bound ∧ hailstone init k = 1) (
  λ h, ((nat.find h ):ℤ)
) (
  λ h, -1
)

def steps_required_sequence (bound len:ℕ) : list ℤ :=
nat.rec_on len list.nil (λ n seq_ind, seq_ind ++ [steps_required bound n])

#eval steps_required_sequence 1000 14
