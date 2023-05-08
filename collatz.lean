import computability.DFA --computability.NA
open_locale classical

def collatz (n : ℕ) : ℕ :=
  if n % 2 = 0 then n / 2 else 3 * n + 1

def collatz_pow (init:ℕ): ℕ →  ℕ :=
λ pow, nat.rec_on pow init (
  λ thepow theval, collatz theval
)

def collatz_iter (bound:ℕ) (init:ℕ) : ℤ := -- https://oeis.org/A006577
dite (∃ k, k<bound ∧ collatz_pow init k = 1) (
  λ h, ((nat.find h ):ℤ)
) (
  λ h, -1
)

def collatz_iter_sequence (bound len:ℕ) : list ℤ :=
nat.rec_on len list.nil (λ n seq_ind, seq_ind ++ [collatz_iter bound n])

#eval collatz_iter_sequence 1000 14
