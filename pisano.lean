import Mathlib.Data.Nat.Basic

def fibo (p l : ℕ) : (List ℕ) × (ℕ×ℕ):= -- a List, and its last two elements
  ite (p ≤ 1) ([0],0,0)
  $ Nat.recOn l
    ([1,0], 1, 0) -- Start of Fibonacci sequence, backwards
    (λ _ fib_ind ↦
      ite (fib_ind.2.1 = 1 ∧ (fib_ind.2.2 + 1) % p = 0) fib_ind
      (
        ((fib_ind.2.1 + fib_ind.2.2) % p) :: fib_ind.1,
        (fib_ind.2.1 + fib_ind.2.2) % p,
        fib_ind.2.1
      )
    )

def pisano (p : ℕ) : List ℕ := (fibo p (p*p-1)).1.reverse

#eval pisano 1
#eval pisano 2
#eval pisano 3
#eval pisano 4
#eval pisano 5
