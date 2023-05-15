def fibo (p l : ℕ) : (list ℕ) × (ℕ×ℕ):= -- a list, and its last two elements
  ite (p ≤ 1) ([0],0,0)
  $ nat.rec_on l
    ([1,0], 1, 0) -- Start of Fibonacci sequence, backwards
    (λ k, λ fib_ind,
      ite (fib_ind.2.1 = 1 ∧ (fib_ind.2.2 + 1) % p = 0) fib_ind
      (
        ((fib_ind.2.1 + fib_ind.2.2) % p) :: fib_ind.1,
        (fib_ind.2.1 + fib_ind.2.2) % p,
        fib_ind.2.1
      )
    )

def pisano (p : ℕ) : list ℕ := (fibo p (p*p-1)).1.reverse

#eval pisano 1
#eval pisano 2
#eval pisano 3
#eval pisano 4
#eval pisano 5
