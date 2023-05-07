def collatz (n : ℕ) : ℕ :=
  if n % 2 = 0 then n / 2 else 3 * n + 1

example :
  (0, collatz 0) = (0, 0) := dec_trivial

example :
  (1, collatz 1, collatz (collatz 1), collatz (collatz (collatz 1)))
  = (1, 4, 2, 1)
  := dec_trivial

example :
  (2, collatz 2, collatz (collatz 2), collatz (collatz (collatz 2)))
  = (2, 1, 4, 2)
  := dec_trivial

example :
  (
    3,
    collatz 3,
    collatz (collatz 3),
    collatz (collatz (collatz 3)),
    collatz (collatz (collatz (collatz 3))),
    collatz (collatz (collatz (collatz (collatz 3)))),
    collatz (collatz (collatz (collatz (collatz (collatz 3))))),
    collatz (collatz (collatz (collatz (collatz (collatz (collatz 3)))))
)
  )
  = (3, 10, 5, 16, 8, 4, 2, 1)
  := dec_trivial

def collatz_pow (init:ℕ): ℕ →  ℕ :=
λ pow, nat.rec_on pow init (
  λ thepow theval, collatz theval
)

example :
  (
    collatz_pow 3 0,
    collatz_pow 3 1,
    collatz_pow 3 2,
    collatz_pow 3 3,
    collatz_pow 3 4,
    collatz_pow 3 5,
    collatz_pow 3 6,
    collatz_pow 3 7
)
  = (3, 10, 5, 16, 8, 4, 2, 1)
  := dec_trivial

example: collatz_pow 3 0 ≠ 1 := dec_trivial
example: collatz_pow 3 1 ≠ 1 := dec_trivial
example: collatz_pow 3 2 ≠ 1 := dec_trivial
example: collatz_pow 3 3 ≠ 1 := dec_trivial
example: collatz_pow 3 4 ≠ 1 := dec_trivial
example: collatz_pow 3 5 ≠ 1 := dec_trivial
example: collatz_pow 3 6 ≠ 1 := dec_trivial
example: collatz_pow 3 7 = 1 := dec_trivial


