import data.vector data.nat.basic data.pnat.prime data.list.of_fn

def blocks {n:ℕ}(b k:ℕ) (x : vector (fin b) n): ℕ :=
  fintype.card {y : vector (fin b) k // 
  ∃ i : fin n,  y.1 = ((x.1++x.1).drop i).take k}

def complexity_function {n:ℕ}(b:ℕ) (x : vector (fin b) n)
--: vector ℕ x.length.succ
: list ℕ
:= list.of_fn (λ k:fin n.succ, blocks b k x)

#eval complexity_function 2 ⟨[0,1,1,0,1,0,0,1,1,0,0,1,0,1,1,0],rfl⟩

#eval complexity_function 2 ⟨[0,1,1,0,1,0,0,1],rfl⟩

example : complexity_function 2 ⟨[0,1,1,0,1,0,0,1],rfl⟩ = [1, 2, 4, 6, 8, 8, 8, 8, 8] :=
dec_trivial

-- example : complexity_function 2 ⟨[0,1,1,0,1,0,0,1,1,0,0,1,0,1,1,0],rfl⟩
-- = [1, 2, 4, 6, 10, 12, 14, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16]
-- := dec_trivial
