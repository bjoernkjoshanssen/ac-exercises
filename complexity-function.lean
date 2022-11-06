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

theorem fintype_card_fin {n:ℕ} : fintype.card (fin n) = n:=  finset.card_fin n

theorem card_vector_fin (b n:ℕ) : fintype.card (vector (fin b) n) = b ^ n :=
            calc _ = fintype.card (fin b) ^ n: card_vector n
               ... = b                    ^ n: by rw fintype_card_fin

theorem bound {n:ℕ}(b:ℕ) (x : vector (fin b.succ) n):
∀ k:fin n, blocks b.succ k.1 x ≤ b.succ ^ k.1 :=
λ k, calc _ ≤ fintype.card (vector (fin b.succ) k.1): fintype.card_le_of_injective (λ y: {y : vector (fin b.succ) k.1 //  ∃ i : fin n,  y.1 = ((x.1++x.1).drop i).take k.1},
y.1) (λ u v huv, subtype.eq huv)
        ... = fintype.card (fin b.succ) ^ k.1     : card_vector k.1
        ... = b.succ                    ^ k.1     : by rw fintype_card_fin
