import Mathlib.Data.Nat.Basic
import Mathlib.Data.Vector.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Vector
import Mathlib.Data.Fintype.BigOperators

def blocks {n:ℕ}(b k:ℕ) (x : Vector (Fin b) n): ℕ :=
  Fintype.card {y : Vector (Fin b) k // ∃ i : Fin n,  y.1 = ((x.1++x.1).drop i).take k}

def complexity_function {n:ℕ}(b:ℕ) (x : Vector (Fin b) n) : List ℕ
:= List.ofFn (λ k:Fin n.succ ↦ blocks b k x)

-- #eval complexity_function 2 ⟨[0,1,1,0,1,0,0,1,1,0,0,1,0,1,1,0],rfl⟩

-- #eval complexity_function 2 ⟨[0,1,1,0,1,0,0,1],rfl⟩

-- example : complexity_function 2 ⟨[0,1,1,0,1,0,0,1],rfl⟩ = [1, 2, 4, 6, 8, 8, 8, 8, 8] :=
-- dec_trivial

-- example : complexity_function 2 ⟨[0,1,1,0,1,0,0,1,1,0,0,1,0,1,1,0],rfl⟩
-- = [1, 2, 4, 6, 10, 12, 14, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16]
-- := dec_trivial

theorem Fintype_card_Fin {n:ℕ} : Fintype.card (Fin n) = n:=  Finset.card_fin n

theorem card_Vector_Fin (b n:ℕ) : Fintype.card (Vector (Fin b) n) = b ^ n :=
            calc _ = Fintype.card (Fin b) ^ n := card_vector n
            _ = b                    ^ n := by rw [Fintype_card_Fin]

theorem bound {n:ℕ}(b:ℕ) (x : Vector (Fin b.succ) n):
∀ k:Fin n, blocks b.succ k.1 x ≤ b.succ ^ k.1 :=
λ k ↦
calc
_ ≤ Fintype.card (Vector (Fin b.succ) k.1) := Fintype.card_le_of_injective
  (λ y: {y : Vector (Fin b.succ) k.1 //  ∃ i : Fin n,  y.1 = ((x.1++x.1).drop i).take k.1} ↦ y.1)
  (λ u v huv ↦ Subtype.eq huv)
_ = Fintype.card (Fin b.succ) ^ k.1     := card_vector k.1
_ = b.succ                    ^ k.1     := by rw [Fintype_card_Fin]
