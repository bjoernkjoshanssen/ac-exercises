import Mathlib.Data.Nat.Basic
import Mathlib.Data.Vector.Basic
import Mathlib.Data.Fintype.Vector

-- Solution to Exercise 2.2.

def squarefree {k:ℕ} (w: Vector (Fin 2) k) : Prop :=
∀ l:ℕ, l < w.length → ∀ v : Vector (Fin 2) l,
v.1 ≠ List.nil → ¬ List.IsInfix (v.1 ++ v.1) w.1

instance (w : Vector (Fin 2) 4) : Decidable (squarefree w)
:=
decidable_of_iff (∀ l:ℕ, l < w.length → ∀ v : Vector (Fin 2) l,
v.1 ≠ List.nil → ¬ List.IsInfix (v.1 ++ v.1) w.1
) (by rw [squarefree])

example : ∀ w : Vector (Fin 2) 4,
¬ squarefree w := by decide
