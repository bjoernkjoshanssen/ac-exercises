import Mathlib.Data.Vector.Basic
import Mathlib.Data.Fintype.Vector

-- Solution to Exercise 2.2.

def squarefree {k:ℕ} (w: Mathlib.Vector (Fin 2) k) : Prop :=
∀ l:ℕ, l < w.length → ∀ v : Mathlib.Vector (Fin 2) l,
v.1 ≠ List.nil → ¬ List.IsInfix (v.1 ++ v.1) w.1

instance (w : Mathlib.Vector (Fin 2) 4) : Decidable (squarefree w)
:= w.length.decidableBallLT fun n _ ↦
      ∀ (v : Mathlib.Vector (Fin 2) n), v.1 ≠ [] → ¬v.1 ++ v.1 <:+: w.1

example : ∀ w : Mathlib.Vector (Fin 2) 4,
¬ squarefree w := by decide
