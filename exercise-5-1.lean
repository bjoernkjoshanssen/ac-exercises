import Mathlib.Data.Nat.Basic
import Mathlib.Data.Vector.Basic

-- Solution to Exercise 5.1.

def Lookback (m k t : ℕ) {n:ℕ} (x: Vector (Fin 2) n) : Prop :=
  ∀ u:ℕ, u < t → x.1.getI (m+u) = x.1.getI (m+u-k) 

example :
∀ x₀ x₁ x₂ x₃ : Fin 2,
Lookback 2 1 1 ⟨[x₀,x₁,x₁,x₂,x₃],rfl⟩ :=
λ x₀ x₁ x₂ x₃ ↦ 
  λ u hut ↦ by {
    have h0: u=0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hut)
    simp
    rw [h0]
    rfl
  }

example :
∀ x₀ x₁ x₂ x₃ x₄ : Fin 2,
Lookback 2 1 1 ⟨[x₀, x₁,x₂,x₃,x₄],rfl⟩ → some x₂ = some x₁ :=
λ x₀ x₁ x₂ x₃ x₄ h ↦
  have h1: [x₀,x₁,x₂,x₃,x₄].getI (2+0)
         = [x₀,x₁,x₂,x₃,x₄].getI (2+0-1) := h 0 zero_lt_one
  have h2: [x₀, x₁, x₂, x₃, x₄].getI 2
         = [x₀, x₁, x₂, x₃, x₄].getI 1 := h1
  calc some x₂ = [x₀,x₁, x₂, x₃, x₄].getI (2) := rfl
  _ = [x₀, x₁, x₂, x₃, x₄].getI (1) := congr_arg _ h2
  _ = some x₁ := rfl
