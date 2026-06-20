import Mathlib.Data.Vector.Basic

-- Solution to Exercise 7.1.

example (a₁ a₂ b₁ b₂ : Nat) (h₁ : a₁ ≥ b₁) (h₂ : a₂ ≥ b₂) (h : a₁+a₂ = b₁+b₂) :
a₁ = b₁ := by {
  have g : a₁ = b₁ ∨ b₁ < a₁ := by omega
  rcases g with p1 | p2
  exact p1
  exfalso
  have gg: a₁ + a₂ > b₁ + b₂ := by {
    calc b₁ + b₂ < a₁ + b₂ := Nat.add_lt_add_right p2 b₂
    _            ≤ a₁ + a₂ := Nat.add_le_add_left h₂ a₁
  }
  have : b₁ + b₂ > b₁ + b₂ := by {rw [h] at gg;exact gg}
  exact (lt_self_iff_false (b₁+b₂)).mp this
}
