import ring_theory.int.basic

example (a₁ a₂ b₁ b₂ : ℕ) (h₁ : a₁ ≥ b₁) (h₂ : a₂ ≥ b₂) (h : a₁+a₂ = b₁+b₂) :
a₁ = b₁ := by {
  have g : a₁ = b₁ ∨ a₁ > b₁, from eq_or_gt_of_le h₁,
  cases g,
  exact g,
  have gg: a₁ + a₂ > b₁ + b₂, from add_lt_add_of_lt_of_le g h₂,
  have : b₁ + b₂ > b₁ + b₂, by {rwa h at gg,},
  exfalso,
  exact (lt_self_iff_false (b₁+b₂)).mp this,
}
