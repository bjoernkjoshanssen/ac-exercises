import data.vector
import number_theory.arithmetic_function

def Lookback (m k t : ℕ) {n:ℕ} (x: vector (fin 2) n) : Prop :=
  ∀ u:ℕ, u < t → x.1.nth (m+u) = x.1.nth (m+u-k) 

example :
∀ x₀ x₁ x₂ x₃ : fin 2,
Lookback 2 1 1 ⟨[x₀,x₁,x₁,x₂,x₃],rfl⟩ :=
λ x₀ x₁ x₂ x₃, 
  λ u hut, by {
    have h0: u=0, from nat.eq_zero_of_le_zero (nat.le_of_lt_succ hut),
    simp,rw h0,norm_num,
  }

example :
∀ x₀ x₁ x₂ x₃ x₄ : fin 2,
Lookback 2 1 1 ⟨[x₀, x₁,x₂,x₃,x₄],rfl⟩ → some x₂ = some x₁ :=
λ x₀ x₁ x₂ x₃ x₄ h, 
  have h1: [x₀,x₁,x₂,x₃,x₄].nth (2+0)
         = [x₀,x₁,x₂,x₃,x₄].nth (2+0-1),
    from h 0 zero_lt_one,
  have h2: [x₀, x₁, x₂, x₃, x₄].nth 2
         = [x₀, x₁, x₂, x₃, x₄].nth 1,
    from h1,
  calc some x₂ = [x₀,x₁, x₂, x₃, x₄].nth (2): rfl
  ... = [x₀, x₁, x₂, x₃, x₄].nth (1): h2
  ... = some x₁: rfl
