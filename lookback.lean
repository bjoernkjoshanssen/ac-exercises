import data.vector
import number_theory.arithmetic_function

def Lookback (m k t : ℕ) {n:ℕ} (x: vector (fin 2) n) : Prop :=
  ∀ u:ℕ, u < t → x.1.nth (m+1+u) = x.1.nth (m+1+u-k) 

example :
∀ x₁ x₂ x₃ x₄ : fin 2,
Lookback 1 1 1 ⟨[x₁,x₂,x₂,x₃,x₄],rfl⟩ :=
λ x₁ x₂ x₃ x₄, 
  λ u hut, by {
    have h0: u=0, from nat.eq_zero_of_le_zero (nat.le_of_lt_succ hut),
    simp,rw h0,norm_num,
  }

example :
∀ x₁ x₂ x₃ x₄ x₅ : fin 2,
Lookback 1 1 1 ⟨[x₁,x₂,x₃,x₄,x₅],rfl⟩ → some x₃ = some x₂ :=
λ x₁ x₂ x₃ x₄ x₅ h, 
  have h1: [x₁,x₂,x₃,x₄,x₅].nth (1+1+0) = [x₁,x₂,x₃,x₄,x₅].nth (1+1+0-1),
    from h 0 zero_lt_one,
  have h2: [x₁, x₂, x₃, x₄, x₅].nth (2) = [x₁, x₂, x₃, x₄, x₅].nth (1),
    from h1,
  calc some x₃ = [x₁, x₂, x₃, x₄, x₅].nth (2): rfl
  ... = [x₁, x₂, x₃, x₄, x₅].nth (1): h2
  ... = some x₂: rfl
