import data.vector
import number_theory.arithmetic_function

def Lookback (m k t n:ℕ) (x: vector (fin 2) n) : Prop :=
  ∀ u:ℕ, u < t → x.1.nth (m+1+u) = x.1.nth (m+1+u-k) 

example : Lookback 1 1 1 5 ⟨[0,1,1,0,1],rfl⟩ :=
  λ u hut, by {
    have h0: u=0, from nat.eq_zero_of_le_zero (nat.le_of_lt_succ hut),
    simp,rw h0,norm_num,
  }
