import Acmoi.Cursive

structure KnapsackInstance (c: ℕ) where
  target : ℕ
  wt : PF c -- weight

def Knapsack : DecisionProblem where
  Instance := Σ c : ℕ, KnapsackInstance c
  Space := fun ⟨c,_⟩ ↦ (Fin (c) → ℕ)
  Solution := fun i p ↦ (i.snd.target = Matrix.dotProduct p i.snd.wt.val)

def KnapsackSolution (i : Knapsack.Instance):= Solution_of i

def Knapsack2 : DecisionProblem where
  Instance := KnapsackInstance 2
  Space := λ _ ↦ (Fin 2 → ℕ) -- given that the # of items is 2, the space doesn't depend on the instance
  Solution := λ i p ↦ (i.target = Matrix.dotProduct i.wt.val p)

def Knapsack2Solution (i : Knapsack2.Instance):= Solution_of i
-- make everything work with this version
