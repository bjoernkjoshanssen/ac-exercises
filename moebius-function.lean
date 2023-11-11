import Mathlib.NumberTheory.ArithmeticFunction

def μ : ℕ → ℤ := Nat.ArithmeticFunction.moebius

theorem moebius_values :
  [μ 0,μ 1,μ 2,μ 3,μ 4,μ 5,μ 6,μ 7,μ 8,μ 9,μ 10,μ 11,μ 12,μ 13,μ 14, μ 15, μ 16]
= [  0,  1, -1, -1,  0, -1,  1, -1,  0,  0,   1,  -1,   0,  -1,   1,    1,    0]
  :=
  of_eq_true (eq_true_of_decide (Eq.refl true))
