import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Ring

-- Solution to Exercise 6.1.

lemma max_left {a b b' c c' : ℕ} (h: a ≤ b * c):
    a ≤ (max b b') * max c c' := calc
    a ≤ b * c:= h
  _ ≤ (max b b') * c       := Nat.mul_le_mul_right _ (le_max_left _ _)
  _ ≤ (max b b') * max c c':= Nat.mul_le_mul_left  _ (le_max_left _ _)

lemma max_right {a' b b' c c' : ℕ} (h: a' ≤ b' * c'):
    a' ≤ (max b b') * max c c' := calc
    a' ≤ b' * c':= h
   _ ≤ (max b b') * c'        := Nat.mul_le_mul_right _ (le_max_right _ _)
   _ ≤ (max b b') * (max c c'):= Nat.mul_le_mul_left  _ (le_max_right _ _)

theorem max_ineq (a a' b b' c c' : ℕ) (h: a ≤ b * c) (h' : a' ≤ b' * c'):
max a a' ≤ (max b b') * max c c' :=
max_le (max_left h) (max_right h')

theorem mul_ineq (a a' b b' c c' : ℕ) (h: a ≤ b * c) (h' : a' ≤ b' * c'):
  a * a' ≤ (b * b') * (c * c') := calc -- In Lean 4, the _ must be right below
         a * a' ≤ (b*c) * a'     := Nat.mul_le_mul_right a' h
         _ ≤ (b*c) * (b' * c')   := Nat.mul_le_mul_left _ h'
         _ = (b * b') * (c * c') := by ring

theorem add_ineq (a a' b b' c c' : ℕ) (h: a ≤ b + c) (h' : a' ≤ b' + c'):
  a + a' ≤ (b + b') + (c + c') := calc
  a + a' ≤ (b+c) + a'        := Nat.add_le_add_right h  _
  _      ≤ (b+c) + (b' + c')   := Nat.add_le_add_left  h' _
  _      = (b + b') + (c + c') := by ring
