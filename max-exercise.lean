import tactic.basic
import tactic.ring

lemma max_left {a b b' c c' : ℕ} (h: a ≤ b * c):
    a ≤ (max b b') * max c c' := calc
    a ≤ b * c: h
  ... ≤ (max b b') * c       : nat.mul_le_mul_right _ (le_max_left _ _)
  ... ≤ (max b b') * max c c': nat.mul_le_mul_left  _ (le_max_left _ _)

lemma max_right {a' b b' c c' : ℕ} (h: a' ≤ b' * c'):
    a' ≤ (max b b') * max c c' := calc
    a' ≤ b' * c': h
   ... ≤ (max b b') * c'        : nat.mul_le_mul_right _ (le_max_right _ _)
   ... ≤ (max b b') * (max c c'): nat.mul_le_mul_left  _ (le_max_right _ _)

theorem max_ineq (a a' b b' c c' : ℕ) (h: a ≤ b * c) (h' : a' ≤ b' * c'):
max a a' ≤ (max b b') * max c c' :=
max_le (max_left h) (max_right h')

theorem mul_ineq (a a' b b' c c' : ℕ) (h: a ≤ b * c) (h' : a' ≤ b' * c'):
  a * a' ≤ (b * b') * (c * c') :=

  calc a * a' ≤ (b*c) * a'          : nat.mul_le_mul_right _ h
          ... ≤ (b*c) * (b' * c')   : nat.mul_le_mul_left _ h'
          ... = (b * b') * (c * c') : by ring

theorem add_ineq (a a' b b' c c' : ℕ) (h: a ≤ b + c) (h' : a' ≤ b' + c'):
  a + a' ≤ (b + b') + (c + c') :=

  calc a + a' ≤ (b+c) + a'          : nat.add_le_add_right h  _
          ... ≤ (b+c) + (b' + c')   : nat.add_le_add_left  h' _
          ... = (b + b') + (c + c') : by ring
