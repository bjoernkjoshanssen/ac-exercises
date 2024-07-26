import Mathlib.Tactic
import Mathlib.Data.Vector.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic

-- Solution to Exercise 1.5.

theorem decide_diophantine2_1 {a b n x y : ℕ} (h : a*x+b*y =n)
  (ha : 0 < a) : x < n/a + 1 := by
  have hh: x*a ≤ n := calc
       _ = a*x + 0     := by ring
       _ ≤ a*x + (b*y) := add_le_add_left (Nat.zero_le  _) (a*x)
       _ = _           := h
  calc _ ≤ n/a         := (Nat.le_div_iff_mul_le ha).mpr hh
     _ < _             := lt_add_one (n/a)

theorem decide_diophantine2_2 {a b n x y : ℕ}
  (g1 : a*x+b*y =n) (ha : 0 < a) (hb : 0 < b) : x < n/a + 1 ∧ y < n/b + 1 := by
  have g2:b*y+a*x =n := by linarith
  constructor
  · exact decide_diophantine2_1 g1 ha
  · exact decide_diophantine2_1 g2 hb

instance example_1_59 :
  Decidable (∀ x y : ℕ, 2*x+3*y=7 ∧ (x>0→ y>0) ↔ x=2∧  y=1) :=
  decidable_of_iff
  (∀ x : Fin (7/2+1), ∀ y: Fin (7/3+1), 2*x.1+3*y.1=7 ∧ (x.1>0→ y.1>0) ↔ x.1=2∧  y.1=1)
  (
    Iff.intro (
      λ h x y ↦ Iff.intro (
        λ h1 ↦
        have H: 2 * x + 3 * y = 7 ∧ (x > 0 → y > 0) ↔ x = 2 ∧ y = 1 :=
          h ⟨ x,
            (decide_diophantine2_2 h1.1 (two_pos) three_pos).1
          ⟩ ⟨y,
            (decide_diophantine2_2 h1.1 (two_pos) three_pos).2
          ⟩
        H.mp h1
      )
      (
        λ hxy ↦ And.intro (
          calc 2 * x + 3 * y = 2 * x + 3 * 1:= by rw [hxy.2]
                         _ = 2 * 2 + 3 * 1  := by rw [hxy.1]
                         _ = 7              := by decide
        ) (
          λ _ ↦ calc y = 1:= hxy.2
                   _ > 0  := one_pos
        )
      )
    ) (
      λ h ↦ λ x y ↦ h x.val y.val
    )
  )

example : (∀ x y : ℕ, 2*x+3*y=7 ∧ (x>0→ y>0) ↔ x=2∧  y=1) := by decide
