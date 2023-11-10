import Std.Logic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LibrarySearch

def φ : Prop :=
  ∀ x : Fin 19, ∀ y : Fin 30, ∀ z : Fin 35,
  143 * x.1 + 91 * y.1 + 77 * z.1 = 2692 ↔ x.1 = 6 ∧ y.1 = 10 ∧ z.1 = 12

def ψ : Prop :=
  ∀ x y z : Nat, 143 * x + 91 * y + 77 * z = 2692 ↔ x = 6 ∧ y = 10 ∧ z = 12


instance myφ : Decidable (φ) := decidable_of_iff (∀ x : Fin 19, ∀ y : Fin 30, ∀ z : Fin 35,
    143 * x.1 + 91 * y.1 + 77 * z.1 = 2692 ↔ x.1 = 6 ∧ y.1 = 10 ∧ z.1 = 12) (by rw [φ])

theorem decide_diophantine3_1 (a b c n x y z : Nat):
a*x+b*y+c*z =n → 0 < a → x < n/a + 1
:=
λ h ↦ λ ha: 0 < a ↦
have hh: x*a ≤ n := calc x*a = a*x + 0     := by ring
                        _ ≤ a*x + (b*y+c*z) := add_le_add_left (Nat.zero_le  _) (a*x)
                        _ = a*x + b*y + c*z := by ring
                        _ = n               := h
  calc _ ≤ n/a           := (Nat.le_div_iff_mul_le ha).mpr hh
     _ < _             := lt_add_one (n/a)

theorem decide_diophantine3_3 (a b c n x y z : Nat):
a*x+b*y+c*z =n → 0 < a → 0 < b → 0 < c → x < n/a + 1 ∧ y < n/b + 1 ∧ z < n/c + 1
:=
λ g1 ↦ λ ha hb hc ↦
have g2:b*y+a*x+c*z =n := calc _ = a*x+b*y+c*z  := by ring
                                _ = _           := g1
have g3:c*z+a*x+b*y =n := calc _ = a*x+b*y+c*z  := by ring
                                _ = _           := g1
have h1: x < n/a + 1 := decide_diophantine3_1 a b c n x y z g1 ha
have h2: y < n/b + 1 := decide_diophantine3_1 b a c n y x z g2 hb
have h3: z < n/c + 1 := decide_diophantine3_1 c a b n z x y g3 hc
And.intro h1 (And.intro h2 h3)

-- #eval 2692/143 -- 18
-- #eval 2692/91  -- 29
-- #eval 2692/77  -- 34
instance remark_2_15 :
  Decidable ψ :=
  decidable_of_iff φ
  (
    Iff.intro (
      λ h x y z ↦ Iff.intro
      -- sorry
      (
        λ h1 ↦
        have H: 143 * x + 91 * y + 77 * z = 2692 ↔ x=6∧  y=10 ∧ z=12 :=
          h ⟨ x,
            (decide_diophantine3_3
              143 91 77 2692 x y z h1 (Nat.succ_pos 142) (Nat.succ_pos 90) (Nat.succ_pos 76)).1
          ⟩ ⟨y,
            (decide_diophantine3_3
              143 91 77 2692 x y z h1 (Nat.succ_pos 142) (Nat.succ_pos 90) (Nat.succ_pos 76)).2.1
          ⟩ ⟨z,
            (decide_diophantine3_3
              143 91 77 2692 x y z h1 (Nat.succ_pos 142) (Nat.succ_pos 90) (Nat.succ_pos 76)).2.2
          ⟩
        H.mp h1
      )
      (
        λ hxyz ↦ calc
        143 * x + 91 *  y + 77 * z = 143 * x + 91 *  y + 77 * 12  := by rw [hxyz.2.2]
        _ = 143 * x + 91 * 10 + 77 * 12 := by rw [hxyz.2.1]
        _ = 143 * 6 + 91 * 10 + 77 * 12 := by rw [hxyz.1]
        _ = 2692  := rfl
      )
    ) (
      λ h x y z ↦ h x.val y.val z.val
    )
  )

#eval (φ : Bool) -- tt
