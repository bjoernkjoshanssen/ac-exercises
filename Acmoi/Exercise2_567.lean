import Mathlib.Tactic.Ring

-- Solutions to Exercises 2.5, 2.6, and 2.7.

/- We prove that generalized almost square-free-ness is the same as (abstract)
almost squarefreeness for binary words.

000 is almost square-free but not overlapfree.
-/

def occurs_in {α:Type} (y w : List α)
  :=
  ∃ x z : List α, w = x ++ y ++ z


def nonnil_occurs_squared_in {α:Type} (y w : List α) : Prop :=
  (y ≠ List.nil) ∧
  occurs_in (y ++ y) w

/-- This is only interesting if a ≠ b so maybe that should be baked in. -/
def abstract_almost_square_free
  (a b : Fin 2) (_ : a ≠ b)
  (w : List (Fin 2))
  : Prop :=
  ∀ y : List (Fin 2), nonnil_occurs_squared_in y w
                    → y = [a] ∨ y = [b] ∨ y = [a,b]

def almost_square_free (w : List (Fin 2)): Prop :=
  abstract_almost_square_free 0 1 Fin.zero_ne_one w

def generalized_almost_square_free {α:Type} (w : List α) : Prop :=
  (∀ a b : α, ¬ (nonnil_occurs_squared_in [a,b] w ∧ nonnil_occurs_squared_in [b,a] w))
  ∧
  ∀ y : List α, nonnil_occurs_squared_in y w →  (∃ a : α, y = [a]) ∨ ∃ a b :α, y= [a,b]

theorem cons_ne_nil' {a : Fin 2}
{b : Fin 2} {c : Fin 2} : [a,b] ≠ [c] :=
  λ h ↦ List.cons_ne_nil b List.nil (List.tail_eq_of_cons_eq h)

theorem eq_cons_ne_nil {a b c d : Fin 2}
  (hcd: [c,d] = [a] ∨ [c,d] = [b] ∨ [c,d] = [a,b])
  (hdc: [d,c] = [a] ∨ [d,c] = [b] ∨ [d,c] = [a,b]): a=b :=
  by {
    rcases hcd with u | v
    rcases hdc
    exfalso
    exact cons_ne_nil' u
    exfalso
    exact cons_ne_nil' u
    rcases v with u | v
    rcases hdc
    exfalso
    have : 2 = 1 := congr_arg List.length u
    have : 1 = 0 := Nat.succ_injective this
    exact zero_ne_one this.symm
    exfalso
    have : 2 = 1 := congr_arg List.length u
    have : 1 = 0 := Nat.succ_injective this
    exact zero_ne_one this.symm
    rcases hdc with hx | hy
    exfalso
    have : 2 = 1 := congr_arg List.length hx
    have : 1 = 0 := Nat.succ_injective this
    exact zero_ne_one this.symm
    rcases hy with hj | hk
    exfalso
    have : 2 = 1 := congr_arg List.length hj
    have : 1 = 0 := Nat.succ_injective this
    exact zero_ne_one this.symm

    exact
    calc a = d := (List.head_eq_of_cons_eq hk).symm
    _ = b :=  List.head_eq_of_cons_eq (List.tail_eq_of_cons_eq v)
  }

theorem generalized (w : List (Fin 2)) (a b : Fin 2)
  (hab : a ≠ b)
  (hsqf: abstract_almost_square_free a b hab w) :
  generalized_almost_square_free w := by {
    constructor

    intros c d hcontra
    rcases hcontra with ⟨hcontra_left, hcontra_right⟩
    exact hab (eq_cons_ne_nil (hsqf _ hcontra_left) (hsqf _ hcontra_right))

    intros y hy
    have hin: y = [a] ∨ (y = [b] ∨ y = [a,b]) := hsqf _ hy

    rcases hin with  hb | ha -- !!
    left
    exists a
    cases ha
    left
    exists b
    right
    exists a
    exists b
  }

def not_overlapfree (w : List (Fin 2)) : Prop :=
∃ y : List (Fin 2), ∃ a : Fin 2, occurs_in ((a :: y) ++ (a ::y) ++ [a]) w

def overlapfree (w : List (Fin 2)) : Prop :=
¬ not_overlapfree w

def ctrex := ([0,0,0]: List (Fin 2))

theorem cons_append_length {a b : Fin 2} {x u z : List (Fin 2)} :
  (x       ++ ((a :: (b :: u))   ++ (a :: (b :: u)))   ++ z).length =
  x.length +  u.length.succ.succ +  u.length.succ.succ +  z.length :=
  by {
    rw [List.append_assoc]
    rw [List.append_assoc]
    rw [List.length_append]
    rw [List.length_append]
    rw [List.length_append]
    rw [add_assoc]
    rw [add_assoc]
    rw [List.length_cons]
    rw [List.length_cons]
  }

theorem square_length_ge_four {x z u: List (Fin 2)} {a b : Fin 2}:
  (x ++ ((a :: (b :: u)) ++ (a::(b::u))) ++ z).length ≥ 4 :=
  let n := u.length.succ.succ
  calc
  _ = x.length + n + n + z.length := cons_append_length
  _ ≥ x.length + n + n            := Nat.le_add_right (List.length x + n + n) (List.length z)
  _ = x.length + (n + n)          := add_assoc _ _ _
  _ ≥            n + n            := Nat.le_add_left _ _
  _ = u.length.succ.succ + u.length.succ.succ := rfl
  _ = (u.length.succ + 1) + (u.length.succ + 1) := by repeat{rw[Nat.succ_eq_add_one]}
  _ = (u.length + 2) + (u.length + 2) := by repeat{rw[Nat.succ_eq_add_one]}
  _ =            2*u.length + 4   := by ring
  _ ≥ _                           := le_add_self

theorem ctrex_ne {x z : List (Fin 2)} {a b : Fin 2}:
  ctrex ≠ (x ++ ([a,b] ++ [a,b]) ++ z) :=
  λh ↦ have : ctrex.length ≥ 4 :=
  (calc _ = (x ++ ([a,b] ++ [a,b]) ++ z).length := by rw [h]
  _ ≥ 4 := square_length_ge_four)
  Nat.not_succ_le_self 3 this

example: generalized_almost_square_free ctrex := by {
  constructor
  intros a b hcontra
  rcases hcontra with ⟨hcontra_left, _⟩
  rcases hcontra_left with ⟨_, h⟩
  rcases h with ⟨x, hx⟩
  rcases hx with ⟨z, hz⟩
  exact ctrex_ne hz
  intros y hy
  rcases y with yy | ⟨a, y_tl⟩
  exfalso
  exact hy.1 rfl
  unfold nonnil_occurs_squared_in at hy
  left
  exists a


  rcases y_tl with _ | ⟨b , u⟩
  rfl
  exfalso
  rcases hy with ⟨_, hy2⟩
  rcases hy2 with ⟨x, hx⟩
  rcases hx with ⟨z, hz⟩
  have : 3 ≥ 4 := (calc
    3 = ctrex.length := rfl
  _ = (x ++ (a :: b :: u ++ a :: b :: u) ++ z).length := by rw [hz]
  _ ≥ 4                                               := square_length_ge_four)
  exact Nat.not_succ_le_self 3 this
}

example: not_overlapfree ctrex := by {
  exists List.nil
  exists (0:Fin 2)
  exists List.nil
  exists List.nil
}

example: ¬ almost_square_free ([0,1,1,0,1,1] : List (Fin 2)) := by {
  let ex := ([0,1,1] : List (Fin 2))
  let target := ([0,1,1,0,1,1] : List (Fin 2))
  intro hcontra
  let h := hcontra ex
  have h1 : nonnil_occurs_squared_in ex target := by {
    constructor
    intro hex
    have h2 : 3 = 0 := congr_arg List.length hex
    exact Nat.succ_ne_zero 2 h2
    exists List.nil
    exists List.nil
  }
  have h2 : ex ∈ ({[0], [1], [0,1]} : Set (List (Fin 2))) := h h1
  rcases h2 with h2 | H2
  have h3: 3 = 1 := congr_arg List.length h2
  exact Nat.succ_ne_zero 1 (Nat.succ_injective h3)
  rcases H2 with HH2 | GG2
  have h3: 3 = 1 := congr_arg List.length HH2
  exact Nat.succ_ne_zero 1 (Nat.succ_injective h3)
  have h2': ex = ([0,1]:List (Fin 2)) := GG2

  have h3: 3 = 2 := (calc
  3 = ex.length := rfl
  _ = ([0,1]:List (Fin 2)).length := by rw [h2']
  _ = 2 := rfl)
  exact Nat.succ_ne_zero 0 (Nat.succ_injective (Nat.succ_injective h3))
}
