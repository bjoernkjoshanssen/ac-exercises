import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

open List

-- Solutions to Exercises 2.5, 2.6, and 2.7.

/- We prove that generalized almost square-free-ness is the same as (abstract)
almost squarefreeness for binary words.

000 is almost square-free but not overlapfree.
-/

def occurs_in {α:Type} (y w : List α)
  :=
  ∃ x z : List α, w = x ++ y ++ z


def nonnil_occurs_squared_in {α:Type} (y w : List α) : Prop :=
  (y ≠ nil) ∧
  occurs_in (y ++ y) w

def pre_abstract_almost_square_free
  (a b : Fin 2)
  (w : List (Fin 2))
  : Prop :=
  ∀ y : List (Fin 2), nonnil_occurs_squared_in y w
                    → y = [a] ∨ y = [b] ∨ y = [a,b]

def abstractAlmostSquareFree (w : List (Fin 2)) :=
  pre_abstract_almost_square_free 0 1 w ∨
  pre_abstract_almost_square_free 1 0 w

def almostSquareFree (w : List (Fin 2)): Prop :=
  pre_abstract_almost_square_free 0 1 w

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
  (∀ a b, ¬ (nonnil_occurs_squared_in [a,b] w ∧ nonnil_occurs_squared_in [b,a] w))
  ∧
  ∀ y, nonnil_occurs_squared_in y w → (∃ a, y = [a]) ∨ ∃ a b, y= [a,b]

theorem cons_ne_nil' {a : Fin 2}
{b : Fin 2} {c : Fin 2} : [a,b] ≠ [c] := by simp

theorem eq_cons_ne_nil {a b c d : Fin 2}
  (hcd: [c,d] = [a] ∨ [c,d] = [b] ∨ [c,d] = [a,b])
  (hdc: [d,c] = [a] ∨ [d,c] = [b] ∨ [d,c] = [a,b]): a=b := by
  cases hcd with
  | inl h => simp at h
  | inr h => cases h with
    | inl h => simp at h
    | inr h => cases hdc with
      | inl h => simp at h
      | inr h => cases h with
        | inl h₀ => simp at h₀
        | inr h₀ => simp only [cons.injEq, and_true] at *; exact Eq.trans h.1.symm h₀.2

theorem generalized (w : List (Fin 2)) (a b : Fin 2)
  (hab : a ≠ b)
  (hsqf: abstract_almost_square_free a b hab w) :
  generalized_almost_square_free w := by
    constructor
    intros c d hc
    exact hab (eq_cons_ne_nil (hsqf _ hc.1) (hsqf _ hc.2))
    intros y hy
    have hin: y = [a] ∨ (y = [b] ∨ y = [a,b]) := hsqf _ hy
    aesop

def overlapfree (w : List (Fin 2)) : Prop :=
∀ y : List (Fin 2), ∀ a : Fin 2, ¬ occurs_in ((a :: y) ++ (a ::y) ++ [a]) w



theorem cons_append_length {a b : Fin 2} {x u z : List (Fin 2)} :
  (x       ++ ((a :: (b :: u))   ++ (a :: (b :: u)))   ++ z).length =
  x.length +  u.length.succ.succ +  u.length.succ.succ +  z.length := by
    repeat rw [append_assoc]
    repeat rw [length_append]
    repeat simp [length_append, add_assoc, length_cons]

theorem square_length_ge_four {x z u: List (Fin 2)} {a b : Fin 2}:
  (x ++ ((a :: (b :: u)) ++ (a::(b::u))) ++ z).length ≥ 4 := by
  simp only [cons_append, append_assoc, length_append, length_cons, ge_iff_le]
  linarith

def ctrex := ([0,0,0]: List (Fin 2))

theorem ctrex_ne {x z : List (Fin 2)} {a b : Fin 2}:
  ctrex ≠ (x ++ ([a,b] ++ [a,b]) ++ z) := fun h => by
  have : ctrex.length ≥ 4 := h ▸ square_length_ge_four
  simp [ctrex] at this

example: generalized_almost_square_free ctrex := by
  constructor
  intros a b hc
  obtain ⟨x, hx⟩ := hc.1.2
  obtain ⟨z, hz⟩ := hx
  exact ctrex_ne hz
  intros y hy
  cases y with
  | nil => exfalso; exact hy.1 rfl
  | cons hd₀ tail =>
    unfold nonnil_occurs_squared_in at hy
    left
    exists hd₀
    cases tail with
    | nil => rfl
    | cons hd tl =>
      exfalso
      obtain ⟨x, hx⟩ := hy.2
      obtain ⟨z, hz⟩ := hx
      have : 3 ≥ 4 := (by
      show ctrex.length ≥ 4
      rw [hz]
      apply square_length_ge_four)
      simp at this

example: ¬ overlapfree ctrex := by
  unfold overlapfree
  push_neg
  exists nil, 0, nil, nil

example: ¬ almost_square_free ([0,1,1,0,1,1] : List (Fin 2)) := by
  let ex := ([0,1,1] : List (Fin 2))
  intro hc
  have h1 : nonnil_occurs_squared_in ex [0,1,1,0,1,1] := by
    constructor
    · intro h
      simp [ex] at h
    · exists nil, nil
  rcases hc ex h1 with h | h <;> simp [ex] at h
