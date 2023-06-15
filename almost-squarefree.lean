import tactic.derive_fintype

/- We prove that generalized almost square-free-ness is the same as (abstract)
almost squarefreeness for binary words. -/

def occurs_squared_in {α:Type} (y w : list α) :=
  ∃ x z : list α, w = x ++ y ++ y ++ z

def abstract_almost_square_free
  (a b : fin 2)(h: a ≠ b)
  (w : list (fin 2))
  : Prop :=
  ∀ y : list (fin 2), occurs_squared_in y w
                    → y ∈ ({ [a], [b], [a,b]}: set (list (fin 2)))

def almost_square_free (w : list (fin 2)): Prop :=
  abstract_almost_square_free 0 1 fin.zero_ne_one w

def generalized_almost_square_free {α:Type} (w : list α) : Prop :=
  (∀ a b : α, ¬ (occurs_squared_in [a,b] w ∧ occurs_squared_in [b,a] w))
  ∧
  ∀ y : list α, occurs_squared_in y w →  (∃ a : α, y = [a]) ∨ ∃ a b :α, y= [a,b]

lemma cons_ne_nil' {a b c :  (fin 2)} : [a,b] ≠ [c] :=
  λ h, list.cons_ne_nil b list.nil (list.tail_eq_of_cons_eq h)

lemma eq_cons_ne_nil {a b c d : fin 2}
  (hcd: [c,d] ∈ ({[a], [b], [a,b]}: set (list (fin 2))))
  (hdc: [d,c] ∈ ({[a], [b] ,[a,b]}: set (list (fin 2)))): a=b :=
  by {
    repeat {cases hcd, exfalso, exact cons_ne_nil' hcd},
    repeat {cases hdc, exfalso, exact cons_ne_nil' hdc},
    exact calc a = d : (list.head_eq_of_cons_eq hdc).symm
            ... = b :  list.head_eq_of_cons_eq (list.tail_eq_of_cons_eq hcd)
  }

theorem generalized (w : list (fin 2)) (a b : fin 2)
  (hab : a ≠ b)
  (hsqf: abstract_almost_square_free a b hab w) :
  generalized_almost_square_free w := by {
    split,

    intros c d hcontra,
    cases hcontra,
    exact hab (eq_cons_ne_nil (hsqf _ hcontra_left) (hsqf _ hcontra_right)),

    intros y hy,
    have hin: y ∈ ({ [a], [b], [a,b]}: set (list (fin 2))), from hsqf _ hy,
    cases hin,refine or.inl _, existsi a,          exact hin,
    cases hin,refine or.inl _, existsi b,          exact hin,
              refine or.inr _, existsi a,existsi b,exact hin,
  }
