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

theorem list_two_ne_one {a b c :  (fin 2)} : [a,b] ≠ [c] := by {
  intro h,
  have : 2 = 1, from congr_arg list.length h,
  have : 1 = 0, from nat.succ_injective this,
  exact zero_ne_one this.symm,
}  

theorem generalized (w : list (fin 2)) (a b : fin 2)(H:a ≠ b)
(h: abstract_almost_square_free a b H w) :
generalized_almost_square_free w := by {
  split,
  intros c d hcontra,
  cases hcontra,
  have hcd: [c,d] ∈ {[a], [b], [a,b]}, from h _ hcontra_left,
  have hdc: [d,c] ∈ {[a], [b] ,[a,b]}, from h _ hcontra_right,
  cases hcd,
    exfalso,exact list_two_ne_one hcd,
  cases hcd, exact list_two_ne_one hcd,
  cases hdc, exact list_two_ne_one hdc,
  cases hdc, exact list_two_ne_one hdc,

  have edb: d=b, from list.head_eq_of_cons_eq (list.tail_eq_of_cons_eq hcd), 
  have eda: d=a, from list.head_eq_of_cons_eq hdc,
  exact H (eq.trans eda.symm edb),

  intros y hy,
  have : y ∈ ({ [a], [b], [a,b]}: set (list (fin 2))), from h _ hy,
  cases this,refine or.inl _, existsi a,          exact this,
  cases this,refine or.inl _, existsi b,          exact this,
             refine or.inr _, existsi a,existsi b,exact this,
}
