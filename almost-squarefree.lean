import tactic.derive_fintype
import tactic.ring
import tactic.linarith
/- We prove that generalized almost square-free-ness is the same as (abstract)
almost squarefreeness for binary words.

000 is almost square-free but not overlapfree.
-/

def occurs_in {α:Type} (y w : list α) 
  :=
  ∃ x z : list α, w = x ++ y ++ z


def properly_occurs_squared_in {α:Type} (y w : list α) : Prop :=
  (y ≠ list.nil) ∧
  occurs_in (y ++ y) w

def abstract_almost_square_free
  (a b : fin 2)(h: a ≠ b)
  (w : list (fin 2))
  : Prop := 
  ∀ y : list (fin 2), properly_occurs_squared_in y w
                    → y ∈ ({  [a], [b], [a,b]}: set (list (fin 2)))

def almost_square_free (w : list (fin 2)): Prop :=
  abstract_almost_square_free 0 1 fin.zero_ne_one w

def generalized_almost_square_free {α:Type} (w : list α) : Prop :=
  (∀ a b : α, ¬ (properly_occurs_squared_in [a,b] w ∧ properly_occurs_squared_in [b,a] w))
  ∧
  ∀ y : list α, properly_occurs_squared_in y w →  (∃ a : α, y = [a]) ∨ ∃ a b :α, y= [a,b]

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

def not_overlapfree (w : list (fin 2)) : Prop :=
∃ y : list (fin 2), ∃ a : fin 2, occurs_in ((a :: y) ++ (a ::y) ++ [a]) w

def overlapfree (w : list (fin 2)) : Prop :=
¬ not_overlapfree w

def ctrex := ([0,0,0]: list (fin 2))

lemma cons_append_length (a b : fin 2) (x u z : list (fin 2)) :
  (x       ++ ((a :: (b :: u))   ++ (a :: (b :: u)))   ++ z).length =
  x.length +  u.length.succ.succ +  u.length.succ.succ +  z.length :=
  by {
    repeat{rw list.append_assoc},
    repeat{rw list.length_append},
    repeat{rw add_assoc},
    repeat{rw list.length_cons,},
  }

lemma square_length_ge_four (x z u: list (fin 2)) ( a b : fin 2):
  (x ++ ((a :: (b :: u)) ++ (a::(b::u))) ++ z).length ≥ 4 :=
  calc _ = x.length + u.length.succ.succ + u.length.succ.succ + z.length : cons_append_length _ _ _ _ _
  ... ≥ x.length + u.length.succ.succ + u.length.succ.succ            : le_self_add
  ... = x.length + (u.length.succ.succ + u.length.succ.succ)          : add_assoc _ _ _
  ... ≥            u.length.succ.succ + u.length.succ.succ            : le_add_self
  ... =            2*u.length + 4                                     : by ring
  ... ≥ _                                                             : le_add_self


lemma square_length_four (x z : list (fin 2)) ( a b : fin 2): (x ++ ([a,b] ++ [a,b]) ++ z).length ≥ 4 :=
  square_length_ge_four _ _ _ _ _


theorem ctrex_ne (x z : list (fin 2)) ( a b : fin 2): ctrex ≠ (x ++ ([a,b] ++ [a,b]) ++ z) :=
  λh, have ctrex.length ≥ 4, from
  calc ctrex.length = (x ++ ([a,b] ++ [a,b]) ++ z).length: by rw h
                ... ≥ 4: square_length_four _ _ _ _,
  nat.not_succ_le_self 3 this

example: generalized_almost_square_free ctrex := by {
  split,intros a b hcontra,cases hcontra,
  cases hcontra_left with hn h,
  cases h with x hx,
  cases hx with z hz,
  exact ctrex_ne x z a b hz,
  intros y hy,
  cases y,
  exfalso,exact hy.1 rfl,
  left,
  cases y_tl,
  existsi y_hd,refl,
  exfalso,
  cases hy with hy1 hy2,
  cases hy2 with x hx,
  cases hx with z hz,
  have : 3 ≥ 4, from calc
    3 = ctrex.length: rfl
  ... = (x ++ (y_hd :: y_tl_hd :: y_tl_tl ++ y_hd :: y_tl_hd :: y_tl_tl) ++ z).length : by rw hz
  ... = (x ++ (y_hd :: y_tl_hd :: y_tl_tl ++ y_hd :: y_tl_hd :: y_tl_tl) ++ z).length : by repeat {rw list.append_assoc}
  ... ≥ 4                                                                             : square_length_ge_four x z y_tl_tl y_hd y_tl_hd,
  exact nat.not_succ_le_self 3 this,
}

example: not_overlapfree ctrex := by {
  existsi list.nil,
  existsi (0:fin 2),
  existsi list.nil,
  existsi list.nil,simp,refl,
}
