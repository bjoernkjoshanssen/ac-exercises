def kbo_alpha_morph (l:ℕ) : fin l.succ → list (fin l.succ) :=
λ i, ite (i.1=l) [0] [0,i+1]  

def kbo_morph (l:ℕ): list (fin l.succ) → list (fin l.succ) :=
λ x, list.rec_on x list.nil (
  λ hd, λ tl, λ outputsofar,
  (kbo_alpha_morph l hd) ++ outputsofar
)

theorem is_morph (l:ℕ) (x: list (fin l.succ)) : ∀ y : list (fin l.succ),
kbo_morph l (x ++ y) = kbo_morph l x ++ kbo_morph l y :=
list.rec_on x (λ y, rfl) (
  λ hd tl h_ind, λ y,
  show kbo_morph l (hd :: tl ++ y) = kbo_morph l (hd :: tl) ++ kbo_morph l y, from
  calc _ = (kbo_alpha_morph l hd) ++ kbo_morph l (tl ++ y)            : rfl
     ... = (kbo_alpha_morph l hd) ++ (kbo_morph l tl ++ kbo_morph l y): by rw (h_ind y)
     ... = ((kbo_alpha_morph l hd) ++ kbo_morph l tl) ++ kbo_morph l y: (list.append_assoc _ _ _).symm
     ... = _: rfl
)
