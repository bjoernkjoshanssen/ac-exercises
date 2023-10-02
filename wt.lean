import ring_theory.int.basic

def wt {n:ℕ} : list (fin n) → ℕ :=
λ x, finset.card (list.to_finset x)

/- The following results characterize wt -/

theorem wt_nil {n:ℕ}:
wt (list.nil : list (fin n)) = 0 :=
by {
  unfold wt,
  rw list.to_finset_nil,
  exact rfl,
}

theorem wt_single {n:ℕ} (a:fin n.succ):
wt ([a]) = 1 :=
by {
  unfold wt,
  rw list.to_finset_cons,
  rw list.to_finset_nil,
  refl,
}

theorem wt_stay {n:ℕ} (a:fin n.succ) (x: list (fin n.succ)) (h: a ∈ x.to_finset):
wt (a :: x) = wt x :=
by {
  unfold wt,
  have h1: has_insert.insert a x.to_finset = x.to_finset, from finset.insert_eq_of_mem h,
  have h2: (a :: x).to_finset = has_insert.insert a x.to_finset, from list.to_finset_cons,
  have h3: (a :: x).to_finset = x.to_finset, from eq.trans h2 h1,
  rw h3,
}

def disjoint_lists {α:Type} [decidable_eq α] (x y : list α) : Prop :=
  disjoint (list.to_finset x) (list.to_finset y)

theorem wt_disjoint {n:ℕ} (x y : list (fin n))
  (h: disjoint_lists x y) :
wt (x++y) = wt x + wt y :=
by {
  unfold wt,
  rw list.to_finset_append,
  rwa finset.card_disjoint_union
}

/- End of results characterizing wt -/

theorem wt_comm {n:ℕ} (x y : list (fin n)):
wt (x++y) = wt (y++x) :=
by {
  unfold wt,
  repeat{rw list.to_finset_append},
  rw finset.union_comm,
}

theorem wt_append {n:ℕ} (x y : list (fin n)):
wt (x++y) ≤ wt x + wt y :=
by {
  unfold wt,
  rw list.to_finset_append,
  exact finset.card_union_le _ _
}



#eval wt  ([0,1,1,1,0]: list (fin 5))
