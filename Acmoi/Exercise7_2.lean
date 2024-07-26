import Mathlib.Data.Set.Finite

-- Solution to Exercise 7.2.

def width {n:Nat} : List (Fin n) → Nat :=
fun x ↦ Finset.card (List.toFinset x)

theorem width_nil {n:ℕ}:
width (List.nil : List (Fin n)) = 0 :=
by {
  unfold width
  rw [List.toFinset_nil]
  exact rfl
}

theorem width_single {n:ℕ} (a:Fin n.succ):
width ([a]) = 1 :=
by {
  unfold width
  rw [List.toFinset_cons,List.toFinset_nil]
  exact rfl
}

theorem width_stay {n:ℕ} (a:Fin n.succ) (x: List (Fin n.succ)) (h: a ∈ x.toFinset):
width (a :: x) = width x :=
by {
  unfold width
  have h1: insert a x.toFinset = x.toFinset := Finset.insert_eq_of_mem h
  have h2: (a :: x).toFinset = insert a x.toFinset := List.toFinset_cons
  have h3: (a :: x).toFinset = x.toFinset:= Eq.trans h2 h1
  rw [h3]
}

def disjoint_lists {α:Type} [DecidableEq α] (x y : List α) : Prop :=
  Disjoint (List.toFinset x) (List.toFinset y)

theorem width_disjoint {n:ℕ} (x y : List (Fin n))
  (h: disjoint_lists x y) :
width (x++y) = width x + width y :=
by {
  unfold width
  rw [List.toFinset_append]
  rwa [Finset.card_union_of_disjoint]
}

/- End of results characterizing width -/

theorem width_comm {n:ℕ} (x y : List (Fin n)):
width (x++y) = width (y++x) := by
  unfold width
  have : List.toFinset (x ++ y) = List.toFinset (y ++ x) := by
      refine List.toFinset_eq_of_perm (x ++ y) (y ++ x) ?h
      exact List.perm_append_comm
  rw [this]

theorem width_append {n:ℕ} (x y : List (Fin n)):
width (x++y) ≤ width x + width y :=
by {
  unfold width
  rw [List.toFinset_append]
  exact Finset.card_union_le _ _
}



#eval width  ([0,1,1,1,0]: List (Fin 5))
