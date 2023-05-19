import combinatorics.simple_graph.connectivity

lemma reverse_cons_length {V : Type} {G : simple_graph V} (a v₀ w : V)
  (p' : G.walk a  w)
  (p  : G.walk v₀ w)
  (h: G.adj v₀ a) {k:ℕ}
  (hp: simple_graph.walk.length p = nat.succ k)
  (hp': p = simple_graph.walk.cons h p')
  : p'.length = k :=
  have p'.length.succ = k.succ, from
              calc _ = (simple_graph.walk.cons h p').length : (simple_graph.walk.length_cons _ _).symm
                ... = p.length                             : by rw hp'
                ... = _                                    : hp,
  nat.succ.inj this

theorem vertex_in_walk_induction {V : Type} {G : simple_graph V} {S : set V} {w : V}
(hw: ¬ w ∈ S) (n:ℕ):
∀ t, t ∈ S →  (∀ p : G.walk t w, p.length = n → ∃ a, ∃ u, u ∈ S ∧ (G.adj u a) ∧ ¬ a ∈ S)
:=
nat.rec_on n (
    (λ v hv _ hpl,
    have v ≠ w, from by tidy,
    false.elim (this (simple_graph.walk.eq_of_length_eq_zero hpl)))
)
(λ k h_ind v hv p hp,
    have v ≠ w, from by tidy,
    exists.elim (simple_graph.walk.exists_eq_cons_of_ne this p) (
      λ b hb, exists.elim hb (λ h hh, exists.elim hh (
        λ p' hp',
        have h_can_ind: p'.length = k, from reverse_cons_length b v w p' p h hp hp',
        (classical.em (b ∈ S)).elim (
          λ heq,
          h_ind b heq p' h_can_ind
        ) (
          λ hneq, exists.intro b (exists.intro v (and.intro hv (and.intro h hneq)))
        )
      )
    )
  )
)

theorem vertex_in_walk {V : Type} {G : simple_graph V} (S : set V) (w t : V)
(hw: ¬ w ∈ S) (ht: t ∈ S)
(p : G.walk t w):
∃ a, ∃ u, u ∈ S ∧ (G.adj u a) ∧ ¬ a ∈ S
:=
vertex_in_walk_induction   hw p.length t ht p rfl
