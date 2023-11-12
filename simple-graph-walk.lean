import Mathlib.CombiNatorics.SimpleGraph.Connectivity

theorem reverse_cons_length {V : Type} {G : SimpleGraph V} (a v₀ w : V)
  (p' : G.Walk a  w)
  (p  : G.Walk v₀ w)
  (h: G.Adj v₀ a) {k:ℕ}
  (hp: SimpleGraph.Walk.length p = Nat.succ k)
  (hp': p = SimpleGraph.Walk.cons h p')
  : p'.length = k :=
  have : p'.length.succ = k.succ :=
              calc _ = (SimpleGraph.Walk.cons h p').length := (SimpleGraph.Walk.length_cons _ _).symm
                _ = p.length                             := by rw [hp']
                _ = _                                    := hp
  Nat.succ.inj this

theorem vertex_in_walk_induction {V : Type} {G : SimpleGraph V} {S : Set V} {w : V}
(hw: ¬ w ∈ S) (n:ℕ):
∀ t, t ∈ S →  (∀ p : G.Walk t w, p.length = n → ∃ a, ∃ u, u ∈ S ∧ (G.Adj u a) ∧ ¬ a ∈ S)
:=
Nat.recOn n (
    (λ v hv _ hpl ↦
    have : v ≠ w := ne_of_mem_of_not_mem hv hw
    False.elim (this (SimpleGraph.Walk.eq_of_length_eq_zero hpl)))
)
(λ k h_ind v hv p hp ↦
    have : v ≠ w := ne_of_mem_of_not_mem hv hw
    Exists.elim (SimpleGraph.Walk.exists_eq_cons_of_ne this p) (
      λ b hb ↦ Exists.elim hb (λ h hh ↦ Exists.elim hh (
        λ p' hp' ↦
        have h_can_ind: p'.length = k := reverse_cons_length b v w p' p h hp hp'
        (Classical.em (b ∈ S)).elim (
          λ heq ↦
          h_ind b heq p' h_can_ind
        ) (
          λ hneq ↦ Exists.intro b (Exists.intro v (And.intro hv (And.intro h hneq)))
        )
      )
    )
  )
)

theorem vertex_in_walk {V : Type} {G : SimpleGraph V} (S : Set V) (w t : V)
(hw: ¬ w ∈ S) (ht: t ∈ S)
(p : G.Walk t w):
∃ a, ∃ u, u ∈ S ∧ (G.Adj u a) ∧ ¬ a ∈ S
:=
vertex_in_walk_induction   hw p.length t ht p rfl
