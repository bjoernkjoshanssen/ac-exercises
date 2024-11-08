-- Solution to Exercise 1.19.

structure digraph (σ:Type) where (edge : σ → σ → Prop)

inductive walk_digraph {σ : Type} (M : digraph σ) : σ → σ  → Type 0
  | nil {u : σ} : walk_digraph M u u
  | cons {u v w: σ} (h : M.edge v w) (p : walk_digraph M u v) : walk_digraph M u w

def digraph_of_seq4 {σ:Type} (s0 s1 s2 s3 : σ) : digraph σ := {
      edge := λ q0 q1 ↦ (q0,q1)=(s0,s1) ∨ (q0,q1) = (s1,s2) ∨ (q0,q1)=(s2,s3)
    }

def walk_of_digraph_of_seq4 {σ:Type}
  (s0 s1 s2 s3 : σ) :
  walk_digraph (digraph_of_seq4 s0 s1 s2 s3) s0 s3
  :=
  walk_digraph.cons (Or.inr (Or.inr rfl)) (
    walk_digraph.cons (Or.inr (Or.inl rfl)) (
      walk_digraph.cons (Or.inl rfl) (walk_digraph.nil)
    )
  )
