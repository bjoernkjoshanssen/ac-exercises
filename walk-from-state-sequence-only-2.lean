structure digraph (σ:Type) := (edge : σ → σ → Prop)

inductive walk_digraph {σ : Type} (M : digraph σ) : σ → σ  → Type 0
  | nil {u : σ} : walk_digraph u u
  | cons {u v w: σ} (h : M.edge v w) (p : walk_digraph u v) : walk_digraph u w 

def digraph_of_seq4 {σ:Type} (s0 s1 s2 s3 : σ) : digraph σ :=
  by {
    exact {
      edge := λ q0 q1, (q0,q1)=(s0,s1) ∨ (q0,q1) = (s1,s2) ∨ (q0,q1)=(s2,s3)
    },
  }

def walk_of_digraph_of_seq4 {σ:Type}
  (s0 s1 s2 s3 : σ) :
  walk_digraph (digraph_of_seq4 s0 s1 s2 s3) s0 s3
  :=
  by {
    refine walk_digraph.cons _ _,exact s2,refine or.inr _,refine or.inr _,refl,
    refine walk_digraph.cons _ _,exact s1,refine or.inr _,refine or.inl _,refl,
    refine walk_digraph.cons _ _,exact s0,refine or.inl _,refl,
    exact walk_digraph.nil,
  }
