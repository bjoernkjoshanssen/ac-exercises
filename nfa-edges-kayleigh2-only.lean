import computability.NFA
import data.vector.basic


/-
A tactic proof that the 2-state Kayleigh graph for a word of length 3 uniquely accepts that word.
Here labeled walks are defined inductively and the labels are "forgotten" when we need
to show the walk is unique.

Dependencies:

kayleigh2_digraph_no_duplicates
  no_duplicate_edges

a_nice_case_of_hyde_theorem
  walk_of_walk_labeled
    walk
    walk_labeled      
      labeled_digraph
  kayleighwalk2
    kayleigh2_digraph
    kayleighsequence2

-/

structure labeled_digraph (α:Type) (σ:Type) := (edge : σ → σ → α → Prop)

@[derive decidable_eq]
inductive walk_labeled  {α : Type} {σ : Type} (M : labeled_digraph α σ) :
σ → σ → list α → Type 0
| nil {u : σ} : walk_labeled u u list.nil
| cons {u v w: σ} {a:α} {x: list α}
  (h : M.edge u v a) (p : walk_labeled v w x) :
                            walk_labeled u w (a::x)

inductive walk  {α : Type} {σ : Type} (M : labeled_digraph α σ) : σ → σ  → Type 0
| nil {u : σ} : walk u u
| cons {u v w: σ}
  (h : ∃ a:α, M.edge u v a) (p : walk v w) :
                            walk u w 

def walk_of_walk_labeled {α : Type} {σ : Type}
/- We remove the labels from the walk: -/
{M : labeled_digraph α σ} {u w : σ} {x : list α}
(wa : walk_labeled M u w x) :
      walk M u w :=
by {
  induction wa,
  exact walk.nil,
  refine walk.cons _ _,
  exact wa_v,existsi wa_a,exact wa_h,
  exact wa_ih,
}

def kayleigh2_digraph (x : vector (fin 2) 3) : labeled_digraph (fin 2) (fin 2) := {
  edge := (λ q1 q2 b,
    (q1,q2,b) = (0, 1, x.nth 0) ∨
    (q1,q2,b) = (1, 1, x.nth 1) ∨
    (q1,q2,b) = (1, 0, x.nth 2)
  )
}

def kayleighsequence2 : vector (fin 2) 4 := ⟨[0,1,1,0],rfl⟩
/- Although 1,0,0,1 would be better for induction proofs -/

def kayleighwalk2 (x0 x1 x2 : fin 2) :
  walk_labeled (kayleigh2_digraph ⟨[x0,x1,x2],rfl⟩)
  (((kayleighsequence2).nth 0):fin 2)
  (((kayleighsequence2).nth 3):fin 2)
  [x0,x1,x2] := by {
/-
This may seem not so useful but it was the reason for going from NFAs
to digraphs. Proving the analogous result using NFAs ran into the problem
that the definition of the Kayleigh graph NFA's transition function using ite's
depends on whether x1=x2.
-/
    refine walk_labeled.cons _ _,
    exact (kayleighsequence2).nth 1,
    refine or.inl _,split,

    refine walk_labeled.cons _ _,
    exact (kayleighsequence2).nth 2,
    refine or.inr _,refine or.inl _,split,

    refine walk_labeled.cons _ _,
    exact (kayleighsequence2).nth 3,
    refine or.inr _,refine or.inr _,split,

    exact walk_labeled.nil,
  }


/- This should sometimes be included or else a_nice_case_of_hyde_theorem
doesn't mean much: -/
def no_duplicate_edges (M : labeled_digraph (fin 2) (fin 2)) : Prop :=
  ∀ q1 q2 a b: fin 2, M.edge q1 q2 a → M.edge q1 q2 b → a = b 

theorem kayleigh2_no_duplicates  (x0 x1 x2 : fin 2):
no_duplicate_edges (kayleigh2_digraph ⟨[x0,x1,x2],rfl⟩) := by {
  intros _ _ _ _ ha hb,
  repeat {cases ha},repeat {cases hb},repeat {refl},
}


/- A_N_bounded_by should be this statement together with no_duplicates,
with q0 and qf, or an augmented digraph could have q0, qf included -/
theorem a_nice_case_of_hyde_theorem (x0 x1 x2 : fin 2) :
let M := (kayleigh2_digraph ⟨[x0,x1,x2],rfl⟩) in
∃ w : walk_labeled M 0 0 [x0,x1,x2],
  ∀ y0 y1 y2 : fin 2, 
   ∀ w' : walk_labeled M 0 0 [y0,y1,y2],
  walk_of_walk_labeled w =
  walk_of_walk_labeled w'

:= by {
  existsi (kayleighwalk2 x0 x1 x2),
  intros _ _ _ w,
  cases w, 
  cases (kayleighwalk2 x0 x1 x2),
  have :     v = 1, by {repeat {cases h},refl,},
  subst this,
  have :   w_v = 1, by {repeat {cases w_h},refl,},
  subst this,
  cases p, cases p_p, cases p_p_p,
  have :   p_v = 1, by {repeat {cases p_p_h},refl,},
  subst this,
  cases w_p, cases w_p_p, cases w_p_p_p,
  have : w_p_v = 1, by {repeat {cases w_p_p_h},refl,},
  subst this,
  refl,
}
