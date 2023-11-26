-- Solution to Exercise 2.3.
import Mathlib.Tactic.Basic
import Mathlib.Data.Vector.Basic
import Mathlib.Data.Nat.Basic

set_option tactic.hygienic false

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

-- @[derive decidable_eq]
inductive walk_labeled  {α : Type} {σ : Type} (M : labeled_digraph α σ) :
σ → σ → List α → Type 0
| nil {u : σ} : walk_labeled M u u List.nil
| cons {u v w: σ} {a:α} {x: List α}
  (h : M.edge u v a) (p : walk_labeled M v w x) :
                            walk_labeled M u w (a::x)

inductive walk  {α : Type} {σ : Type} (M : labeled_digraph α σ) : σ → σ  → Type 0
| nil {u : σ} : walk M u u
| cons {u v w: σ}
  (h : ∃ a:α, M.edge u v a) (p : walk M v w) :
                            walk M u w

noncomputable def walk_of_walk_labeled {α : Type} {σ : Type}
/- We remove the labels from the walk: -/
{M : labeled_digraph α σ} {u w : σ} {x : List α}
(wa : walk_labeled M u w x) :
      walk M u w :=
walk_labeled.recOn wa walk.nil (
  λ {uu vv ww a xx} ↦ λ e _ wawa ↦

  by {
    refine walk.cons (by {
      exists a

    }) (by {
      exact wawa
    })
  }
)

def kayleigh2_digraph (x : Vector (Fin 2) 3) : labeled_digraph (Fin 2) (Fin 2) := {
  edge := (λ q1 q2 b ↦
    (q1,q2,b) = (0, 1, x.get 0) ∨
    (q1,q2,b) = (1, 1, x.get 1) ∨
    (q1,q2,b) = (1, 0, x.get 2)
  )
}

def kayleighsequence2 : Vector (Fin 2) 4 := ⟨[0,1,1,0],rfl⟩
/- Although 1,0,0,1 would be better for induction proofs -/

def kayleighwalk2 (x0 x1 x2 : Fin 2) :
  walk_labeled (kayleigh2_digraph ⟨[x0,x1,x2],rfl⟩)
  (((kayleighsequence2).get 0):Fin 2)
  (((kayleighsequence2).get 3):Fin 2)
  [x0,x1,x2] :=
  -- sorry
  by {
/-
This may seem not so useful but it was the reason for going from NFAs
to digraphs. Proving the analogous result using NFAs ran into the problem
that the definition of the Kayleigh graph NFA's transition function using ite's
depends on whether x1=x2.
-/

    refine' walk_labeled.cons _ _
    exact (kayleighsequence2).get 1
    refine' Or.inl _
    constructor

    refine' walk_labeled.cons _ _
    exact (kayleighsequence2).get 2
    refine' Or.inr _
    refine' Or.inl _
    constructor

    refine' walk_labeled.cons _ _
    exact (kayleighsequence2).get 3
    refine' Or.inr _
    refine' Or.inr _
    constructor

    exact walk_labeled.nil
  }


/- This should sometimes be included or else a_nice_case_of_hyde_theorem
doesn't mean much: -/
def no_duplicate_edges (M : labeled_digraph (Fin 2) (Fin 2)) : Prop :=
  ∀ q1 q2 a b: Fin 2, M.edge q1 q2 a → M.edge q1 q2 b → a = b

theorem kayleigh2_no_duplicates  (x0 x1 x2 : Fin 2):
no_duplicate_edges (kayleigh2_digraph ⟨[x0,x1,x2],rfl⟩) := by {
  intros x_0 x_1 x_2 a ha hb
  rcases ha with hha | pp
  rcases hha with hhha | ppp

  rcases hb with hhb | pppp

  rcases hhb with hhhb | ppppp
  rfl
  exfalso
  rcases pppp with hha | pp
  have : 0 = 1 := congr_arg (λ x ↦ x.1) hha
  exact Fin.zero_ne_one this
  have : 0 = 1 := congr_arg (λ x ↦ x.1) pp
  exact Fin.zero_ne_one this
  rcases hb with hhb | ppq
  rcases pp with ppp | pppp
  have hg0: x_0 = 0 := congr_arg (λ x ↦ x.1) hhb
  have hg1: x_0 = 1 := congr_arg (λ x ↦ x.1) ppp
  have : 0 = 1 := Eq.trans hg0.symm hg1
  exfalso
  exact Fin.zero_ne_one this

  have hg0: x_0 = 0 := congr_arg (λ x ↦ x.1) hhb
  have hg1: x_0 = 1 := congr_arg (λ x ↦ x.1) pppp
  have : 0 = 1 := Eq.trans hg0.symm hg1
  exfalso
  exact Fin.zero_ne_one this
  rcases ppq with ghh | ghhh
  rcases pp with ggh | ggh
  have : (x_0,x_1,x_2) = (x_0,x_1,a) :=  (Eq.trans ghh ggh.symm).symm
  exact congr_arg (λ x ↦ x.2.2) this
  have hj: x_1 = 1 := congr_arg (λ x ↦ x.2.1) ghh
  have hjj: x_1 = 0 := congr_arg (λ x ↦ x.2.1) ggh
  have : 0 = 1 := Eq.trans hjj.symm hj
  exfalso
  exact Fin.zero_ne_one this
  rcases pp with qz | qzz

  have hj: x_1 = 1 := congr_arg (λ x ↦ x.2.1) qz
  have hjj: x_1 = 0 := congr_arg (λ x ↦ x.2.1) ghhh
  have : 0 = 1 := Eq.trans hjj.symm hj
  exfalso
  exact Fin.zero_ne_one this

  have : (x_0,x_1,x_2) = (x_0,x_1,a) :=  (Eq.trans qzz ghhh.symm)
  exact congr_arg (λ x ↦ x.2.2) this


}


/- A_N_bounded_by should be this statement together with no_duplicates,
with q0 and qf, or an augmented digraph could have q0, qf included -/
theorem a_nice_case_of_hyde_theorem (x0 x1 x2 : Fin 2) :
let M := (kayleigh2_digraph ⟨[x0,x1,x2],rfl⟩)
∃ w : walk_labeled M 0 0 [x0,x1,x2],
  ∀ y0 y1 y2 : Fin 2,
   ∀ w' : walk_labeled M 0 0 [y0,y1,y2],
  walk_of_walk_labeled w =
  walk_of_walk_labeled w'
:=


 by {
  exists (kayleighwalk2 x0 x1 x2)
  intros _ _ _ w

  cases w
  cases (kayleighwalk2 x0 x1 x2)



  cases h
  have : v = 1 := congr_arg (λ xx ↦ xx.2.1) h_2
  subst this

  cases p
  cases h
  have : v = 1 := congr_arg (λ xx ↦ xx.2.1) h_3
  subst this

  exfalso
  have : 0 = 1  := (congr_arg (λ xx ↦ xx.1) h_3).symm
  exact Fin.zero_ne_one this

  cases h_3
  have : v = 1 := congr_arg (λ xx ↦ xx.2.1) h
  subst this
  cases h_1
  have : v_1 = 1 := congr_arg (λ xx ↦ xx.2.1) h_3
  subst this
  cases p_1
  cases p_2
  cases h_1
  have : v = 1 := congr_arg (λ xx ↦ xx.2.1) h_5
  subst this

  exfalso
  have : 0 = 1  := (congr_arg (λ xx ↦ xx.1) h_5).symm
  exact Fin.zero_ne_one this

  cases h_5
  cases p_1
  cases h_4

  exfalso
  have : 0 = 1  := (congr_arg (λ xx ↦ xx.1) h_5).symm
  exact Fin.zero_ne_one this

  cases h_5
  exfalso
  have : 0 = 1  := congr_arg (λ xx ↦ xx.2.1) h_4
  exact Fin.zero_ne_one this

  have : v = 1 := congr_arg (λ xx ↦ xx.2.1) h_1
  subst this
  cases p
  cases p_1
  cases h_5

  exfalso
  have : 0 = 1  := (congr_arg (λ xx ↦ xx.1) h_6).symm
  exact Fin.zero_ne_one this

  cases h_6

  exfalso
  have : kayleighsequence2.get 3 = 1 := congr_arg (λ xx ↦ xx.2.1) h_5
  exact Fin.zero_ne_one this

  have : y0 = x0 := congr_arg (λ xx ↦ xx.2.2) h_2
  subst this

  have : y1 = x1 := congr_arg (λ xx ↦ xx.2.2) h
  subst this
  have : y2 = x2 := congr_arg (λ xx ↦ xx.2.2) h_4
  subst this
  rfl
  have : v = 0 := congr_arg (λ xx ↦ xx.2.1) h_1

  subst this
  cases p_1
  cases p
  cases p_1
  cases h_4

  exfalso
  have : 0 = 1 := congr_arg (λ xx ↦ xx.2.1) h_6
  exact Fin.zero_ne_one this

  cases h_6

  exfalso
  have : 0 = 1 := congr_arg (λ xx ↦ xx.2.1) h_4
  exact Fin.zero_ne_one this

  cases h_5

  exfalso
  have : 0 = 1 := congr_arg (λ xx ↦ xx.2.1) h_6
  exact Fin.zero_ne_one this

  cases h_6

  exfalso
  have : 0 = 1 := congr_arg (λ xx ↦ xx.2.1) h_5
  exact Fin.zero_ne_one this

  have : y0 = x0 := congr_arg (λ xx ↦ xx.2.2) h_2
  subst this

  have : y1 = x1 := congr_arg (λ xx ↦ xx.2.2) h
  subst this
  have : y2 = x2 := congr_arg (λ xx ↦ xx.2.2) h_4
  subst this

  exfalso
  have : 0 = 1 := congr_arg (λ xx ↦ xx.1) h_5
  exact Fin.zero_ne_one this

  cases h_3

  exfalso
  have : 0 = 1 := congr_arg (λ xx ↦ xx.1) h_1
  exact Fin.zero_ne_one this

  exfalso
  have : 0 = 1 := congr_arg (λ xx ↦ xx.1) h_1
  exact Fin.zero_ne_one this

-- should use the properties before doing cases!
  have : v = 0 := congr_arg (λ xx ↦ xx.2.1) h
  subst this
  have : y1 = x2 := congr_arg (λ xx ↦ xx.2.2) h
  subst this
  have : y0 = x0 := congr_arg (λ xx ↦ xx.2.2) h_2
  subst this
  cases h_1
  have : v_1 = 1 := congr_arg (λ xx ↦ xx.2.1) h_3
  subst this
  cases p_1
  cases p

  cases p_1
  cases p_2

  cases p


  cases h_1
  exfalso
  have : 0 = 1 := congr_arg (λ xx ↦ xx.1) h_6.symm
  exact Fin.zero_ne_one this

  cases h_6
  have : v = 1 := congr_arg (λ xx ↦ xx.2.1) h_1
  subst this
  cases h_5

  exfalso
  have : 0 = 1 := congr_arg (λ xx ↦ xx.2.1) h_6
  exact Fin.zero_ne_one this

  cases h_6

  exfalso
  have : 0 = 1 := congr_arg (λ xx ↦ xx.1) h_5
  exact Fin.zero_ne_one this

  exfalso
  have : 0 = 1 := congr_arg (λ xx ↦ xx.1) h_5
  exact Fin.zero_ne_one this

  have : v = 0 := congr_arg (λ xx ↦ xx.2.1) h_1
  subst this

  have : x1 = y1 := congr_arg (λ xx ↦ xx.2.2) h_1
  subst this

  cases h_5

  exfalso
  have : 0 = 1 := congr_arg (λ xx ↦ xx.2.1) h_6
  exact Fin.zero_ne_one this

  cases h_6

  exfalso
  have : 0 = 1 := congr_arg (λ xx ↦ xx.2.1) h_5
  exact Fin.zero_ne_one this

  exfalso
  have : 0 = 1 := congr_arg (λ xx ↦ xx.1) h_5
  exact Fin.zero_ne_one this

  cases h_3

  exfalso
  have : 0 = 1 := congr_arg (λ xx ↦ xx.1) h_1
  exact Fin.zero_ne_one this

  exfalso
  have : 0 = 1 := congr_arg (λ xx ↦ xx.1) h_1
  exact Fin.zero_ne_one this

  cases h_2

  exfalso
  have : 0 = 1 := congr_arg (λ xx ↦ xx.1) h
  exact Fin.zero_ne_one this

  exfalso
  have : 0 = 1 := congr_arg (λ xx ↦ xx.1) h
  exact Fin.zero_ne_one this
}
