import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Prod

-- Solution to Exercise 2.4.

set_option tactic.hygienic false

structure labeled_digraph (α:Type) (σ:Type) := (edge : σ × σ × α → Prop)

def no_duplicate_edges {q:ℕ}{b : ℕ} (M : labeled_digraph (Fin b) (Fin q)) : Prop :=
  ∀ q1 q2: Fin q, ∀ a b: Fin b, M.edge (q1, q2, a) → M.edge (q1, q2, b) → a = b

-- @[derive decidable_eq]
inductive walk_labeled_digraph  {α : Type} {σ : Type} (M : labeled_digraph α σ) :
σ → σ → List α → Type 0
| nil {u : σ} : walk_labeled_digraph M u u List.nil
| cons {u v w: σ} {a:α} {x: List α}
  (h : M.edge (u, v, a)) (p : walk_labeled_digraph M v w x) :
                            walk_labeled_digraph M u w (a::x)

-- @[derive decidable_eq]
inductive unlabeled_walk_labeled_digraph  {α : Type} {σ : Type}
(M : labeled_digraph α σ) : σ → σ  → Type 0
| nil {u : σ} : unlabeled_walk_labeled_digraph M u u
| cons {u v w: σ}
  (h : ∃ a:α, M.edge (u, v, a)) (p : unlabeled_walk_labeled_digraph M v w) :
                            unlabeled_walk_labeled_digraph M u w


noncomputable def walk_of_walk_labeled_digraph {α : Type} {σ : Type}
/- We remove the labels from the walk: -/
{M : labeled_digraph α σ} {u w : σ} {x : List α}
(wa : walk_labeled_digraph M u w x) :
      unlabeled_walk_labeled_digraph M u w := by
  induction wa with
  |nil => exact unlabeled_walk_labeled_digraph.nil
  |cons p =>
    apply unlabeled_walk_labeled_digraph.cons
    exists a
    exact p_ih

open Classical

def E_N_bounded_by {b:ℕ} (x:List (Fin b)) (e:ℕ) : Prop :=
∃ q : ℕ, -- as an upper bound we could take q = e.succ but that would need a proof
  ∃ q0 qf : Fin q, ∃ M : labeled_digraph (Fin b) (Fin q),
  Finset.card (Finset.filter M.edge (Finset.univ)) ≤ e
  ∧ no_duplicate_edges M
  ∧ ∃ w : walk_labeled_digraph M q0 qf x,
    ∀ y : List (Fin b), y.length = x.length →
    ∀ w' : walk_labeled_digraph M q0 qf y,
    walk_of_walk_labeled_digraph w =
    walk_of_walk_labeled_digraph w'
/- Note that if we don't require no duplicate edges then
a 1-state automaton with b states would do.
-/
/- Given no_duplicate_edges, it may be better to ignore y and say:
  for each unlabeled walk w' of the same length as w
  from q0 to qf, w = w' -/

theorem E_N_List_nil {b:ℕ} : E_N_bounded_by (List.nil : List (Fin b)) 0 :=
  by {
    exists (1)
    exists (0:Fin 1)
    exists (0:Fin 1)
    exists ({edge:= (λ _ ↦ false)} : labeled_digraph (Fin b) (Fin 1))
    constructor
    simp
    constructor
                     -- Cardinality
    intros _ _ _ _ _
    exfalso
    cases a_1
     /- No duplicate edges -/
    exists walk_labeled_digraph.nil   /- Uniqueness -/
    intros y hy w'
    have : y = List.nil := List.length_eq_zero.mp hy
    subst this
    cases w'
    rfl
  }

def thewalk1 {b:ℕ}:
    let M := ({edge:= (λ x ↦ x.2.2=0)} : labeled_digraph (Fin b.succ) (Fin 1))
    walk_labeled_digraph M 0 0 [0]:= by {
      let M := ({edge:= (λ x ↦ x.2.2=0)} : labeled_digraph (Fin b.succ) (Fin 1))
      exact @walk_labeled_digraph.cons (Fin b.succ) (Fin 1) M 0 0 0 0 [] rfl walk_labeled_digraph.nil
    }

def thewalk2 {b:ℕ}:
    let M := ({edge:= (λ x ↦ x.2.2=0)} : labeled_digraph (Fin b.succ) (Fin 1))
    walk_labeled_digraph M 0 0 [0,0]:= by {
      refine' walk_labeled_digraph.cons _ _
      exact 0
      exact rfl
      refine' walk_labeled_digraph.cons _ _
      exact 0
      exact rfl
      exact walk_labeled_digraph.nil
    }


theorem prod_eq_zero {b:ℕ} : -- by tidy
      Finset.filter (
        λ (x : Fin 1 × Fin 1 × Fin b.succ) ↦ x.snd.snd = 0
      ) Finset.univ
     = {(0,0,0)} := by
      apply Finset.ext
      intro a
      simp
      constructor
      intro h
      apply Prod.ext
      simp
      exact Fin.fin_one_eq_zero a.1
      simp
      ext
      simp
      tauto
      intro h
      rw [h]

theorem E_N_one {b:ℕ} : E_N_bounded_by ([0] : List (Fin b.succ)) 1 := by
    exists 1, 0, 0, {edge:= (λ x ↦ x.2.2=0)}
    constructor
 -- Cardinality:
    simp
    refine Finset.card_le_one_iff.mpr ?left.a
    intro u v hu hv
    simp at hu
    simp at hv
    ext
    · simp
    · simp
    · rw [hu,hv]


    constructor
     /- No duplicate edges: -/
    intros _ _ _ _ _ _
    cases a_1
    exact a_2.symm
    /- Uniqueness: -/
    exists thewalk1
    intros y hy w'
    obtain ⟨a, t, ht⟩ := List.exists_of_length_succ y hy
    subst ht
    cases t
    cases w'
    cases p
    · exact rfl
    · exfalso; exact Nat.succ_ne_zero _ (Nat.succ_injective hy)


theorem E_N_two {b:ℕ} : E_N_bounded_by ([0,0] : List (Fin b.succ)) 1 :=
  by {
    exists 1, 0, 0, {edge:= (λ x ↦ x.2.2=0)}
    constructor
 -- Cardinality:
    simp
    refine Finset.card_le_one_iff.mpr ?left.a
    intro u v hu hv
    simp at hu
    simp at hv
    ext
    · simp
    · simp
    · rw [hu,hv]

    constructor
     /- No duplicate edges: -/
    intros _ _ _ _ _ _
    cases a_1
    exact a_2.symm
    /- Uniqueness: -/
    exists thewalk2
    intros y hy w'
    obtain ⟨a, t, ht⟩ := List.exists_of_length_succ y hy
    subst ht
    cases t
    exfalso
    exact Nat.succ_ne_zero _ (Nat.succ_injective hy).symm
    cases tail
    cases w'
    cases v
    cases val
    cases p
    · cases p_1
      · exact rfl
    · exfalso; simp at isLt
    · exfalso; simp at hy
  }
