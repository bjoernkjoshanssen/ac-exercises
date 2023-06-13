import data.fintype.prod

structure labeled_digraph (α:Type) (σ:Type) := (edge : σ × σ × α → Prop)

def no_duplicate_edges {q:ℕ}{b : ℕ} (M : labeled_digraph (fin b) (fin q)) : Prop :=
  ∀ q1 q2: fin q, ∀ a b: fin b, M.edge (q1, q2, a) → M.edge (q1, q2, b) → a = b 

@[derive decidable_eq]
inductive walk_labeled_digraph  {α : Type} {σ : Type} (M : labeled_digraph α σ) :
σ → σ → list α → Type 0
| nil {u : σ} : walk_labeled_digraph u u list.nil
| cons {u v w: σ} {a:α} {x: list α}
  (h : M.edge (u, v, a)) (p : walk_labeled_digraph v w x) :
                            walk_labeled_digraph u w (a::x)

@[derive decidable_eq]
inductive unlabeled_walk_labeled_digraph  {α : Type} {σ : Type}
(M : labeled_digraph α σ) : σ → σ  → Type 0
| nil {u : σ} : unlabeled_walk_labeled_digraph u u
| cons {u v w: σ}
  (h : ∃ a:α, M.edge (u, v, a)) (p : unlabeled_walk_labeled_digraph v w) :
                            unlabeled_walk_labeled_digraph u w 


def walk_of_walk_labeled_digraph {α : Type} {σ : Type}
/- We remove the labels from the walk: -/
{M : labeled_digraph α σ} {u w : σ} {x : list α}
(wa : walk_labeled_digraph M u w x) :
      unlabeled_walk_labeled_digraph M u w :=
by {
  induction wa,
  exact unlabeled_walk_labeled_digraph.nil,
  refine unlabeled_walk_labeled_digraph.cons _ _,
  exact wa_v,existsi wa_a,exact wa_h,
  exact wa_ih,
}

open_locale classical

def E_N_bounded_by {b:ℕ} (x:list (fin b)) (e:ℕ) : Prop :=
∃ q : ℕ, -- as an upper bound we could take q = e.succ but that would need a proof
  ∃ q0 qf : fin q, ∃ M : labeled_digraph (fin b) (fin q),
  finset.card (finset.filter M.edge (finset.univ)) ≤ e
  ∧ no_duplicate_edges M
  ∧ ∃ w : walk_labeled_digraph M q0 qf x,
    ∀ y : list (fin b), y.length = x.length → 
    ∀ w' : walk_labeled_digraph M q0 qf y,
    walk_of_walk_labeled_digraph w =
    walk_of_walk_labeled_digraph w'
/- Note that if we don't require no duplicate edges then
a 1-state automaton with b states would do.
-/
/- Given no_duplicate_edges, it may be better to ignore y and say:
  for each unlabeled walk w' of the same length as w
  from q0 to qf, w = w' -/

theorem E_N_list_nil {b:ℕ} : E_N_bounded_by (list.nil : list (fin b)) 0 :=
  by {
    existsi (1), existsi (0:fin 1), existsi (0:fin 1),
    existsi ({edge:= (λ x, false)} : labeled_digraph (fin b) (fin 1)),
    split, simp, split,                 -- Cardinality
    intros _ _ _ _ _ _,exfalso,cases ᾰ, /- No duplicate edges -/
    existsi walk_labeled_digraph.nil,   /- Uniqueness -/
    intros y hy w',
    have : y = list.nil, from list.length_eq_zero.mp hy,
    subst this,
    cases w',
    refl,
  }

def thewalk1 {b:ℕ}:
    let M := ({edge:= (λ x, x.2.2=0)} : labeled_digraph (fin b.succ) (fin 1)) in
    walk_labeled_digraph M 0 0 [0]:= by {
      refine walk_labeled_digraph.cons _ _,
      exact 0,exact rfl,exact walk_labeled_digraph.nil,
    }

def thewalk2 {b:ℕ}:
    let M := ({edge:= (λ x, x.2.2=0)} : labeled_digraph (fin b.succ) (fin 1)) in
    walk_labeled_digraph M 0 0 [0,0]:= by {
      refine walk_labeled_digraph.cons _ _, exact 0,exact rfl,
      refine walk_labeled_digraph.cons _ _, exact 0,exact rfl,
      exact walk_labeled_digraph.nil,
    }


theorem prod_eq_zero {b:ℕ} : -- by tidy
      finset.filter (
        λ (x : fin 1 × fin 1 × fin b.succ), x.snd.snd = 0
      ) finset.univ
     = {(0,0,0)} := by {
      apply finset.ext,
      intro a,
      simp,
      split,
      intro h,
      refine prod.ext _ _, exact fin.eq_zero _,
      refine prod.ext _ _, exact fin.eq_zero _,
      exact h,
      intro h,rw h,
    }

theorem E_N_one {b:ℕ} : E_N_bounded_by ([0] : list (fin b.succ)) 1 :=
  by {
    existsi (1), existsi (0:fin 1), existsi (0:fin 1),
    let M := ({edge:= (λ x, x.2.2=0)} : labeled_digraph (fin b.succ) (fin 1)),
    
    existsi M,split,
 -- Cardinality:
    simp,rw prod_eq_zero,simp,
    
    split,
     /- No duplicate edges: -/
    intros _ _ _ _ _ _,
    cases ᾰ,
    exact ᾰ_1.symm,
    /- Uniqueness: -/
    existsi thewalk1,
    intros y hy w',
    have : ∃ a, ∃ t, y = a :: t, from list.exists_of_length_succ y hy,
    cases this with a ha,
    cases ha with t ht,
    subst ht,
    cases t,
    cases w',
    cases w'_p,
    exact rfl,
    exfalso,
    exact nat.succ_ne_zero _ (nat.succ_injective hy)
  }


theorem E_N_two {b:ℕ} : E_N_bounded_by ([0,0] : list (fin b.succ)) 1 :=
  by {
    existsi (1), existsi (0:fin 1), existsi (0:fin 1),
    let M := ({edge:= (λ x, x.2.2=0)} : labeled_digraph (fin b.succ) (fin 1)),
    
    existsi M,split,
 -- Cardinality:
    simp,rw tidy_one,simp,
    
    split,
     /- No duplicate edges: -/
    intros _ _ _ _ _ _,
    cases ᾰ,
    exact ᾰ_1.symm,
    /- Uniqueness: -/
    existsi thewalk2,
    intros y hy w',
    have : ∃ a, ∃ t, y = a :: t, from list.exists_of_length_succ y hy,
    cases this with a ha,
    cases ha with t ht,
    subst ht,
    cases t,
    exfalso,
    exact nat.succ_ne_zero _ (nat.succ_injective hy).symm,
    cases t_tl,
    cases w',
    cases w'_v,cases w'_v_val,
    cases w'_p,
    cases w'_p_p,
    exact rfl,
    exfalso,
    exact not_lt_zero' (nat.succ_lt_succ_iff.mp w'_v_property),
    exfalso,
    exact nat.succ_ne_zero _ (nat.succ_injective (nat.succ_injective hy)),
  }

