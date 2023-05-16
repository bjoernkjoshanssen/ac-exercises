import data.real.nnreal
--import data.vector.basic
/-

Exercise 6.1: Let a1,...,ak,b1,...,bk ≥ 0 be real numbers such that for each 1≤i≤k, ai ≤bi. Then
∏^k_{i=1}ai ≤∏^k_{i=1}b_i.

Exercise 6.2: If f_i achieves maximum at c_i then prod_i f_i (x_i) achieves maximum at c.

To to do the inductive step we need list.rec_on and hence projections p1 and p2.
However, def dominates below shows a better way of working with lists in some ways.
-/

def dominates (a : list (nnreal×nnreal)) : Prop := ∀ i ∈ a, (i.1:nnreal) ≤ i.2

lemma dom_cons (hd : nnreal×nnreal) (tl: list (nnreal×nnreal)): dominates (hd:: tl) → dominates tl :=
  λ h i hi,
  have i ∈ hd :: tl, from list.mem_cons_of_mem hd hi,
  h i this

def p1 {U:Type}: list (U×U) → list(U) :=
λ l, list.map (λ x : U×U, x.1) l

def p2 {U:Type}: list (U×U) → list(U) :=
λ l, list.map (λ x : U×U, x.2) l


theorem p1_list_of_fn {U:Type} {n:ℕ} (Q1 Q2: fin n → U):
p1 (list.of_fn (λ k, (Q1 k, Q2 k))) = 
list.of_fn (λ k, Q1 k) :=
list.map_of_fn _ _ 

theorem p2_list_of_fn {U:Type} {n:ℕ} (Q1 Q2: fin n → U) : p2 (list.of_fn (λ k, (Q1 k, Q2 k))) = 
list.of_fn (λ k, Q2 k) :=
list.map_of_fn _ _ 

theorem exercise_6_1 (a : list (nnreal×nnreal)) :
  dominates (a) →
  (p1 a).prod ≤ (p2 a).prod := list.rec_on a (
    λ hdom, le_refl _
  ) (
    λ hd tl h_ind hdom,
    have hhh: hd.1 ≤ hd.2, from hdom hd (list.mem_cons_self hd tl),
    calc
      (p1 (hd :: tl)).prod = hd.1   *  (p1 tl).prod : list.prod_cons
                       ... ≤ hd.2   *  (p1 tl).prod : mul_le_mul_right' hhh (p1 tl).prod
                       ... ≤ hd.2   *  (p2 tl).prod : mul_le_mul_left' (h_ind (dom_cons hd tl hdom)) _
                       ... = (hd.2 :: (p2 tl)).prod : list.prod_cons.symm
  )


def diag {n:ℕ} (F: fin n → nnreal → nnreal): vector nnreal n → list nnreal :=  -- (x1, x2) -> (F 1 x1, F 2 x2)
λ x, list.of_fn (λ i : fin n, F i (x.nth i))

def prod_diag {n:ℕ} (F: fin n → nnreal → nnreal) : vector nnreal n → nnreal :=
λ (x: vector nnreal n), (diag F x).prod

lemma mem_list {U:Type} {n:ℕ} (G : fin n → U ) (z:U) :
  z ∈ list.of_fn (λ j : fin n, G j) → ∃ j, G j = z:=
  λ hz, 
  have z ∈ set.range (λ j : fin n, G j), from  (list.mem_of_fn _ _).mp hz,
  set.mem_range.mp this

theorem exercise_6_2 {n:ℕ} (F: fin n → nnreal → nnreal) (c : vector nnreal n)
(h : ∀ i, ∀ y, F i y ≤ F i (c.nth i))
: ∀ x, prod_diag F x ≤ prod_diag F c
:= λ x,
  have h_easy: ∀ i, ∀ x : vector nnreal n, F i (x.nth i)≤ F i (c.nth i), from
    λ i x, h i (x.nth i),

  have dominates (list.of_fn (
    λ j : fin n,
    (F j (x.nth j), F j (c.nth j))
  )), from λ z,
    have hex:
      z ∈ list.of_fn (λ (j : fin n), (F j (vector.nth x j), F j (c.nth j)))
      →
      ∃ j, (F j (vector.nth x j), F j (c.nth j)) = z, from (mem_list _ _),
    λ hz,
    have ∃ j, (F j (vector.nth x j), F j (c.nth j)) = z, from hex hz,
    exists.elim this (
      λ j hj, calc z.1 = F j (vector.nth x j): (congr_arg prod.fst hj.symm).trans rfl
                  ...  ≤ F j (vector.nth c j): h_easy j x
                  ... = z.2: ((congr_arg prod.snd (eq.symm hj)).congr_right.mp rfl).symm
    ),-- from h_easy

let a:= (list.of_fn (
    λ j : fin n,
    (F j (x.nth j), F j (c.nth j))
  )) in
have hp : (p1 a).prod ≤ (p2 a).prod, from exercise_6_1 _ this,

have hp1a: p1 a = (list.of_fn (
    λ j : fin n,
    (F j (x.nth j))
  )), from p1_list_of_fn _ _, -- probably have to prove from def. of a by list.rec_on

have hp2a: p2 a = (list.of_fn (
    λ j : fin n,
    (F j (c.nth j))
  )), from p2_list_of_fn _ _, -- probably have to prove by list.rec_on

have (list.of_fn (λ i : fin n, F i (x.nth i))).prod
          ≤ (list.of_fn (λ i : fin n, F i (c.nth i))).prod, from calc
        _ = (p1 a).prod: by rw hp1a
      ... ≤ (p2 a).prod: hp
      ... = _: by rw hp2a,

calc _ = (diag F x).prod : rfl
          ... = (list.of_fn (λ i : fin n, F i (x.nth i))).prod: rfl
          ... ≤ (list.of_fn (λ i : fin n, F i (c.nth i))).prod: this
          ... = (diag F c).prod : rfl
          ... = prod_diag F c: rfl
