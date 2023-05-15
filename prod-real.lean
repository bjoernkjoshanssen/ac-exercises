import data.real.nnreal
/-

Let a1,...,ak,b1,...,bk ≥ 0 be real numbers such that for each 1≤i≤k, ai ≤bi. Then
∏^k_{i=1}ai ≤∏^k_{i=1}b_i.

To to do the inductive step we need list.rec_on and hence projections p1 and p2.
However, def dominates below shows a better way of working with lists in some ways.
-/

def dominates (a : list (nnreal×nnreal)) : Prop := ∀ i ∈ a, (i.1:nnreal) ≤ i.2

lemma dom_cons (hd : nnreal×nnreal) (tl: list (nnreal×nnreal)): dominates (hd:: tl) → dominates tl :=
  λ h i hi,
  have i ∈ hd :: tl, from list.mem_cons_of_mem hd hi,
  h i this

def p1 {U:Type}: list (U×U) → list(U) :=
  λ l, list.rec_on l list.nil (λ a _ p_ind, a.1 :: p_ind)
def p2 {U:Type}: list (U×U) → list(U) :=
  λ l, list.rec_on l list.nil (λ a _ p_ind, a.2 :: p_ind)

theorem six_16_nnreal (a : list (nnreal×nnreal)) :
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
