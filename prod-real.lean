import data.list.big_operators.basic
import data.real.basic

/-

Let a1,...,ak,b1,...,bk ≥ 0 be real numbers such that for each 1≤i≤k, ai ≤bi. Then
∏^k_{i=1}ai ≤∏^k_{i=1}b_i.

To to do the inductive step we need list.rec_on and hence projections p1 and p2.
However, def nonnegative below shows a better way of working with lists in some ways.
-/

def nonnegative  (a : list (ℝ)): Prop := ∀ i ∈ a, (0  :ℝ) ≤ i
def dominates (a : list (ℝ×ℝ)) : Prop := ∀ i ∈ a, (i.1:ℝ) ≤ i.2

lemma prod_nonneg (tl : list ℝ): nonnegative tl  → 0 ≤ tl.prod :=
 list.rec_on tl (λh,  zero_le_one) (
  λ hd tl_1 h_ind hyp,
  have h1: hd ∈ hd :: tl_1, from list.mem_cons_self hd tl_1,
  have h2: 0 ≤hd, from hyp hd h1,
  have h3: ∀ (x : ℝ), x ∈ tl_1 → 0 ≤ x, from
    λ x hx, hyp _ (list.mem_cons_of_mem hd hx),
  have h4: 0 ≤ tl_1.prod, from h_ind h3,
  have h5: 0 ≤hd * tl_1.prod, from mul_nonneg h2 h4,
  calc 0 ≤  hd *   tl_1.prod: h5
     ... = (hd :: tl_1).prod: list.prod_cons.symm
)

lemma nonn_tl  (tl: list ℝ) : ∀ (hd:ℝ), nonnegative (hd::tl) → nonnegative tl :=
  λ hd hn, list.forall_mem_of_forall_mem_cons hn

lemma nonn_hd  {tl: list ℝ} {hd:ℝ}: nonnegative (hd::tl) → 0 ≤ hd :=
  λ hn, (list.forall_mem_cons.mp hn).1

lemma dom_cons (hd : ℝ×ℝ) (tl: list (ℝ×ℝ)): dominates (hd:: tl) → dominates tl :=
  λ h i hi,
  have i ∈ hd :: tl, from list.mem_cons_of_mem hd hi,
  h i this

def p1 {U:Type}: list (U×U) → list(U) :=
  λ l, list.rec_on l list.nil (λ a _ p_ind, a.1 :: p_ind)
def p2 {U:Type}: list (U×U) → list(U) :=
  λ l, list.rec_on l list.nil (λ a _ p_ind, a.2 :: p_ind)


theorem lemma_6_16 (a : list (ℝ×ℝ)) :
  nonnegative (p1 a) →
  nonnegative (p2 a) →
  dominates (a) →
  (p1 a).prod ≤ (p2 a).prod
  :=
  list.rec_on a (
    λ hn1 hn2 hd,  
      le_refl _ 
  ) (
    λ hd tl h_ind hn1 hn2 hdom,
    have hh: 0≤hd.2, from nonn_hd hn2,
    have hhh: hd.1 ≤ hd.2, from hdom hd (list.mem_cons_self hd tl),
    have hhh1: nonnegative (p1 tl), from nonn_tl _ hd.1 hn1,
    have hhh2: nonnegative (p2 tl), from nonn_tl _ hd.2 hn2,
    have H: 0 ≤ (p1 tl).prod, from prod_nonneg _ hhh1,
    have hp: (p1 tl).prod ≤ (p2 tl).prod, from
      h_ind hhh1 hhh2 (dom_cons hd tl hdom),
    calc
      (p1 (hd :: tl)).prod = hd.1   *  (p1 tl).prod : list.prod_cons
                       ... ≤ hd.2   *  (p1 tl).prod : mul_le_mul_of_nonneg_right hhh H
                       ... ≤ hd.2   *  (p2 tl).prod : mul_le_mul_of_nonneg_left  hp  hh 
                       ... = (hd.2 :: (p2 tl)).prod : list.prod_cons.symm
  )
