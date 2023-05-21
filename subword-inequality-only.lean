import tactic.derive_fintype
import computability.DFA
import data.set.basic
import data.set.finite

constant alpha:ℕ
def α := fin alpha -- α is the input alphabet

/-
NA = Nondeterministic automaton
NA' = NA with a single start state and a single accept state.
For automatic complexity we are more interested in NA' than in NA, to simplify proofs
-/

structure NA' (α : Type ) (σ : Type ) :=
mk :: (step : σ → α → set σ) (start :  σ) (accept :  σ)


namespace NA'
  variables  {σ  : Type } (M : NA' α σ)
  instance [inhabited σ]: inhabited (NA' α σ) := ⟨ NA'.mk (λ _ _, ∅) default default ⟩
  
  def step_set (S : set σ) (a : α) : set σ := ⋃ s ∈ S, M.step s a

  def eval_from (start : set σ) : list α → set σ :=
  list.foldl M.step_set start

  def eval : list α → set σ := M.eval_from {M.start}

  def accepts : language α := λ x, M.accept ∈ M.eval x

  lemma step_set_empty {a : α} : M.step_set ∅ a = ∅ :=
  by simp_rw [step_set, set.Union_false, set.Union_empty]

  end NA'

namespace eval

  theorem from_empty {σ:Type} (M: NA' α σ) (y:list α):
    M.eval_from ∅ y = ∅ :=
    list.rec_on y rfl (
      λ hd tl h,
      have h0: M.step_set ∅ hd = ∅, from M.step_set_empty,
      calc
      M.eval_from ∅ (hd :: tl) = M.eval_from (M.step_set ∅ hd) tl: rfl
                          ... = M.eval_from (∅) tl: by rw h0
                          ... = ∅:h
    )

  theorem eval_from_subset {γ: Type } (M: NA' α γ) (w: list α):
    ∀ (S T : set γ), S ⊆ T → M.eval_from S w ⊆ M.eval_from T w :=
    list.rec_on w -- important to have ∀ S T as part of the induction hypothesis
    (λ _ _ h, h) (
      λ b _ h_ind S T hST _ hq,
      have hs: M.step_set S b ⊆ M.step_set T b, from set.bUnion_subset_bUnion_left hST,
      (h_ind (M.step_set S b) (M.step_set T b) hs) hq
    )

  theorem step_singleton {σ:Type} (M:NA' α σ) (q:σ)(a:α):
    M.step_set {q} a = M.step q a  :=
    set.bUnion_singleton q (λ q, M.step q a)

  lemma eval_from_set_cons {σ:Type} {M:NA' α σ} {q:σ} {y:list α} {F: set σ} {a:α}
    (h_given: ∃ r : σ, r ∈ (M.step_set F a) ∧ q ∈ M.eval_from {r} y)
            : ∃ s : σ, s ∈ F                ∧ q ∈ M.eval_from {s} (a::y)
    :=   
    let G := (M.step_set F a) in
    exists.elim h_given (λ r, λ hr: r ∈ G ∧ q ∈ M.eval_from {r} y,
        have ∃ (s:σ) (H:s ∈ F), r ∈ (M.step s a), from set.mem_Union₂.mp hr.1,
        have h0: ∃ s:σ, s ∈ F ∧ r ∈ (M.step_set {s} a), from
          exists.elim this (
            λ s, λ hs: ∃(H:s ∈ F), r ∈ (M.step s a), exists.elim hs (λ H, λ hrM: r ∈ M.step s a,
              exists.intro s (and.intro H (by {rw ← (step_singleton M s a) at hrM,exact hrM,}))
            )
          ),
        exists.elim h0 (
          λ s, λ hs : s ∈ F ∧ r ∈ (M.step_set {s} a),
          exists.intro s (and.intro hs.1 (
            have h3: {r} ⊆ M.step_set {s} a, from set.singleton_subset_iff.mpr hs.2,
            show     q ∈ M.eval_from (M.step_set {s} a) y, from
            (eval_from_subset M y {r} (M.step_set {s} a) h3) hr.2
          ))
        )
      )

  lemma singleton_member_of_set {σ:Type} {M:NA' α σ} {q:σ} {l:list α}:
    ∀ F:set σ, (     q ∈ M.eval_from F   l 
    → ∃ r:σ, r ∈ F ∧ q ∈ M.eval_from {r} l) :=
    list.rec_on l (
      λ F hq, exists.intro q (and.intro hq (set.mem_singleton q))
    ) (
      λ a y h_ind F,
      let G := (M.step_set F a) in
      λ hyp : q ∈ M.eval_from G y, eval_from_set_cons (h_ind G hyp)
    )

  lemma set_of_singleton_member {σ:Type} {M:NA' α σ} {q:σ} {l:list α} {F:set σ}
    (hsome: ∃ r:σ, r ∈ F ∧ q ∈ M.eval_from {r} l) :
                           q ∈ M.eval_from F l :=
    exists.elim hsome (
      λ r, λ hr:r ∈ F ∧ q ∈ M.eval_from {r} l,
      have h1: {r} ⊆ F, from set.singleton_subset_iff.mpr hr.1,
      (eval_from_subset M l {r} F h1) hr.2
    )
  theorem set_iff_singleton_member {σ:Type} {M:NA' α σ} {q:σ} {l:list α} (F:set σ):
    q ∈ M.eval_from F l ↔ ∃ r:σ, r ∈ F ∧ q ∈ M.eval_from {r} l :=
    iff.intro (singleton_member_of_set F) set_of_singleton_member

end eval

instance my_sum_inst {δ : Type} (u : fintype δ) : fintype (unit ⊕ δ) :=
  sum.fintype unit δ

namespace hd -- head_concat_automaton
  def trafo {δ:Type} (u:fintype δ) (N: NA' α δ) (a:α): NA' α (unit ⊕ δ) := -- transformation of NA's
    let sum_inr := (λ x:δ, ((sum.inr x): unit ⊕ δ)) in
    NA'.mk 
      (λ state b, sum.cases_on state
        (λ _, ite (a=b) {sum.inr N.start} {})
        (λ q, sum_inr '' (N.step q b))
      )
      (sum.inl unit.star) (sum.inr N.accept)

-- 1
theorem lift_to {δ:Type} [u:fintype δ] {N: NA' α δ} {a:α} {t:list α}:
  let M := (trafo u N a) in
  ∀ q1 q2 : δ, q2 ∈ N.eval_from {q1}         t →
       sum.inr q2 ∈ M.eval_from {sum.inr q1} t :=

  let M := (trafo u N a) in
  let sum_inr := (λ x:δ, ((sum.inr x): unit ⊕ δ)) in
  list.rec_on t (λ _ _ h, congr_arg sum.inr h) (
  λ b s h_ind q1 q2 hyp,
  let Ns := (N.step q1 b), Nss := (N.step_set {q1} b), Mef := M.eval_from in

  have hyp': ∃ q1', q1' ∈  Nss ∧ q2 ∈ N.eval_from {q1'} s, from (eval.singleton_member_of_set Nss) hyp,
  have h_ex: ∃ q1', q1' ∈ (sum_inr '' Ns) ∧ sum.inr q2 ∈ Mef {q1'} s, from
    exists.elim hyp'
    (λ q1', λ hq1': q1' ∈ N.step_set {q1} b ∧ q2 ∈ N.eval_from {q1'} s,
    exists.intro (sum.inr q1') (
      and.intro (
        set.mem_image_of_mem sum_inr (by {cases hq1' with h_1 h_2,rw eval.step_singleton at h_1,exact h_1,})
      ) (h_ind q1' q2 hq1'.2)
    )),
  
  have h_in: sum.inr q2 ∈ Mef (sum_inr '' Ns) s, from eval.set_of_singleton_member h_ex,
  have h_step:(M.step_set {sum.inr q1} b) = sum_inr '' Ns, from eval.step_singleton M (sum.inr q1) b,
  by {rw ← h_step at h_in,exact h_in,}
  )

-- 2
  theorem accept_self {δ:Type} [u:fintype δ] {N: NA' α δ} {a:α} {t:list α}:
    N.accepts t → (trafo u N a).accepts (a::t) :=
    λ hNt,
    let M := (trafo u N a), start := ({sum.inr N.start}: set (unit ⊕ δ)) in
    have h0: M.step_set {M.start} a = start, from calc
                                  _ = M.step M.start a : eval.step_singleton M M.start a
                                ... = _                : if_pos rfl,

    have h1: M.accept ∈ list.foldl M.step_set start t, from (lift_to N.start N.accept) hNt,
    by {rw ← h0 at h1,exact h1,}


-- 3
  theorem stay_old      {δ:Type} [u:fintype δ] {N: NA' α δ} {a b:α} {q:δ} {q':unit⊕δ}:
  let M := (trafo u N a) in
  q' ∈ M.step_set {sum.inr q} b → ∃ q_, q' = sum.inr q_ :=
  let M := (trafo u N a) in

  sum.cases_on q' -- q' is either inl or inr
  (
    let sum_inr := (λ x:δ, ((sum.inr x): unit ⊕ δ)) in
    λ val h,
    have h2: sum.inl val ∈ sum_inr '' (N.step q b), by {rw eval.step_singleton at h,exact h,},
    exists.elim (
      (set.mem_image sum_inr (N.step q b) (sum.inl val)).mp h2
    ) (
      λ _ hqq, false.elim (sum.inr_ne_inl hqq.2)
    )
  ) (λ val _, exists.intro val rfl)

-- 4
  theorem remove_step   {δ:Type} [u:fintype δ] {N: NA' α δ} {q q_:δ} {a b:α}
  (hq1: ((sum.inr q_):unit ⊕ δ) ∈ (trafo u N a).step_set {sum.inr q} b):
                  q_            ∈            N   .step_set (       {q}:set δ) b
  :=
  let sum_inr := (λ x:δ, ((sum.inr x): unit ⊕ δ)) in
  have h: sum.inr q_ ∈ sum_inr '' (N.step q b), by {rw eval.step_singleton at hq1,exact hq1,},
  have h_eq: ∃ x, x ∈ N.step q b ∧ sum.inr x = sum_inr q_, from
    (set.mem_image sum_inr (N.step q b) (sum.inr q_)).mp h ,
  have h_step: q_ ∈ N.step q b, from
    exists.elim h_eq (λ _ hr_, eq.subst (sum.inr_injective hr_.2) hr_.1),
  by {rw ← eval.step_singleton at h_step,exact h_step,}

-- 5
theorem remove_accept {δ:Type} [u:fintype δ] {N: NA' α δ} {q:δ} {a b:α} {z:list α}:
  let M:= (trafo u N a) in
    (∃ q',         q' ∈ M.step_set {sum.inr q}                  b ∧ M.accept ∈ M.eval_from {q'} z)
  → (∃ q_, sum.inr q_ ∈ M.step_set ({sum.inr q}:set (unit ⊕ δ)) b ∧ M.accept ∈ M.eval_from {sum.inr q_} z)
  :=
  λ hyp', exists.elim hyp' (
    λ q' hq',
    exists.elim (stay_old  hq'.1) (
      λ q_, λ hq_,
      exists.intro q_ (
        by {rw hq_ at hq',exact hq',}
      )
    )
  )

-- 6
theorem remove        {δ:Type} [u:fintype δ] {N: NA' α δ} {a:α} {y:list α}:
  let M := (trafo u N a) in
  ∀ q:δ,
  M.accept ∈ M.eval_from (({sum.inr q}):set (unit ⊕ δ)) y → 
  N.accept ∈ N.eval_from           {q}             y
  :=
  list.rec_on y (
    λ _, λ h, sum.inr_injective h
  ) (
    λ b z h_ind q hyp,
    let M := (trafo u N a) in
    have hyp': ∃ q', q' ∈ M.step_set {sum.inr q} b ∧ M.accept ∈ M.eval_from {q'} z, from
      (eval.singleton_member_of_set (M.step_set {sum.inr q} b)) hyp,
    exists.elim (remove_accept hyp') (
      λ q_ hq_,
      have h_step_set:        q_ ∈ N.step_set ({q}:set δ) b, from remove_step hq_.1,
      have h_eval:      N.accept ∈ N.eval_from {q_} z,       from h_ind q_ hq_.2,
      (eval.set_iff_singleton_member (N.step_set {q} b)).mpr (exists.intro q_ (and.intro h_step_set h_eval))
    )
  )

-- 7
theorem accepts_only          {δ:Type} [u:fintype δ] {N: NA' α δ} {a:α} {t:list α}:
  (trafo u N a).accepts t → ∃ s:list α, t = a :: s ∧ N.accepts s :=
  let M := (trafo u N a) in
  list.cases_on t (
    λ h, false.elim (sum.inl_ne_inr (set.mem_singleton_iff.mp h).symm)
  ) (
    λ b y,
    λ h:        M.accept ∈ M.eval_from (M.step_set  {M.start} b) y,
    have h_ite: M.accept ∈ M.eval_from (ite (a=b){sum.inr N.start} {}) y, from
      by {rw eval.step_singleton at h,exact h,},
    have h_:    M.accept ∈ M.eval_from (M.step       M.start  b) y, from h_ite,
    have hab: a = b, from by_contra (
      λ hnot,
      have h0 : ite (a=b) ({sum.inr N.start}: set (unit ⊕ δ)) {} = {}, by {refine if_neg hnot,},
      set.not_mem_empty M.accept (eq.subst (eval.from_empty M y) (eq.subst h0 h_ite))
    ),
    have h01: M.step M.start b = {sum.inr N.start},         by {refine if_pos hab,},
    have h02: M.accept ∈ M.eval_from ({sum.inr N.start}) y, by {rw h01 at h_,exact h_,},
    have h2: N.accepts y, from (remove N.start) h02,
    exists.intro y (and.intro (congr_arg _ hab.symm) h2)
  )

-- 8
theorem regex         {δ:Type} {u:fintype δ} {N: NA' α δ} {a:α}:
  ∀ t:list α,
  (trafo u N a).accepts t ↔ ∃ s:list α, t = a :: s ∧ N.accepts s :=

  λ t,
  iff.intro                                            accepts_only
  (λ hex, exists.elim hex (λ _ hs, eq.subst hs.1.symm (accept_self hs.2)))

end hd --head_concat_automaton

notation `!`a`!` := a.length


def accepts_exactly {δ:Type} (M:NA' α δ) (x:list α) : Prop :=
  ∀ y: list α, !y! = !x! → (M.accepts y ↔ y = x)

def A_N_word_bounded_by (x: list α) (n:ℕ) :=
  ∃ δ:Type, ∃ u: fintype δ, u.elems.card ≤ n ∧ ∃ M: NA' α δ,
  accepts_exactly M x

theorem A_N_word_finite_prelim (x:list α) :
  ∃ δ:Type, ∃ u: fintype δ, ∃ M: NA' α δ,
  accepts_exactly M x :=

  let M1 := NA'.mk (λ q:unit, λ b:α, {}) unit.star unit.star in

  list.rec_on x (
    exists.intro (unit) (exists.intro (unit.fintype) (exists.intro (M1) (
      λ y, λ h:y.length = list.nil.length,
      have h0: y = list.nil, from list.eq_nil_of_length_eq_zero h,
      have h1: M1.accepts list.nil, from rfl,
      by cc          
    )))
  )
  (
    λ a:α,λ y:list α,
    λ h_ind: ∃ (δ : Type) (u : fintype δ) (N : NA' α δ),
            ∀ (s : list α), s.length = y.length → (N.accepts s ↔ s = y),
    exists.elim h_ind
    (
      λ δ hδ,
      exists.elim hδ (
        λ u hu,
        exists.elim hu (
          λ N, λ hN: ∀ (s : list α), s.length = y.length → (N.accepts s ↔ s = y),
          let M := (hd.trafo u N a) in -- !!!
          exists.intro (unit ⊕ δ) (exists.intro (my_sum_inst u) (exists.intro M (
            λ z hz,
            iff.intro (
              λ hM,
              have ∃ s:list α, z = a :: s ∧ N.accepts s, from (hd.regex z).mp hM,
              exists.elim this (
                λ s hs,
                have (a::s).length = (a::y).length, from calc
                                 _ = z.length: (congr_arg _ hs.1).symm
                               ... = _ : hz,
                have s.length = y.length, from nat.succ_inj'.mp this,
                have s = y, from (hN s this).mp hs.2,
                hs.1.trans (congr_arg _ this)
              )
            ) (
              λ hza,
              have ∃ s:list α, z = a :: s ∧ N.accepts s, from
                exists.intro y (and.intro hza
                ((hN y rfl).mpr rfl)
                ),
              (hd.regex z).mpr this
            )
          )))
        )
      )
    )
  )

theorem A_N_word_finite : ∀ x:list α, ∃ n:ℕ, A_N_word_bounded_by x n :=
  λ x,
  exists.elim (A_N_word_finite_prelim x) (
    λ δ hδ, exists.elim hδ (
      λ u hu, exists.elim hu (
        λ M hM, exists.elim (
          exists.intro δ (
            exists.intro u (
              exists.intro M hM
            )
          )
        ) (
          λ δ hδ, exists.elim hδ (
            λ u hu, exists.elim hu (
              λ M hM, exists.intro u.elems.card (
                exists.intro δ (
                  exists.intro u (
                    and.intro (le_refl u.elems.card) (exists.intro M (hM))
                  )
                )
              )
            )
          )
        )
      )
    )
  )
open_locale classical

noncomputable def A_N_word : list α → ℕ :=
  λ x,
  nat.find_x (A_N_word_finite x) -- word-counting nondeterministic complexity
-- find and find_x both work

theorem fintype_card_sum_typesafe {δ:Type} {u:fintype δ}:
  (my_sum_inst u).elems.card = fintype.card(unit) + u.elems.card:= fintype.card_sum


theorem autocomplex_bound_nil :
  ∃ δ:Type, ∃ u: fintype δ, u.elems.card ≤ (list.nil : list α).length.succ ∧ ∃ M: NA' α δ, 
  accepts_exactly M list.nil :=
  let q0 := (⟨0,zero_lt_one⟩:fin 1), M1:=NA'.mk (λ q:fin 1, λ b:α, {}) q0 q0 in
   (
    exists.intro (fin 1) (
      exists.intro (fin.fintype 1) (
        and.intro (le_refl 1) (
          exists.intro M1 (
            λ y h,
            have h0: y = list.nil, from list.eq_nil_of_length_eq_zero h,
            have h1: M1.accepts list.nil, from rfl,
            by cc
          )
        )
      )
    )
  )

theorem A_N_word_nil_bound_length_succ : A_N_word list.nil ≤ 1 :=
  nat.find_min'
  ((A_N_word_finite list.nil):∃ n:ℕ, A_N_word_bounded_by list.nil n)
  (autocomplex_bound_nil)

theorem nonempty_of_mem {α : Type} {a:α} {s: finset α} : a ∈ s → s.nonempty :=
λ h, finset.nonempty_of_ne_empty (finset.ne_empty_of_mem h)

theorem lower_bound (x:list α): 1 ≤ A_N_word x :=
  have h1: (nat.find (A_N_word_finite x)) ≠ 0, from
    have A_N_word_bounded_by x (nat.find _), from (nat.find_x (A_N_word_finite x)).2.1,
    λ h : (nat.find _) = 0,
    have A_N_word_bounded_by x 0, by {rw h at this,exact this,},
    exists.elim this (
      λ _ hδ, exists.elim hδ (
        λ u hu,
        exists.elim hu.2 (
          λ M _, 
          lt_irrefl 0 (
            calc 0 < u.elems.card: finset.card_pos.mpr (nonempty_of_mem (u.complete M.start))
               ... ≤ 0: hu.1)
        )
      )
    ),
  nat.one_le_iff_ne_zero.mpr h1

theorem A_N_word_nil : A_N_word list.nil = 1 :=
  antisymm A_N_word_nil_bound_length_succ (lower_bound list.nil)


-- May 20, 2023:
theorem accepts_exactly_hd {δ:Type} (N : NA' α δ) (y : list α) (a:α) (u: fintype δ)
  (hae: accepts_exactly N       y): let M := (hd.trafo u N a) in
        accepts_exactly M (a :: y) :=
  let M := (hd.trafo u N a) in

  have hN: ∀ (s : list α), s.length = y.length → (N.accepts s ↔ s = y), from hae,

  show ∀ z: list α, z.length = (a :: y).length → (M.accepts z ↔ z = a :: y), from
  λ z hz, iff.intro (
    λ hM,
    have ∃ s:list α, z = a :: s ∧ N.accepts s, from (hd.regex z).mp hM,
    exists.elim this (
      λ s hs,
      have (a::s).length = (a::y).length, from calc
                      _ = z.length: (congr_arg _ hs.1).symm
                    ... = _ : hz,
      have s.length = y.length, from nat.succ_inj'.mp this,
      have s = y, from (hN s this).mp hs.2,
      hs.1.trans (congr_arg _ this)
    )
  ) (
    λ hza,
    have ∃ s:list α, z = a :: s ∧ N.accepts s, from
      exists.intro y (and.intro hza
      ((hN y rfl).mpr rfl)
      ),
    (hd.regex z).mpr this
  )

theorem hd_card (δ:Type) (u: fintype δ):
(fintype.elems (unit ⊕ δ)).card =
(fintype.elems (       δ)).card.succ

:=

 calc
    _ = fintype.card(unit) + u.elems.card: fintype_card_sum_typesafe
  ... = 1                  + u.elems.card: congr_arg _ rfl
  ... = u.elems.card       + 1           : add_comm _ _
  ... = u.elems.card.succ                : nat.succ_eq_add_one _

theorem hd_card_my (δ:Type) : ∀ u : fintype δ,
(my_sum_inst u).elems.card = u.elems.card.succ := λ u, hd_card δ u

theorem iterative_bound (x:list α) (a:α): -- May 21, 2023
  A_N_word (a::x) ≤ (A_N_word x).succ :=

  have A_N_word_bounded_by x (nat.find_x (A_N_word_finite x)), from nat.find_spec _,
  exists.elim this (
    λ δ hδ, exists.elim hδ (
      λ u hu, exists.elim hu.2 (
        λ N hN, let M := (hd.trafo u N a) in
          have ha: accepts_exactly M (a :: x), from accepts_exactly_hd N x a u hN,

          have hc: (my_sum_inst u).elems.card ≤ (A_N_word x).succ, from  calc
                   (my_sum_inst u).elems.card = u.elems.card.succ: hd_card_my δ u
                                          ... ≤ (A_N_word x).succ: nat.succ_le_succ hu.1,
          have A_N_word_bounded_by (a::x) (A_N_word x).succ, from
          exists.intro (unit⊕δ) (exists.intro (my_sum_inst u) (and.intro hc (exists.intro M ha))),
          nat.find_min' (A_N_word_finite (a::x)) this
      )
    )
  )

theorem subword_inequality (x y : list α) : A_N_word (x ++ y) ≤ x.length + A_N_word y :=
list.rec_on x (
  calc _ = A_N_word y     : rfl
     ... = 0 + A_N_word y : by rw zero_add
     ... ≤  _             : le_refl _
) (
  λ hd tl, λ h_ind : A_N_word (tl ++ y) ≤ list.length tl + A_N_word y,
show A_N_word (hd :: tl ++ y) ≤ (hd :: tl).length + A_N_word y, from
calc
A_N_word (hd :: tl ++ y) ≤ (A_N_word (tl ++ y)).succ      : iterative_bound _ _
                     ... ≤ (tl.length + A_N_word y).succ  : nat.succ_le_succ h_ind
                     ... = tl.length.succ + A_N_word y    : by rw nat.succ_add
                     ... = (hd :: tl).length + A_N_word y : rfl
)

theorem A_N_word_bound_length_succ' (x:list α): A_N_word x ≤ x.length.succ :=
calc A_N_word x = A_N_word (x ++ list.nil)    : by rw (list.append_nil x)
            ... ≤ x.length + A_N_word list.nil: subword_inequality _ _
            ... ≤ x.length + 1                : add_le_add_left A_N_word_nil_bound_length_succ _
            ... = x.length.succ               : rfl 
