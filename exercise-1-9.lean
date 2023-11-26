import Mathlib.Computability.DFA
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Sum
import Mathlib.Init.Data.Nat.Lemmas

-- Solution to Exercise 1.9.

axiom alpha:ℕ
-- def α := Fin alpha -- (Fin alpha) is the input alphabet

/-
NA = Nondeterministic automaton
NA' = NA with a single start state and a single accept state.
For automatic complexity we are more interested in NA' than in NA, to simplify proofs
-/

structure NA' (α : Type ) (σ : Type ) :=
mk :: (step : σ → α → Set σ) (start :  σ) (accept :  σ)


namespace NA'
  variable  {σ  : Type } (M : NA' (Fin alpha) σ)
  instance [Inhabited σ]: Inhabited (NA' (Fin alpha) σ) := ⟨ NA'.mk (λ _ _ ↦ ∅) default default ⟩

  def step_set (S : Set σ) (a : (Fin alpha)) : Set σ := ⋃ s ∈ S, M.step s a

  def eval_from (start : Set σ) : List (Fin alpha) → Set σ :=
  List.foldl M.step_set start

  def eval : List (Fin alpha) → Set σ := M.eval_from {M.start}

  def accepts : Language (Fin alpha) := λ x ↦ M.accept ∈ M.eval x

  lemma step_set_empty {a : (Fin alpha)} : M.step_set ∅ a = ∅ :=
  by {
    rw [step_set]
    exact Set.biUnion_empty fun x ↦ step M x a
  }


  end NA'

namespace eval

  theorem from_empty {σ:Type} (M: NA' (Fin alpha) σ) (y:List (Fin alpha)):
    M.eval_from ∅ y = ∅ :=
    List.recOn y rfl (
      λ hd tl h ↦
      have h0: M.step_set ∅ hd = ∅ := M.step_set_empty
      calc
      M.eval_from ∅ (hd :: tl) = M.eval_from (M.step_set ∅ hd) tl := rfl
      _ = M.eval_from (∅) tl := by rw [h0]
      _ = ∅ := h
    )

  theorem eval_from_subset {γ: Type } (M: NA' (Fin alpha) γ) (w: List (Fin alpha)):
    ∀ (S T : Set γ), S ⊆ T → M.eval_from S w ⊆ M.eval_from T w :=
    List.recOn w -- important to have ∀ S T as part of the induction hypothesis
    (λ _ _ h ↦ h) (
      λ b _ h_ind S T hST _ hq ↦
      have hs: M.step_set S b ⊆ M.step_set T b := by {
        exact Set.biUnion_subset_biUnion_left hST
      }
      (h_ind (M.step_set S b) (M.step_set T b) hs) hq
    )

  theorem step_singleton {σ:Type} (M:NA' (Fin alpha) σ) (q:σ)(a:(Fin alpha)):
    M.step_set {q} a = M.step q a  :=
    Set.biUnion_singleton q (λ q ↦ M.step q a)

  lemma eval_from_set_cons {σ:Type} {M:NA' (Fin alpha) σ} {q:σ} {y:List (Fin alpha)} {F: Set σ} {a:(Fin alpha)}
    (h_given: ∃ r : σ, r ∈ (M.step_set F a) ∧ q ∈ M.eval_from {r} y)
            : ∃ s : σ, s ∈ F                ∧ q ∈ M.eval_from {s} (a::y)
    :=
    let G := (M.step_set F a)
    Exists.elim h_given (λ r ↦ λ hr: r ∈ G ∧ q ∈ M.eval_from {r} y ↦
        have : ∃ (s:σ) (_:s ∈ F), r ∈ (M.step s a) := Set.mem_iUnion₂.mp hr.1
        have h0: ∃ s:σ, s ∈ F ∧ r ∈ (M.step_set {s} a) :=
          Exists.elim this (
            λ s ↦ λ hs: ∃(_:s ∈ F), r ∈ (M.step s a) ↦ Exists.elim hs (λ H ↦ λ hrM: r ∈ M.step s a ↦
              Exists.intro s (And.intro H (by {rw [← (step_singleton M s a)] at hrM;exact hrM}))
            )
          )
        Exists.elim h0 (
          λ s ↦ λ hs : s ∈ F ∧ r ∈ (M.step_set {s} a) ↦
          Exists.intro s (And.intro hs.1 (
            have h3: {r} ⊆ M.step_set {s} a := Set.singleton_subset_iff.mpr hs.2
            show     q ∈ M.eval_from (M.step_set {s} a) y from
            (eval_from_subset M y {r} (M.step_set {s} a) h3) hr.2
          ))
        )
      )

  lemma singleton_member_of_set {σ:Type} {M:NA' (Fin alpha) σ} {q:σ} {l:List (Fin alpha)}:
    ∀ F:Set σ, (     q ∈ M.eval_from F   l
    → ∃ r:σ, r ∈ F ∧ q ∈ M.eval_from {r} l) :=
    List.recOn l (
      λ _ hq ↦ Exists.intro q (And.intro hq (Set.mem_singleton q))
    ) (
      λ a y h_ind F ↦
      let G := (M.step_set F a)
      λ hyp : q ∈ M.eval_from G y ↦ eval_from_set_cons (h_ind G hyp)
    )

  lemma set_of_singleton_member {σ:Type} {M:NA' (Fin alpha) σ} {q:σ} {l:List (Fin alpha)} {F:Set σ}
    (hsome: ∃ r:σ, r ∈ F ∧ q ∈ M.eval_from {r} l) :
                           q ∈ M.eval_from F l :=
    Exists.elim hsome (
      λ r ↦ λ hr:r ∈ F ∧ q ∈ M.eval_from {r} l ↦
      have h1: {r} ⊆ F := Set.singleton_subset_iff.mpr hr.1
      (eval_from_subset M l {r} F h1) hr.2
    )
  theorem set_iff_singleton_member {σ:Type} {M:NA' (Fin alpha) σ} {q:σ} {l:List (Fin alpha)} (F:Set σ):
    q ∈ M.eval_from F l ↔ ∃ r:σ, r ∈ F ∧ q ∈ M.eval_from {r} l :=
    Iff.intro (singleton_member_of_set F) set_of_singleton_member

end eval

instance my_sum_inst {δ : Type} (u : Fintype δ) : Fintype (Unit ⊕ δ) :=
  by exact instFintypeSum Unit δ

noncomputable instance (a b : (Fin alpha)):
  Decidable (a = b) := by exact Classical.dec (a = b)

namespace hd -- head_concat_automaton
  def trafo {δ:Type} (_:Fintype δ) (N: NA' (Fin alpha) δ) (a:(Fin alpha)): NA' (Fin alpha) (Unit ⊕ δ) := -- transformation of NA's
    let sum_inr := (λ x:δ ↦ ((Sum.inr x): Unit ⊕ δ))
    NA'.mk
      (λ state b ↦ Sum.casesOn state
        (λ _ ↦ ite (a=b) {Sum.inr N.start} {})
        (λ q ↦ sum_inr '' (N.step q b))
      )
      (Sum.inl Unit.unit) (Sum.inr N.accept)

-- 1
theorem lift_to {δ:Type} [u:Fintype δ] {N: NA' (Fin alpha) δ} {a:(Fin alpha)} {t:List (Fin alpha)}:
  let M := (trafo u N a)
  ∀ q1 q2 : δ, q2 ∈ N.eval_from {q1}         t →
       Sum.inr q2 ∈ M.eval_from {Sum.inr q1} t :=

  let M := (trafo u N a)
  let sum_inr := (λ x:δ ↦ ((Sum.inr x): Unit ⊕ δ))
  List.recOn t (λ _ _ h ↦ congr_arg Sum.inr h) (
  λ b s h_ind q1 q2 hyp ↦
  let Ns := (N.step q1 b)
  let Nss := (N.step_set {q1} b)
  let Mef := M.eval_from

  have hyp': ∃ q1', q1' ∈  Nss ∧ q2 ∈ N.eval_from {q1'} s := (eval.singleton_member_of_set Nss) hyp
  have h_ex: ∃ q1', q1' ∈ (sum_inr '' Ns) ∧ Sum.inr q2 ∈ Mef {q1'} s :=
    Exists.elim hyp'
    (λ q1' ↦ λ hq1': q1' ∈ N.step_set {q1} b ∧ q2 ∈ N.eval_from {q1'} s ↦
    Exists.intro (Sum.inr q1') (
      And.intro (
        Set.mem_image_of_mem sum_inr (by {
          rcases hq1' with ⟨h_1, h_2⟩
          rw [eval.step_singleton] at h_1
          exact h_1
        }
      )
      ) (h_ind q1' q2 hq1'.2)
    )
    )

  have h_in: Sum.inr q2 ∈ Mef (sum_inr '' Ns) s := eval.set_of_singleton_member h_ex
  have h_step:(M.step_set {Sum.inr q1} b) = sum_inr '' Ns := eval.step_singleton M (Sum.inr q1) b
  by {
    rw [← h_step] at h_in
    exact h_in
  }
  )

-- 2
  theorem accept_self {δ:Type} [u:Fintype δ] {N: NA' (Fin alpha) δ} {a:(Fin alpha)} {t:List (Fin alpha)}:
    N.accepts t → (trafo u N a).accepts (a::t) :=
    λ hNt ↦
    let M := (trafo u N a)
    let start := ({Sum.inr N.start}: Set (Unit ⊕ δ))
    have h0: M.step_set {M.start} a = start := (calc
    _ = M.step M.start a := eval.step_singleton M M.start a
    _ = _                := by {
      unfold NA'.step
      exact  if_pos rfl
    }
    )

    have h1: M.accept ∈ List.foldl M.step_set start t := (lift_to N.start N.accept) hNt

    by {
      rw [← h0] at h1
      exact h1
    }


-- 3
  theorem stay_old      {δ:Type} [u:Fintype δ] {N: NA' (Fin alpha) δ} {a b:(Fin alpha)} {q:δ} {q': Unit⊕δ}:
  let M := (trafo u N a)
  q' ∈ M.step_set {Sum.inr q} b → ∃ q_, q' = Sum.inr q_ :=
  

  Sum.casesOn q' -- q' is either inl or inr
  (
    let sum_inr := (λ x:δ ↦ ((Sum.inr x): Unit ⊕ δ))
    λ val h ↦
    have h2: Sum.inl val ∈ sum_inr '' (N.step q b) := by {rw [eval.step_singleton] at h;exact h}
    Exists.elim (
      (Set.mem_image sum_inr (N.step q b) (Sum.inl val)).mp h2
    ) (
      λ _ hqq ↦ False.elim (Sum.inr_ne_inl hqq.2)
    )
  ) (λ val _ ↦ Exists.intro val rfl)

-- 4
  theorem remove_step   {δ:Type} [u:Fintype δ] {N: NA' (Fin alpha) δ} {q q_:δ} {a b:(Fin alpha)}
  (hq1: ((Sum.inr q_):Unit ⊕ δ) ∈ (trafo u N a).step_set {Sum.inr q} b):
                  q_            ∈            N.step_set (       {q}:Set δ) b
  :=
  have h: Sum.inr q_ ∈ Sum.inr '' (N.step q b) := by {rw [eval.step_singleton] at hq1;exact hq1}
  have h_eq: ∃ x, x ∈ N.step q b ∧ Sum.inr x = Sum.inr q_ :=
    (Set.mem_image Sum.inr (N.step q b) (Sum.inr q_)).mp h
  have h_step: q_ ∈ N.step q b := by {
    rcases h_eq with ⟨r_,hr_⟩
    have : r_ = q_ := Sum.inr_injective hr_.2
    rw [this] at hr_
    exact hr_.1
  }
  by {rw [← eval.step_singleton] at h_step;exact h_step}

-- 5
theorem remove_accept {δ:Type} [u:Fintype δ] {N: NA' (Fin alpha) δ} {q:δ} {a b:(Fin alpha)} {z:List (Fin alpha)}:
    ((∃ q',         q' ∈ (trafo u N a).step_set {Sum.inr q}                  b ∧ (trafo u N a).accept ∈ (trafo u N a).eval_from {q'} z)
  → (∃ q_, Sum.inr q_ ∈ (trafo u N a).step_set ({Sum.inr q}:Set (Unit ⊕ δ)) b ∧ (trafo u N a).accept ∈ (trafo u N a).eval_from {Sum.inr q_} z))
  :=
  λ hyp' ↦ Exists.elim hyp' (
    λ q' hq' ↦
    Exists.elim (stay_old  hq'.1) (
      λ q_ hq_ ↦
      Exists.intro q_ (
        by {rw [hq_] at hq';exact hq'}
      )
    )
  )

-- 6
theorem remove        {δ:Type} [u:Fintype δ] {N: NA' (Fin alpha) δ} {a:(Fin alpha)} {y:List (Fin alpha)}:
  let M := (trafo u N a)
  ∀ q:δ,
  M.accept ∈ M.eval_from (({Sum.inr q}):Set (Unit ⊕ δ)) y →
  N.accept ∈ N.eval_from           {q}             y
  :=
  List.recOn y (
    λ _ h ↦ Sum.inr_injective h
  ) (
    λ b z h_ind q hyp ↦
    let M := (trafo u N a)
    have hyp': ∃ q', q' ∈ M.step_set {Sum.inr q} b ∧ M.accept ∈ M.eval_from {q'} z :=
      (eval.singleton_member_of_set (M.step_set {Sum.inr q} b)) hyp
    Exists.elim (remove_accept hyp') (
      λ q_ hq_ ↦
      have h_step_set:        q_ ∈ N.step_set ({q}:Set δ) b := remove_step hq_.1
      have h_eval:      N.accept ∈ N.eval_from {q_} z := h_ind q_ hq_.2
      (eval.set_iff_singleton_member (N.step_set {q} b)).mpr (Exists.intro q_ (And.intro h_step_set h_eval))
    )
  )

-- 7
theorem accepts_only {δ:Type} [u:Fintype δ] {N: NA' (Fin alpha) δ} {a:(Fin alpha)} {t:List (Fin alpha)}:
  (trafo u N a).accepts t → ∃ s:List (Fin alpha), t = a :: s ∧ N.accepts s :=
  let M := (trafo u N a)
  List.casesOn t (
    λ h ↦ False.elim (Sum.inl_ne_inr (Set.mem_singleton_iff.mp h).symm)
  ) (
    λ b y ↦
    λ h:        M.accept ∈ M.eval_from (M.step_set  {M.start} b) y ↦
    have h_ite: M.accept ∈ M.eval_from (ite (a=b) {Sum.inr N.start} {}) y :=
      by {rw [eval.step_singleton] at h;exact h}


    have h_:    M.accept ∈ M.eval_from (M.step       M.start  b) y := h_ite
    have hab: a = b := by_contra (
      λ hnot ↦
      have h0 : ite (a=b) ({Sum.inr N.start}: Set (Unit ⊕ δ)) {} = {} := by {refine if_neg hnot}

      have h0' : (if a = b then {Sum.inr N.start} else ∅) = NA'.eval_from M ∅ y := by {
        rw [h0]
        exact (eval.from_empty M y).symm
      }


      Set.not_mem_empty M.accept (Eq.subst (eval.from_empty M y) (
        by {
          rw [if_neg hnot] at h_ite
          exact h_ite
        }
      ))
    )
    have h01: M.step M.start b = {Sum.inr N.start} :=         by {
      exact if_pos hab
    }
    have h02: M.accept ∈ M.eval_from ({Sum.inr N.start}) y := by {rw [h01] at h_;exact h_}
    have h2: N.accepts y := (remove N.start) h02
    Exists.intro y (
      And.intro
        (congrArg (λ c ↦ c :: y) hab.symm)
        h2
    )
  )

-- 8
theorem regex         {δ:Type} {u:Fintype δ} {N: NA' (Fin alpha) δ} {a:(Fin alpha)}:
  ∀ t:List (Fin alpha),
  (trafo u N a).accepts t ↔ ∃ s:List (Fin alpha), t = a :: s ∧ N.accepts s :=

  λ _ ↦
  Iff.intro                                            accepts_only
  (λ hex ↦ Exists.elim hex (λ _ hs ↦ Eq.subst hs.1.symm (accept_self hs.2)))

end hd --head_concat_automaton



def accepts_exactly {δ:Type} (M:NA' (Fin alpha) δ) (x:List (Fin alpha)) : Prop :=
  ∀ y: List (Fin alpha), y.length = x.length → (M.accepts y ↔ y = x)

def A_N_word_bounded_by (x: List (Fin alpha)) (n:ℕ) :=
  ∃ δ:Type, ∃ u: Fintype δ, u.elems.card ≤ n ∧ ∃ M: NA' (Fin alpha) δ,
  accepts_exactly M x

theorem A_N_word_finite_prelim (x:List (Fin alpha)) :
  ∃ δ:Type, ∃ _: Fintype δ, ∃ M: NA' (Fin alpha) δ,
  accepts_exactly M x :=

  let M1 := NA'.mk (λ _:Unit ↦ λ _:(Fin alpha) ↦ {}) Unit.unit Unit.unit

  List.recOn x (
    Exists.intro (Unit) (Exists.intro (Unit.fintype) (Exists.intro (M1) (
      λ y ↦ λ h:y.length = List.nil.length ↦
      have h0: y = List.nil := List.eq_nil_of_length_eq_zero h
      have h1: M1.accepts List.nil := rfl
      by {refine Iff.symm (iff_of_true h0 (by {
        rw [← h0] at h1
        exact h1
      }))}
    )))
  )
  (
    λ a:(Fin alpha) ↦ λ y:List (Fin alpha) ↦
    λ h_ind: ∃ (δ : Type) (_ : Fintype δ) (N : NA' (Fin alpha) δ),
            ∀ (s : List (Fin alpha)), s.length = y.length → (N.accepts s ↔ s = y) ↦
    Exists.elim h_ind
    (
      λ δ hδ ↦
      Exists.elim hδ (
        λ u hu ↦
        Exists.elim hu (
          λ N ↦ λ hN: ∀ (s : List (Fin alpha)), s.length = y.length → (N.accepts s ↔ s = y) ↦
          let M := (hd.trafo u N a)
          Exists.intro (Unit ⊕ δ) (Exists.intro (instFintypeSum Unit δ) (Exists.intro M (
            λ z hz ↦
            Iff.intro (
              λ hM ↦
              have : ∃ s:List (Fin alpha), z = a :: s ∧ N.accepts s := (hd.regex z).mp hM
              Exists.elim this (
                λ s hs ↦
                have : (a::s).length = (a::y).length := calc
                                 _ = z.length := (congr_arg _ hs.1).symm
                               _ = _ := hz
                have : s.length = y.length := Nat.succ_inj'.mp this
                have : s = y := (hN s this).mp hs.2
                hs.1.trans (congr_arg _ this)
              )
            ) (
              λ hza ↦
              have : ∃ s:List (Fin alpha), z = a :: s ∧ N.accepts s :=
                Exists.intro y (
                  And.intro
                    hza
                    ((hN y rfl).mpr rfl)
                )
              (hd.regex z).mpr this
            )
          )))
        )
      )
    )
  )

theorem A_N_word_finite : ∀ x:List (Fin alpha), ∃ n:ℕ, A_N_word_bounded_by x n :=
  by {
    intro x
    have :   ∃ δ u M, accepts_exactly M x := A_N_word_finite_prelim x
    rcases this with ⟨ δ, hδ ⟩
    rcases hδ with ⟨ u, hu ⟩
    rcases hu with ⟨ M, hM ⟩
    exists u.elems.card
    unfold A_N_word_bounded_by
    exists δ
    exists u
    constructor
    exact Nat.le_refl (Finset.card Fintype.elems)
    exists M
  }
open Classical

  
  noncomputable
  def A_N_word : List (Fin alpha) → ℕ :=
  λ x ↦
  Nat.find (A_N_word_finite x) -- word-counting nondeterministic complexity
-- Find and Find_x both work

theorem Fintype_card_sum_typesafe {δ:Type} {u:Fintype δ}:
  (instFintypeSum Unit δ).elems.card = Fintype.card (Unit) + u.elems.card:= Fintype.card_sum


theorem autocomplex_bound_nil :
  ∃ δ:Type, ∃ u: Fintype δ, u.elems.card ≤ (List.nil : List (Fin alpha)).length.succ ∧ ∃ M: NA' (Fin alpha) δ,
  accepts_exactly M List.nil :=
  let q0 := (⟨0,zero_lt_one⟩:Fin 1)
  let M1:=NA'.mk (λ _:Fin 1 ↦ λ _:(Fin alpha) ↦ {}) q0 q0
  by {
    exists (Fin 1)
    exists (Fin.fintype 1)
    constructor
    exact le_refl 1
    exists M1
    unfold accepts_exactly
    intro y h
    have h0: y = List.nil := List.eq_nil_of_length_eq_zero h
    have h1: M1.accepts List.nil := rfl
    constructor
    intro _
    exact h0
    intro _
    rw [← h0] at h1
    exact h1
  }

theorem A_N_word_nil_bound_length_succ : A_N_word List.nil ≤ 1 :=
  Nat.find_min'
  ((A_N_word_finite List.nil):∃ n:ℕ, A_N_word_bounded_by List.nil n)
  (autocomplex_bound_nil)

theorem nonempty_of_mem {α : Type} {a:α} {s: Finset α} : a ∈ s → s.Nonempty :=
λ h ↦ Finset.nonempty_of_ne_empty (Finset.ne_empty_of_mem h)

theorem lower_bound (x:List (Fin alpha)): 1 ≤ A_N_word x :=
  have h1: (Nat.find (A_N_word_finite x)) ≠ 0 :=
    have : A_N_word_bounded_by x (Nat.find _) := (Nat.findX (A_N_word_finite x)).2.1
    λ h : (Nat.find _) = 0 ↦
    have : A_N_word_bounded_by x 0 := by {rw [h] at this;exact this}
    Exists.elim this (
      λ _ hδ ↦ Exists.elim hδ (
        λ u hu ↦
        Exists.elim hu.2 (
          λ M _ ↦
          lt_irrefl 0 (
            calc
            0 < u.elems.card := Finset.card_pos.mpr (nonempty_of_mem (u.complete M.start))
            _ ≤ 0 := hu.1)
        )
      )
    )
  Nat.one_le_iff_ne_zero.mpr h1

theorem A_N_word_nil : A_N_word List.nil = 1 :=
  antisymm A_N_word_nil_bound_length_succ (lower_bound List.nil)


-- May 20, 2023:
theorem accepts_exactly_hd {δ:Type} (N : NA' (Fin alpha) δ) (y : List (Fin alpha)) (a:(Fin alpha)) (u: Fintype δ)
  (hae: accepts_exactly N       y): let M := (hd.trafo u N a)
        accepts_exactly M (a :: y) :=
  λ z hz ↦ Iff.intro (
    λ hM ↦
    have : ∃ s:List (Fin alpha), z = a :: s ∧ N.accepts s := (hd.regex z).mp hM
    Exists.elim this (
      λ s hs ↦
      have : (a::s).length = (a::y).length := (calc
      _ = z.length := (congr_arg _ hs.1).symm
      _ = _ := hz)
      have : s.length = y.length := Nat.succ_inj'.mp this
      have : s = y := (hae s this).mp hs.2
      hs.1.trans (congrArg _ this)
    )
  ) (
    λ hza ↦
    have : ∃ s:List (Fin alpha), z = a :: s ∧ N.accepts s :=
      Exists.intro y (And.intro hza
      ((hae y rfl).mpr rfl)
      )
    (hd.regex z).mpr this
  )

theorem hd_card (δ:Type) (u: Fintype δ):
(Fintype.elems : Finset (Unit ⊕ δ)).card =
(Fintype.elems : Finset (       δ)).card.succ

:=

 calc
  (Fintype.elems : Finset (Unit ⊕ δ)).card = Fintype.card (Unit) + u.elems.card :=
    Fintype_card_sum_typesafe
  _ = 1                  + u.elems.card := congr_arg _ rfl
  _ = u.elems.card       + 1           := add_comm _ _
  _ = u.elems.card.succ                := Nat.succ_eq_add_one _
  _ = (Fintype.elems : Finset (       δ)).card.succ := by exact rfl

theorem hd_card_my (δ:Type) : ∀ u : Fintype δ,
(instFintypeSum Unit δ).elems.card = u.elems.card.succ := λ u ↦ hd_card δ u

theorem iterative_bound (x:List (Fin alpha)) (a:(Fin alpha)): -- May 21, 2023
  A_N_word (a::x) ≤ (A_N_word x).succ :=

  have : A_N_word_bounded_by x (Nat.findX (A_N_word_finite x)) := Nat.find_spec _
  Exists.elim this (
    λ δ hδ ↦ Exists.elim hδ (
      λ u hu ↦ Exists.elim hu.2 (
        λ N hN ↦ let M := (hd.trafo u N a)
          have ha: accepts_exactly M (a :: x) := accepts_exactly_hd N x a u hN

          have hc: (my_sum_inst u).elems.card ≤ (A_N_word x).succ :=  (calc
          (my_sum_inst u).elems.card = u.elems.card.succ := hd_card_my δ u
          _ ≤ (A_N_word x).succ := Nat.succ_le_succ hu.1)
          have : A_N_word_bounded_by (a::x) (A_N_word x).succ :=
          Exists.intro (Unit⊕δ) (Exists.intro (my_sum_inst u) (And.intro hc (Exists.intro M ha)))
          Nat.find_min' (A_N_word_finite (a::x)) this
      )
    )
  )

theorem subword_inequality (x y : List (Fin alpha)) : A_N_word (x ++ y) ≤ x.length + A_N_word y :=
List.recOn x (
  calc _ = A_N_word y   := rfl
     _ = 0 + A_N_word y := by rw [zero_add]
     _ ≤  _             := le_refl _
) (
  λ hd tl ↦ λ h_ind : A_N_word (tl ++ y) ≤ List.length tl + A_N_word y ↦
show A_N_word (hd :: tl ++ y) ≤ (hd :: tl).length + A_N_word y from
calc
A_N_word (hd :: tl ++ y) ≤ (A_N_word (tl ++ y)).succ    := iterative_bound _ _
_ ≤ (tl.length + A_N_word y).succ  := Nat.succ_le_succ h_ind
_ = tl.length.succ + A_N_word y    := by rw [Nat.succ_add]
_ = (hd :: tl).length + A_N_word y := rfl
)

theorem A_N_word_bound_length_succ' (x:List (Fin alpha)): A_N_word x ≤ x.length.succ :=
calc A_N_word x = A_N_word (x ++ List.nil)    := by rw [List.append_nil x]
            _ ≤ x.length + A_N_word List.nil:= subword_inequality _ _
            _ ≤ x.length + 1                := add_le_add_left A_N_word_nil_bound_length_succ _
            _ = x.length.succ               := rfl
