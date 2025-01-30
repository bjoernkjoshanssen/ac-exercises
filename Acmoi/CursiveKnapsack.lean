import Mathlib.Computability.NFA
import Mathlib.Data.Matrix.Basic
import Acmoi.DecisionProblem
import Acmoi.Ch7Tools
import Acmoi.Cursive
import Acmoi.Knapsack

/-
Connect the diophantine equation (a.val 0)x+(a.val 1)y=n with a walk in a digraph that has a cycle of length (a.val 0) followed by a cycle of length (a.val 1).
-/

-- KnapsackInstance_of_CursiveWalkInstance
def KI (i : CursiveWalk.Instance) : Knapsack2.Instance where
  target := i.length.val.pred
  wt := i.cycleLength

def CI (i : Knapsack2.Instance) : CursiveWalk.Instance where
  length := ⟨i.target.succ,Nat.succ_pos _⟩
  cycleLength := i.wt

theorem inverses_KCI (i : Knapsack2.Instance) : KI (CI i) = i := rfl

theorem inverses_CKI (i : CursiveWalk.Instance) : CI (KI i) = i := by
  unfold KI; unfold CI
  have :  Nat.succ (Nat.pred ↑i.length) = i.length.val := PNat.natPred_add_one _
  simp_rw [this]
  exact rfl

instance : Nonempty CursiveWalk.Instance :=
-- needed for more_inverses
  ⟨1,⟨λ _ ↦ (1:ℕ),by simp⟩⟩


theorem more_inverses : CI = Function.invFun KI := by
  unfold Function.invFun
  apply funext
  intro i
  have h : ∃ x, KI x = i := by exists CI i
  rw [dif_pos h]
  let P := (λ x ↦ KI x = i)
  have : P (Exists.choose h) := Exists.choose_spec _
  have : KI (Exists.choose h) = i := this
  have : CI (KI (Exists.choose h)) = CI i := congrArg CI this
  have : Exists.choose h = CI i := by
    rw [inverses_CKI] at this;
    exact this
  exact this.symm

theorem CS_property {i:Knapsack2.Instance} (s : Solution_of i) :
    curs_walks i.wt (walk_' i.wt (s.val 0))
    ∧ walk_' i.wt (s.val 0) (Nat.succ i.target) = i.wt.val 0 := by
  constructor
  exact walk_walks' _ _
  let G := keep_arriving i.wt s.val
  rw [← G,s.property]

-- The parsimonious function, CursiveWalkSolution_of_KnapsackSolution
def CS {i:Knapsack2.Instance} (s : Solution_of i) : Solution_of (CI i) where
    val      := walk_' i.wt (s.val 0)
    property := CS_property _

  -- CS' that maps KI i solutions to i solutions
def CS' {j:CursiveWalk.Instance} (s : Solution_of (KI j)) : Solution_of (j) where
    val      := walk_' (KI j).wt (s.val 0)
    property := by
      let Q := CS_property s
      unfold DecisionProblem.Solution
      unfold CursiveWalk
      simp
      have : j.cycleLength = (KI j).wt := rfl;
      rw [this]
      have : (KI j).target.succ = j.length.val := PNat.natPred_add_one _
      rw [← this]
      exact Q

-- As needed replace CS i by (λ sc : Solution_of i ↦ CS sc)

theorem CS_injective (i:Knapsack2.Instance) :
    Function.Injective (λ sc : Solution_of i ↦ CS sc) := by
  unfold Function.Injective; intro p₁ p₂ hp;
  unfold CS at hp
  have h₁₁: p₁.val 0 = p₂.val 0 := walk__injective' i.wt _ _ (congr_arg (λ x ↦ x.1) hp)

  have h₁₂: p₁.val 1 = p₂.val 1 := l_unique i.wt (p₁.val 0) _ _ (by
    unfold Solution_of at p₂; let g := p₂.2
    unfold DecisionProblem.Solution Knapsack2 at g
    unfold Matrix.dotProduct at g; simp at g
    rw [← h₁₁] at g;
    let G := p₁.2.symm
    have : Matrix.dotProduct i.wt.val p₁.val
    =  (Matrix.dotProduct i.wt.val fun i_1 => List.get [p₁.val 0, p₁.val 1] i_1)
     := by simp [Matrix.dotProduct]
    rw [← this,G,g]
    unfold Matrix.dotProduct
    simp
  )
  exact Subtype.eq (by
    apply funext; intro i; have : i = 0 ∨ i = 1 := fin2cases _
    cases this with
    | inl h => rw [h]; exact h₁₁
    | inr h => rw [h]; exact h₁₂
  )

-- KnapsackSolution_of_CursiveWalkSolution = KS

noncomputable def KS_val  (i : CursiveWalk.Instance) : Solution_of i → (Fin 2 → ℕ) :=
  λ wpair ↦ by
    let j := KI i
    unfold KI at j
    have : j.target.succ = i.length.val := PNat.natPred_add_one _
    let hT := wpair.2.2;
    rw [← this] at hT
    let ⟨k,hwp⟩ := getk i wpair
    rw [hwp] at hT
    exact (λ b ↦ [(getk i wpair).1, (getl j.wt hT).1].get b)

theorem KS_is_getk (i : CursiveWalk.Instance) (wpair : Solution_of i) :
    KS_val i wpair 0 = getk i wpair := rfl

noncomputable def KS {j : CursiveWalk.Instance} (wpair : Solution_of j) : Solution_of (KI j) where
  val := KS_val j wpair
  property := by
    let i := KI j; let ⟨hw,hT⟩ := wpair.2;
    have : i.target.succ = j.length.val := PNat.natPred_add_one _
    rw [← this,(getk _ _).2] at hT;
    rw [(getk _ _).2] at hw;
    have get_getl: KS_val j wpair 1 = (getl i.wt hT).1 := by simp [KS_val]
    unfold Knapsack2
    unfold Matrix.dotProduct;
    simp;
    let pro := (getl i.wt hT).2
    apply Nat.succ_injective at pro
    unfold i at pro
    simp_rw [pro]
    unfold Matrix.dotProduct at pro
    simp at pro
    rw [← get_getl]
    rw [← KS_is_getk]
    unfold Matrix.dotProduct
    simp

-- Thanks to Dillies:
theorem cast_val (u₁ u₂ : CursiveWalk.Instance) (a:ℕ→ℕ)
    (h₁ : CursiveWalk.Solution ⟨u₁,a⟩) (h₂ : CursiveWalk.Solution ⟨u₂,a⟩) (hu : u₁ = u₂)
    (h₃ : {a // CursiveWalk.Solution ⟨u₁,a⟩} = {a // CursiveWalk.Solution ⟨u₂,a⟩}):
    cast h₃ (⟨a,h₁⟩) = (⟨a,h₂⟩) := by
  subst hu; exact rfl

theorem inverses_dot1 (j : CursiveWalk.Instance) (wpair : Solution_of j):
    wpair.1 = (Eq.mp ((congr_arg _ (inverses_CKI j)) : Solution_of (CI (KI j)) = Solution_of j)
    ((λ sc : Solution_of (KI j) ↦ CS sc) (KS wpair))).1 := by
  unfold CS; unfold KS; simp;
  have : j.cycleLength = (KI j).wt := rfl; simp_rw [← this]

  let wk := walk_' j.cycleLength (getk j wpair).1
  have h₂ : CursiveWalk.Solution ⟨j,wk⟩ := by
    have : wk = wpair.1 := (getk j wpair).2.symm
    rw [this]
    exact wpair.2
  let H := (getk j wpair).2
  have h₁ : CursiveWalk.Solution ⟨CI (KI j), wk⟩
    := by {
      rw [inverses_CKI]
      unfold wk
      rw [← H];
      exact wpair.2
    }
  have h₃ : Solution_of (CI (KI j)) = Solution_of j := by rw [inverses_CKI]
  rw [H]
  simp_rw [KS_is_getk]
  have : cast h₃ ⟨wk,h₁⟩ = ⟨wk,h₂⟩
    := cast_val ((CI (KI j))) j wk h₁ h₂ (inverses_CKI j) h₃
  rw [this]

/-- We first want to prove: CS (KI j) (KS j wpair) = wpair, but that's not type-hygienic so we do:
( by {
  let wpair' := CS (KI j) (KS j wpair)
  rw [inverses_CKI] at wpair'
  exact (wpair = wpair')
})
which becomes this -/
theorem inverses_CKS_eqmp (j : CursiveWalk.Instance) (wpair : Solution_of j):
    wpair = Eq.mp
    ((congr_arg _ (inverses_CKI j)) : Solution_of (CI (KI j)) = Solution_of j)
    (CS (KS wpair)) := by
  apply SetCoe.ext
  exact inverses_dot1 _ _

theorem inverses'' (ci : CursiveWalk.Instance) :
    id = λ cs ↦ Eq.mp (congr_arg _ (inverses_CKI _)) ((λ sc : Solution_of (KI ci) ↦ CS sc) (KS cs)) := by
  apply funext; intro; exact inverses_CKS_eqmp _ _


theorem inverses_KCS {j : Knapsack2.Instance} (s : Solution_of j):
    s = (KS ((λ sc : Solution_of j ↦ CS sc) s)) := by
  apply CS_injective
  let G := inverses_CKS_eqmp (CI j) ((λ sc : Solution_of j ↦ CS sc) s)
  nth_rewrite 1 [G]
  simp

theorem KS_injective :
    ∀ (j : CursiveWalk.Instance), Function.Injective fun s : Solution_of j => KS s := by
  intro j s₁ s₂ hs
  simp at hs
  let G₁ := inverses_CKS_eqmp j s₁
  let G₂ := inverses_CKS_eqmp j s₂
  rw [G₁,G₂,hs]

theorem KS_surjective (i:CursiveWalk.Instance) :
    Function.Surjective (λ s : Solution_of i ↦ KS s) := by
  intro s
  exists CS' s
  let G := (inverses_KCS s).symm
  exact G


theorem CS_surjective (i:Knapsack2.Instance) :
    Function.Surjective (λ sc : Solution_of i ↦ CS sc) := by
  unfold Function.Surjective
  intro wpair
  let ⟨_,hT⟩ := wpair.2;
  let ⟨k,hwp⟩ := getk (CI i) wpair
  rw [hwp] at hT
  let ⟨l,lproof⟩ := (getl i.wt hT);

  exists ⟨
    (λ i ↦ [k,l].get i), by
      apply Nat.succ_injective
      have hh: (CI i).length = i.target.succ := rfl
      rw [← hh,lproof]
  ⟩
  exact SetCoe.ext (id hwp.symm)

def CI_reduction : Reduction Knapsack2 CursiveWalk := ⟨CI,
  λ i ↦ by
    constructor
    intro h; rcases h with ⟨p,hp⟩
    let CW := CS ⟨p,hp⟩; exact ⟨CW.1,CW.2⟩

    intro h; rcases h with ⟨w,hw⟩
    let KS := (KS ⟨w,hw⟩); exact ⟨KS.1,KS.2⟩
⟩

def KI_reduction : Reduction CursiveWalk Knapsack2 := ⟨KI,
  λ i ↦ by
    constructor
    intro h; rcases h with ⟨p,hp⟩
    let K := KS ⟨p,hp⟩; exact ⟨K.1,K.2⟩

    intro h; rcases h with ⟨w,hw⟩
    let C := (CS ⟨w,hw⟩);

    let C₂₂ := C.2.2
    simp_rw [inverses_CKI] at C₂₂
    exact ⟨C.1,And.intro C.2.1 C₂₂⟩
⟩



def CI_parsimoniousreduction : ParsimoniousReduction Knapsack2 CursiveWalk where
  Reduction := CI_reduction
  SolutionMap := λ i s ↦ CS s
  Property := by
    intro i
    constructor
    exact CS_injective i
    exact CS_surjective i

noncomputable def KI_parsimoniousreduction : ParsimoniousReduction CursiveWalk Knapsack2 where
  Reduction := KI_reduction
  SolutionMap := λ i s ↦ KS s
  Property := by
    intro i
    constructor
    exact KS_injective i
    exact KS_surjective i

-- Here we have finally the formal proof that UNIQUE KNAPSACK2 reduces to
-- UNIQUE CURSIVEWALK:

theorem UNIQUE_reduces_C {i: Knapsack2.Instance} (h:Nonempty (Solution_of i)) :
    (Nonempty (Unique (Solution_of i)))
    ↔ (Nonempty (Unique (Solution_of (CI_reduction.1 i)))) :=
  UNIQUE_reduces CI_parsimoniousreduction h

theorem UNIQUE_reduces_K {i: CursiveWalk.Instance} (h:Nonempty (Solution_of i)) :
    (Nonempty (Unique (Solution_of i)))
    ↔ (Nonempty (Unique (Solution_of (KI_reduction.1 i)))) :=
  UNIQUE_reduces KI_parsimoniousreduction h



noncomputable def CI_UNIQUE_reduction : Reduction (UNIQUE Knapsack2) (UNIQUE CursiveWalk) :=
  UNIQUE_reduction CI_parsimoniousreduction KI_parsimoniousreduction (by
    intro i
    unfold KI_parsimoniousreduction; unfold CI_parsimoniousreduction; simp
    unfold KI_reduction; unfold CI_reduction; simp
    exact inverses_KCI _
  )

-- The general statement that can be applied to our case
theorem jointly_inductive_decision_problem
    {I₁ I₂: Type}
    {space₁ : I₁ → Type} {space₂ : I₂ → Type}
    {reduction : I₁ → I₂} {parsimone : (i:I₁) → (space₁ i) → (space₂ (reduction i))}
    (hf : Function.Injective reduction)
    (hg : ∀ i, Function.Injective (λ s  ↦ parsimone i s)) :
    Function.Injective (
      λ (⟨i,s⟩ : Σ _ : I₁, space₁ _) ↦ ((⟨reduction i, parsimone i s⟩) : Σ _ : I₂, _)
    ) := by
  intro ⟨i₁,s₁⟩ ⟨i₂,s₂⟩ h; simp at h; have : i₁ = i₂ := hf h.1
  subst this; simp at h; have : s₁ = s₂ := hg _ h; subst this; rfl

theorem KI_injective : Function.Injective KI := by
  intro x y h
  have : CI (KI x) = CI (KI y) := congrArg CI h
  rw [inverses_CKI] at this
  rw [inverses_CKI] at this
  exact this

theorem CI_injective : Function.Injective CI := by
  intro x y h
  exact congr_arg KI h

theorem KS_CS_inverses (j : Knapsack2.Instance) [Nonempty (Solution_of j)] :
    (λ s : Solution_of (CI j) ↦ KS s) = Function.invFun (λ sc : Solution_of j ↦ CS sc) := by
  unfold Function.invFun
  apply funext
  intro s
  have h : ∃ x, CS x = s := CS_surjective j s
  rw [dif_pos (CS_surjective j s)]
  let P := (λ x ↦ CS x = s)
  have : P (Exists.choose h) := Exists.choose_spec _
  have : CS (Exists.choose h) = s := this
  let H := inverses_KCS (Exists.choose h)
  rw [H]
  simp_rw [this]

theorem K_of_C_jointly_inductive : Function.Injective (
    λ (⟨i,s⟩ : Σ i' : CursiveWalk.Instance, Solution_of _)
    ↦ ((⟨KI i, KS s⟩) : Σ _ : Knapsack2.Instance, _)) :=
  jointly_inductive_decision_problem KI_injective KS_injective

theorem C_of_K_jointly_inductive : Function.Injective (
    λ (⟨i,s⟩ : Σ i' : Knapsack2.Instance, Solution_of _)
    ↦ ((⟨CI i, CS s⟩) : Σ _ : CursiveWalk.Instance, _)) :=
  jointly_inductive_decision_problem CI_injective CS_injective
