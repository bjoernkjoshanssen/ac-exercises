import Mathlib.Computability.NFA
import Mathlib.Data.Matrix.Basic

/-!
Wikipedia (https://en.wikipedia.org/wiki/Parsimonious_reduction):
  "A general reduction from problem A to problem B is a transformation that guarantees that
  whenever A has a solution B also has at least one solution and vice versa."

  "A parsimonious reduction guarantees that
  for every solution of A, there exists a unique solution of B and vice versa."
  "A parsimonious reduction is a transformation from one problem to another (a reduction) that
  preserves the number of solutions."

  Instead of representing the number of solutions as a number in ℕ,
  here we just require a bijective function:
-/


structure DecisionProblem where
  Instance : Type
  Space    : Instance → Type
  Solution : (Σ i : Instance, Space i) → Prop
  Question : Instance → Prop := λ i ↦ ∃ s, Solution ⟨i,s⟩ -- default question

def UNIQUE (P : DecisionProblem) : DecisionProblem where
  Instance := P.Instance
  Space    := P.Space
  Solution := P.Solution
  Question := λ i ↦ Nonempty (Unique ({s // P.Solution ⟨i,s⟩}))

def Solution_of {P : DecisionProblem} (i : P.Instance) := { val : P.Space i // P.Solution ⟨i,val⟩}

def Reduction (P Q : DecisionProblem) := { Map : P.Instance → Q.Instance //
   ∀ i : P.Instance, P.Question i ↔ Q.Question (Map i)}

structure Reduction' (P Q : DecisionProblem) where
  Map : P.Instance → Q.Instance
  Property : ∀ i : P.Instance,
    (Nonempty (Solution_of i)) ↔ (Nonempty (Solution_of (Map i)))


structure ParsimoniousReduction (P Q : DecisionProblem) where
  Reduction : Reduction P Q
  SolutionMap : (i : P.Instance) → (Solution_of i → Solution_of (Reduction.1 i))  -- or : Fun : Σ i : P.Instance, (P.Space i → Q.Space (Reduction.Map i))
  Property : ∀ i : P.Instance, Function.Bijective (
    SolutionMap i
  )


theorem inv_sur {α β :Type} {f :α→β} (hf: Function.Surjective f) (b : β) [Nonempty α]:
    b = f ((Function.invFun f) b) :=
  (Function.invFun_eq (hf _)).symm

theorem inj_of_sur  {α β :Type} {f :α→β} (hf: Function.Surjective f) [Nonempty α] :
    Function.Injective (Function.invFun f) := by
  intro x y h; let G := congr_arg f h; rw [← inv_sur hf x,← inv_sur hf y] at G; exact G

theorem surj_of_inj  {α β :Type} {f :α→β} (hf: Function.Injective f) [Nonempty α] :
    Function.Surjective (Function.invFun f) := by
  intro x; exists (f x); let G :=  Function.invFun_comp hf; exact congr_arg (λ F ↦ F x) G

theorem unique_of_surjective {α β :Type} {f :α→β} (hf: Function.Surjective f)
    (h:Nonempty (Unique α)) : Nonempty (Unique β) := by
  let s := (Classical.choice h).default
  have ha: ∀ a : α, a = s := (Classical.choice h).uniq
  have : Nonempty α := Nonempty.intro s
  have ti : Inhabited β := { default := f s }

  have : (Function.invFun f) (f s) = (Function.invFun f) default := calc
    _ = s := ha _
    _ = _ := (ha _).symm

  have hb: ∀ b : β, b = default :=
  λ b ↦ calc
    b = f (Function.invFun f b) := inv_sur hf _
    _ = f s                     := by {rw [ha (Function.invFun f b)]}
    _ = default                 := inj_of_sur hf this
  exact Nonempty.intro ⟨ti,hb⟩

theorem unique_of_bijective {α β :Type} {f :α→β} (hf: Function.Bijective f) [Nonempty α]:
Nonempty (Unique α) ↔  Nonempty (Unique β) := by {
  constructor
  exact unique_of_surjective hf.2
  exact unique_of_surjective (surj_of_inj hf.1)
}

theorem parsi_unique {P Q : DecisionProblem} (φ : ParsimoniousReduction P Q) (i: P.Instance)
    [Nonempty (Solution_of i)] :
    (Nonempty (Unique (Solution_of i))) ↔ (Nonempty (Unique (Solution_of (φ.Reduction.1 i)))) :=
  unique_of_bijective (φ.Property i)

theorem UNIQUE_reduces {P Q:DecisionProblem} (φ : ParsimoniousReduction P Q)
    {i: P.Instance} (_:Nonempty (Solution_of i)) :
    (Nonempty (Unique (Solution_of i))) ↔ (Nonempty (Unique (Solution_of (φ.Reduction.1 i)))) :=
  parsi_unique φ _

def UNIQUE_reduction {P Q : DecisionProblem} (φ : ParsimoniousReduction P Q)
    (ψ : ParsimoniousReduction Q P)
    (hφ : ∀ i, ψ.Reduction.1 (φ.Reduction.1 i) = i) : Reduction (UNIQUE P) (UNIQUE Q) := by
    -- This can be strengthened to show ψ always exists
  unfold Reduction
  exists φ.Reduction.1
  intro i
  by_cases h : (Nonempty (Solution_of i))
  exact UNIQUE_reduces φ h
  constructor
  intro hu;exfalso; let s :=                                   (Classical.choice hu).default; exact h (Nonempty.intro s)
  intro hu;exfalso; let s := (ψ.SolutionMap) (φ.Reduction.1 i) (Classical.choice hu).default;
  rw [hφ] at s
  exact h (Nonempty.intro s)
