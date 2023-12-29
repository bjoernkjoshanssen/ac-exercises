import Mathlib.Computability.NFA
import Mathlib.Data.Nat.Basic
import Mathlib.MeasureTheory.Constructions.Prod.Basic
import Std.Data.Nat.Lemmas
import Mathlib.Data.Matrix.Basic

set_option tactic.hygienic false
-- set_option maxHeartbeats 10000000
/-
Connect the diophantine equation (a.val 0)x+(a.val 1)y=n with
a walk in a digraph that has a cycle of length (a.val 0) followed by a cycle of length (a.val 1).
-/

-- #check (5 : PNat).val
/- The following data structure PosFun is useful.
  The alternative would be Fin c → PNat
  but this way we can talk about
  a.val 0
  instead of the cumbersome
  (a 0).val
  And we can write Matrix.dotProduct a.val p
  instead of Matrix.dotProduct (λ i ↦ a.val) p
-/


structure PosFun (c:ℕ) where
  val : Fin c → ℕ
  pos : ∀ i, 0 < val i


-- Some properties of walks in cursive NFAs:
structure cursiveish (a :PosFun 2) (f:ℕ → ℕ) where
 (h00 : f 0 = 0)
 (h0: ∀ t, f t = 0 → f t.succ = 1 % (a.val 0) ∨ f t.succ = (a.val 0))
 (h1: ∀ i t : ℕ, i % (a.val 0) ≠ 0 → f t = i % (a.val 0) → f t.succ = (i.succ) % (a.val 0))
 (h2s: ∀ i t, f t = (a.val 0) + (i%(a.val 1)) → f t.succ = (a.val 0) + (i.succ %(a.val 1)))

section general

def functional_eq_add_of_le  {m n : ℕ} (h : m ≤ n) : {k // n = m + k}
  := ⟨n-m,(Nat.add_sub_of_le h).symm⟩

theorem unique_iff_of_bijective {α β : Type}
{P:α → Prop} {Q:β → Prop}
{f:{a : α // P a}  → {b :β // Q b}}
(h : Function.Bijective f) :
(∃! a, P a) ↔ (∃! b, Q b) := by {
  constructor
  intro hQ
  rcases hQ with ⟨a,ha⟩
  exists f ⟨a,ha.1⟩
  constructor

  exact (f ⟨a,ha.1⟩).2

  intro b hQb
  let surj := h.2 ⟨b,hQb⟩
  rcases surj with ⟨a'pair,ha'pair⟩
  let a' := a'pair.1
  let heq := ha.2 a'pair a'pair.2

  have : a' = a'pair.1 := rfl
  rw [← this] at heq
  have hae: a'pair = ⟨a,ha.1⟩ := Subtype.coe_eq_of_eq_mk heq
  rw [hae] at ha'pair
  exact congr_arg (λ x ↦ x.1) ha'pair.symm

  intro hunique
  rcases hunique with ⟨b,hb⟩
  let surj := h.2 ⟨b,hb.1⟩
  rcases surj with ⟨apair,ha⟩
  exists apair
  constructor
  exact apair.2
  intro a' ha'
  let a'pair := (⟨a',ha'⟩ : { a // P a})
  have h₁: f a'pair = b     := hb.2 (f a'pair) (f a'pair).2
  have h₁': f a'pair = ⟨b,hb.1⟩ := Subtype.coe_eq_of_eq_mk h₁
  have h₃: f a'pair = f apair := Eq.trans h₁' ha.symm
  exact congr_arg (λ x ↦ x.1) (h.1 h₃)
}

  def find_spec_le
    (Z : ℕ → Prop)  (u:ℕ) (hu: Z u) [DecidablePred Z] : {t₀ // Z t₀ ∧ ∀ v, Z v → t₀ ≤ v}
    := ⟨Nat.find (Exists.intro u hu),by {
      constructor
      exact Nat.find_spec _
      intro v hv
      exact Nat.find_le hv
    }⟩

  -- To get uniqueness we turn ∃ results into functional results:
  def get_equation'' {a n : ℕ} (han : (a) % n = 0): {k // a = n * k} :=
  by {
    have : n ∣ a := Nat.modEq_zero_iff_dvd.mp han
    have : a / n * n = a := Nat.div_mul_cancel this
    rw [mul_comm] at this
    exact ⟨(a)/n,this.symm⟩
  }

  def get_equation' {a b n : ℕ} (hab: a ≤ b) (han : (b) % n = a % n): {k // b = a + n * k} :=
  by {
    have : (b - a) % n = 0 := Nat.sub_mod_eq_zero_of_mod_eq han
    have pair : {k // b-a = n*k} := get_equation'' this
    have : b = a + n * pair.1 := by {
      exact calc
      _ = (b-a) + a := Nat.eq_add_of_sub_eq hab rfl
      _ = (n*pair.1) + a := congr_arg (λ x ↦ x + a) pair.2
      _ = _ := Nat.add_comm _ _

    }
    exact ⟨pair.1, this⟩
  }


  theorem get_equation {a b n : ℕ} (hab: a ≤ b) (han : (b) % n = a % n): ∃ k, b = a + n * k
    := by {let pair := get_equation' hab han; exists pair.1; exact pair.2}

  theorem zero_of_mod {a n : ℕ} (hn: 1 ≤ n) (ha: a % n  = 0 ) (han: a < n) : a = 0
    := by {
    have : ∃ k, a = 0 + n * k := get_equation (zero_le _) ha
    rcases this with ⟨k,hk⟩
    cases k
    rw [hk]
    simp
    have : n < n := calc
      _ = 0 + n * 1 := by ring
      _ ≤ 0 + n * n_1.succ := by {field_simp;exact tsub_add_cancel_iff_le.mp rfl}
      _ = a := hk.symm
      _ < n := han
    exfalso
    exact LT.lt.false this
  }

end general

theorem walk_mod_a0 (a : PosFun 2) {f:ℕ → ℕ}(ish : cursiveish a f)(t: ℕ)
(hs : ∀ s, s ≤ t → f s < (a.val 0)) : f t = t % (a.val 0)
  := by {
  induction t
  rw [ish.h00]
  rfl
  have hfn : f n = n % (a.val 0) := n_ih (λ s hsn ↦ hs s (Nat.le_step hsn))
  by_cases hna : (n % (a.val 0) = 0); rw [hna] at hfn
  let g := ish.h0 n hfn; cases g
  rename f n.succ = 1 % (a.val 0) => cg; rw [cg]
  have : (n+1) % (a.val 0) = (n % (a.val 0) + 1 % (a.val 0)) % (a.val 0) := Nat.add_mod _ _ _
  rw [hna,zero_add,Nat.mod_mod] at this; exact id this.symm

  rw [h]; exfalso; let gg := hs n.succ (le_refl _)
  have : (a.val 0) < (a.val 0) := Eq.trans_lt (id h.symm) gg
  exact LT.lt.false this; exact ish.h1 n n hna hfn
 }

 theorem get_a0dvd (a : PosFun 2) {f:ℕ → ℕ}(ish : cursiveish a f)(t: ℕ)
(h : (∀ s, s ≤ t → f s < a.val 0)) (h2: f t.succ = a.val 0): t % a.val 0 = 0
  := by {
  have ftt : f t = t % (a.val 0) := walk_mod_a0 a ish (by {
    exact t
  }) h
  by_contra hcontra
  let g := ish.h1 t t hcontra ftt
  have ht1: t.succ % (a.val 0) = (a.val 0) := Eq.trans g.symm h2
  have ht2: t.succ % (a.val 0) < (a.val 0) := Nat.mod_lt _ (a.pos 0)
  have : (a.val 0) < (a.val 0) := Eq.trans_lt ht1.symm ht2
  exact LT.lt.false this
 }


theorem strengthen {a : PosFun 2}  {t₀:ℕ} {f:ℕ → ℕ}
  (ish : cursiveish a f) (ht₀ : (∀ s, s ≤ t₀ → f s ≠ (a.val 0))) :  ∀ s, s ≤ t₀ → f s < (a.val 0)
  := by {
    induction t₀; intro s; intro;
    have : s = 0 := Nat.le_zero.mp a_1
    rw [this,ish.h00]; exact (a.pos 0)

    intro s hs; cases hs
    let g := n_ih (by {intro _ hsn; exact ht₀ _ (Nat.le_step hsn)}) n (le_refl _)
    by_cases (f n = 0); let gg := ish.h0 n h; cases gg; rw [h_1]

    let G := ht₀ n.succ (le_refl _); rw [h_1] at G
    exact Nat.mod_lt _ (a.pos 0)

    let ggg := ht₀ n.succ (le_refl _); exfalso; exact ggg h_1

    let g1 := ish.h1 (f n) n (by {
      contrapose h; simp; simp at h
      exact zero_of_mod (Nat.one_le_iff_ne_zero.mpr (Nat.not_eq_zero_of_lt (a.pos 0))) h g
    }) (Nat.mod_eq_of_lt g).symm
    rw [g1]

    exact Nat.mod_lt _ ((a.pos 0))
    let g := n_ih (by {intro _ hsn; exact ht₀ _ (Nat.le_step hsn)}) s a_1
    exact g
  }


-- Our running example will be the "cursive" NFA that has a cycle of length (a.val 0) and then a cycle of length (a.val 1).
-- We implement it as an infinite NFA where only the first (a.val 0)+(a.val 1) states are reachable,
-- in order to avoid type casting issues.


def cursive_step' (a : PosFun 2)  : ℕ → Set (ℕ) :=
-- ideally, define this over Posfun c for any c
  by {
    exact (
      λ q ↦ ite (q=0)
      {1 % (a.val 0),(a.val 0)}
      (ite (q<(a.val 0)) {(q+1) % (a.val 0)} {(((a.val 0) + (((q-(a.val 0)+1) % (a.val 1)))):ℕ)})
    )
}
def cursive' (a : PosFun 2) : NFA (Fin 1) (ℕ) := {
  step := λ q _ ↦ cursive_step' a q
  start := {0}
  accept := {a.val 0}
}

def walk_in_NFA (f : ℕ → ℕ) (M : NFA (Fin 1) ℕ) := f 0 ∈ M.start
∧ ∀ k, f k.succ ∈ M.step (f k) 0

def walk_in_cursive' (a : PosFun 2) (f : ℕ → ℕ) := walk_in_NFA f (cursive' a)

structure KnapsackInstance (c: ℕ) where
  target : ℕ
  weight : PosFun c

structure DecisionProblem where
  Instance : Type
  Space : Instance → Type
  Solution : (Σ i : Instance, Space i) → Prop

structure Solution {P : DecisionProblem} (i : P.Instance) where
  val : P.Space i
  property : P.Solution ⟨i,val⟩


def Knapsack : DecisionProblem :=
{
  Instance := Σ c : ℕ, KnapsackInstance c
  Space := λ ⟨c,_⟩ ↦ (Fin (c) → ℕ)
  Solution := λ ⟨i,p⟩ ↦ (i.snd.target = Matrix.dotProduct p i.snd.weight.val)
}

def KnapsackSolution (i : Knapsack.Instance):= Solution i

def Knapsack2 : DecisionProblem :=
{
  Instance := KnapsackInstance 2
  Space := λ _ ↦ (Fin 2 → ℕ) -- given that the # of items is 2, the space doesn't depend on the instance
  Solution := λ ⟨i,p⟩ ↦ (i.target = Matrix.dotProduct i.weight.val p)
}
structure CursiveWalkInstance (c: PNat) where
  length : ℕ
  cycleLength : PosFun c

structure CursiveWalkSolution (i : CursiveWalkInstance 2) where
  w : ℕ → ℕ
  walks : walk_in_cursive' (i.cycleLength) w
  timed : w i.length = i.cycleLength.val 0

def CursiveWalk : DecisionProblem :=
{
  Instance := CursiveWalkInstance 2
  Space := λ _ ↦ (ℕ → ℕ)
  Solution := λ ⟨i,w⟩ ↦ walk_in_cursive' i.cycleLength w ∧  w i.length = i.cycleLength.val 0
}


def Knapsack2Solution (i : Knapsack2.Instance):= Solution i
-- make everything work with this version

structure Reduction (P Q : DecisionProblem) where
  Map : P.Instance → Q.Instance
  Property : ∀ i : P.Instance, (∃ x, P.Solution ⟨i, x⟩) ↔ (∃ y, Q.Solution ⟨(Map i), y⟩)
/-
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

structure ParsimoniousReduction (P Q : DecisionProblem) where
  Reduction : Reduction P Q
  Fun : (i : P.Instance) → (P.Space i → Q.Space (Reduction.Map i))  -- or : Fun : Σ i : P.Instance, (P.Space i → Q.Space (Reduction.Map i))
  Preserves : ∀ i : P.Instance, ∀ v : P.Space i, P.Solution ⟨i,v⟩ → Q.Solution ⟨Reduction.Map i,Fun i v⟩
  Property : ∀ i : P.Instance, Function.Bijective (
    (λ v ↦ ⟨Fun i v.1,Preserves i v.1 v.2⟩) :
      {v : P.Space i           // P.Solution ⟨i,v⟩}
    → {w : Q.Space (Reduction.Map i) // Q.Solution ⟨Reduction.Map i,w⟩}
  )

-- We can prove my_reduction is a Reduction

theorem generalh2s' (a : PosFun 2) (F: ℕ → ℕ)
(hw: walk_in_cursive' a F)
: ∀ (i t : ℕ), (F t) = a.val 0 + i % a.val 1 → (F (Nat.succ t)) = a.val 0 + Nat.succ i % a.val 1
:= by {
  intro i t hit; let g := hw.2 t; unfold walk_in_cursive' at g; rw [hit] at g
  unfold cursive' at g;
  unfold cursive_step' at g; simp at g;
  have : a.val 0 ≠ 0 := by {
    intro hcontra;
    let ha₀pos := a.pos 0
    rw [hcontra] at ha₀pos
    exact LT.lt.false ha₀pos
  }
  have : ¬ ( a.val 0 = 0 ∧ i % a.val 1 = 0) := by {intro hcontra; exact this hcontra.1}
  rw [if_neg this] at g
  rw [g]
}

theorem getish' (F:ℕ → ℕ) (a : PosFun 2) (hw : walk_in_cursive' a F) :
cursiveish a (λ n ↦ (F n))
  := {
    h00 := by {
      have : F 0 = 0 := Set.eq_of_mem_singleton hw.1
      rw [this];
    }
    h0 := by {
      intro t ht; let g := hw.2 t;
      rw [ht] at g; cases g;left;rw [h];
      right;rw [h];
    }
    h1 := by {
      intro i t hi ht;
      unfold walk_in_cursive' at hw; unfold cursive' at hw
      unfold cursive_step' at hw;
      unfold walk_in_NFA at hw
      simp at hw
      let g := hw.2 t
      have : F t ≠ 0 := Eq.trans_ne ht hi
      rw [if_neg this] at g
      have : i % (a.val 0) < (a.val 0) := Nat.mod_lt _ (a.pos 0)
      rw [← ht] at this; rw [if_pos this] at g
      simp at g; rw [Nat.add_mod,ht] at g
      rw [g]; simp
    }
    h2s := generalh2s' _ _ hw
  }

def walk_' (a : PosFun 2) (k:ℕ) (i: ℕ) : ℕ :=
by {
  exact (ite (i ≥ ((a.val 0)*k).succ)
  (((a.val 0) + ((i-((a.val 0)*k).succ) % (a.val 1))))
  (i % (a.val 0))
)
}

theorem walk__injective_lt' (a : PosFun 2) {k₁ k₂ : ℕ} (hk : k₁ < k₂) : walk_' a k₁ ≠ walk_' a k₂ := by {
  intro hcontra
  have : ∀ n, walk_' a k₁ n = walk_' a k₂ n := fun n ↦ congrFun hcontra n
  let g := this (a.val 0 * k₁).succ
  unfold walk_' at g;
  simp at g
  have h₀: ¬ (k₂) ≤ (k₁) := Nat.not_le.mpr hk
  have : ¬ (a.val 0 * k₂) ≤ (a.val 0 * k₁) := by {
    intro hcontra
    have : k₂ ≤ k₁ := Nat.le_of_mul_le_mul_left hcontra ((a.pos 0))
    exact h₀ this
  }
  have : ¬ Nat.succ (a.val 0 * k₂) ≤ Nat.succ (a.val 0 * k₁) := by {
    intro hcontra
    exact this (Nat.succ_le_succ_iff.mp hcontra)
  }
  rw [if_neg this] at g
  have : ∀ x : ℕ, x % a.val 0 < a.val 0 := by {intro x;exact Nat.mod_lt _ (a.pos 0)}
  let G := this (a.val 0*k₁).succ;
  rw [← g] at G; exact LT.lt.false G
}

theorem keep_arriving' (a : PosFun 2) (p : Fin 2 → ℕ)
: walk_' a (p 0) (a.val 0*(p 0) + 1 + a.val 1*(p 1)) = a.val 0 :=
  by {
    let k := p 0
    let l := p 1
    unfold walk_'; rw [if_pos _]; simp;
    rw [add_assoc]
    have : PosFun.val a 0 * k + (1 + PosFun.val a 1 * l)
    = (PosFun.val a 0 * k + (PosFun.val a 1 * l)) + 1 := by ring
    rw [this,← Nat.succ_eq_add_one]
    apply Nat.succ_le_succ_iff.mpr
    exact Nat.le_add_right _ _
  }

theorem unique_walk_cursive_helper' (a : PosFun 2) {w : ℕ → ℕ}
(hw: walk_in_cursive' a w) (k : ℕ) (hwk: w (a.val 0*k).succ = a.val 0 ∧ ∀ n < (a.val 0*k).succ, w n ≠ a.val 0)
  : ∀ n < (a.val 0*k).succ, w n < a.val 0 := by {
  intro n; induction n; intro; rw [hw.1]; exact (a.pos 0)

  intro hn_1; by_cases (n_1 < (a.val 0*k).succ)
  let G:= hwk.2 n_1.succ hn_1
  unfold walk_in_cursive' at hw; unfold cursive' at hw; unfold cursive_step' at hw
  unfold walk_in_NFA at hw
  simp at hw;
  let g := hw.2 n_1; let gg := n_ih h; rw [if_pos gg] at g
  by_cases (w n_1=0); rw [if_pos h] at g; simp at g; cases g
  rw [h_1]; exact Nat.mod_lt _ (a.pos 0)

  exfalso; exact G h_1; let H := hw.2 n_1
  rw [if_neg h,if_pos gg] at H; simp at H; rw [H]; exact Nat.mod_lt _ (a.pos 0)

  let g := hw.2 n_1; unfold cursive' at g; unfold cursive_step' at g; simp at g
  have : n_1 < (a.val 0*k).succ := Nat.lt_of_succ_lt hn_1
  let G := n_ih this; rw [if_pos G] at g
  have : w n_1 ≠ 0 := by {
    intro hcontra; rw [if_pos hcontra] at g; simp at g; cases g
    exact h this; let H := hwk.2 n_1.succ hn_1; exact H h_1
  }
  rw [if_neg _] at g; simp at g; rw [g]; exact Nat.mod_lt _ (a.pos 0); exact this
  }

theorem little_lemma' (a : PosFun 2) {w: ℕ → ℕ} {k n: ℕ}
(g: w (Nat.succ n) ∈ NFA.step (cursive' a) (a.val 0 + (n - Nat.succ (a.val 0 * k)) % a.val 1) 0)
(h₄: n - Nat.succ (a.val 0 * k) + 1 = n - a.val 0 * k) : w (Nat.succ n) = a.val 0 + (n - a.val 0 * k) % a.val 1
:= by {
  unfold cursive' at g; unfold cursive_step' at g; simp at g; rw [← h₄];
  have : ¬ (a.val 0 = 0 ∧ (n - Nat.succ (a.val 0 * k)) % a.val 1 = 0) := by {
    intro hcontra
    have : 0 < 0 := by {
      have ha₀pos := a.pos 0
      rw [hcontra.1] at ha₀pos
      exact ha₀pos
    }
    exact LT.lt.false this
  }
  rw [if_neg this] at g
  exact g
}

theorem unique_walk_cursive' (a : PosFun 2) {w : ℕ → ℕ}
  (hw: walk_in_cursive' a w) {k : ℕ} (hwk': w (a.val 0*k).succ = a.val 0 ∧ ∀ n < (a.val 0*k).succ, w n ≠ a.val 0) :
  w = walk_' a k :=
  by {
  have hwk : w ((a.val 0)*k).succ = (a.val 0) ∧ ∀ n < ((a.val 0)*k).succ, w n < (a.val 0) :=
    ⟨ hwk'.1, (unique_walk_cursive_helper' a hw _ hwk')⟩
  apply funext; intro x; induction x; unfold walk_in_cursive' at hw; unfold walk_'
  rw [if_neg _]; simp; exact hw.1
  intro hcontra; simp at hcontra
  by_cases hnk : (n.succ ≥ ((a.val 0)*k).succ)
  unfold walk_'; rw [if_pos _]; simp; let g := hw.2 n; rw [n_ih] at g
  unfold walk_' at g; by_cases hnks : (n ≥ ((a.val 0)*k).succ )

  have h₂: n ≥ (a.val 0)*k := Nat.lt_succ.mp hnk
  have h₃: n - (a.val 0)*k ≥ 1 := (le_tsub_iff_left h₂).mpr hnks
  have h₄: n - ((a.val 0)*k).succ + 1 = n - (a.val 0)*k := by {rw [Nat.sub_succ']; exact Nat.sub_add_cancel h₃}

  rw [if_pos hnks] at g; exact little_lemma' a g h₄

  have hn2k: n = (a.val 0)*k := (Nat.eq_of_lt_succ_of_not_lt hnk hnks).symm
  rw [hn2k]; simp; rw [if_neg hnks] at g; have : (a.val 0) ∣ n := Dvd.intro k (id hn2k.symm)
  have : n % (a.val 0) = 0 := Nat.mod_eq_zero_of_dvd this
  rw [this] at g
  cases g; exact hwk.1

  rw [hn2k] at h; exact h; exact hnk; unfold walk_'; rw [if_neg hnk]
  unfold walk_' at n_ih

  have hnss : n.succ < ((a.val 0)*k).succ := Nat.not_le.mp hnk
  have hnlt : n < ((a.val 0)*k).succ := Nat.lt_of_succ_lt hnss
  have hn2k : ¬ n ≥ ((a.val 0)*k).succ := by {
    intro hcontra
    have : n < n := Nat.lt_of_lt_of_le hnlt hcontra
    exact LT.lt.false this
  }

  rw [if_neg hn2k] at n_ih; unfold walk_in_cursive' at hw
  let g₂ := hw.2 n; rw [n_ih] at g₂

  unfold cursive' at g₂; unfold cursive_step' at g₂
  simp at g₂
  have : n % (a.val 0) < (a.val 0) := Nat.mod_lt _ ((a.pos 0))
  rw [if_pos this] at g₂; by_cases (n % (a.val 0) = 0); rw [if_pos h] at g₂
  have h1: n.succ % (a.val 0) = 1 % (a.val 0) := by {
    rw [Nat.succ_eq_add_one,Nat.add_mod,h,]
    simp
  }
  rw [h] at n_ih; let g := hw.2 n; rw [n_ih] at g
  unfold cursive' at g; unfold cursive_step' at g
  simp at g; cases g₂; rw [h1]; cases g; exact h_2; exact h_1
  simp at h_1; rw [h1]; exfalso; let G := hwk'.2 n.succ hnss
  exact G h_1; rw [if_neg h] at g₂; simp at g₂; exact g₂
}

theorem ne_of_le' (a : PosFun 2) {w : ℕ → ℕ}
  {t₀:ℕ}
  (hw: walk_in_cursive' a w)
  (ht₀ : w (Nat.succ t₀) = a.val 0 ∧ ∀ (v : ℕ), w (Nat.succ v) = a.val 0 → t₀ ≤ v)
  : ∀ (s : ℕ), s ≤ t₀ → (w s) ≠ a.val 0
  := by {
      intro s hs
      cases s
      intro hcontra
      let gg := hw.1
      simp at gg
      rw [gg] at hcontra
      let ha₀pos := a.pos 0
      rw [← hcontra] at ha₀pos
      exact LT.lt.false ha₀pos
      intro hcontra
      let g := ht₀.2 n (hcontra)
      have : n < n := Nat.succ_le.mp (le_trans hs g)
      exact LT.lt.false this
    }

theorem ne_first' (a : PosFun 2) {w : ℕ → ℕ} {t₀ k:ℕ} (hk: t₀ = a.val 0 * k)
(hw: walk_in_cursive' a w)
  (ht₀ : w (Nat.succ t₀) = a.val 0 ∧ ∀ (v : ℕ), w (Nat.succ v) = a.val 0 → t₀ ≤ v)
  :w (a.val 0*k).succ = a.val 0 ∧ ∀ n, n < (a.val 0 * k).succ → w n ≠ a.val 0 :=
    by {
      constructor; rw [hk] at ht₀; exact ht₀.1

      intro u hu hu2; cases u
      let g := hw.1
      rw [hu2] at g
      let ha₀pos := a.pos 0
      rw [← g] at ha₀pos
      exact LT.lt.false ha₀pos

      have : (a.val 0)*k < (a.val 0)*k := calc
        _ = t₀  := id hk.symm
        _ ≤ n   := ht₀.2 n hu2
        _ < (a.val 0)*k := Nat.succ_lt_succ_iff.mp hu
      exact LT.lt.false this
    }

def getk1' (a : PosFun 2) {w : ℕ → ℕ} {u:ℕ}
(hw: walk_in_cursive' a w) (hu: w (Nat.succ u) = a.val 0) : ℕ
  := by {
    let t₀ := (find_spec_le (λ s ↦ w (Nat.succ s) = (a.val 0)) u hu).1
    let ht₀ := (find_spec_le (λ s ↦ w (Nat.succ s) = (a.val 0)) u hu).2
    let ish := getish' w a hw
    have hlt :  ∀ (s : ℕ), s ≤ t₀ → (w s) < (a.val 0) := by {
      intro _ hs
      exact strengthen ish (ne_of_le' a hw ht₀) _ hs
    }
    have h02 : t₀ % (a.val 0) = 0 % (a.val 0) := get_a0dvd a ish _ hlt ht₀.1
    let k := (get_equation' (Nat.zero_le _) h02).1
    exact k
  }

  theorem getk2' (a : PosFun 2) {w : ℕ → ℕ} {u:ℕ}
  (hw: walk_in_cursive' a w) (hu: w (Nat.succ u) = a.val 0)
  : w = walk_' a (getk1' a hw hu)
  := by {
    let t₀ := (find_spec_le (λ s ↦ w (Nat.succ s) = (a.val 0)) u hu).1
    let ht₀ := (find_spec_le (λ s ↦ w (Nat.succ s) = (a.val 0)) u hu).2
    let ish := getish' w a hw
    have hlt :  ∀ (s : ℕ), s ≤ t₀ → (w s) < (a.val 0) := by {
      intro _ hs
      exact strengthen ish (ne_of_le' a hw ht₀) _ hs
    }
    have h02 : t₀ % (a.val 0) = 0 % (a.val 0) := get_a0dvd a ish _ hlt ht₀.1
    let hk := (get_equation' (Nat.zero_le _) h02).2

    rw [zero_add] at hk
    exact unique_walk_cursive' a hw (ne_first' a hk hw ht₀)
  }

theorem l_unique' (a : PosFun 2) {k l₁ l₂ : ℕ}
  (he: a.val 0*k + 1 + a.val 1*l₁ = a.val 0*k + 1 + a.val 1*l₂) : l₁=l₂
  :=  by {
    let ha₁pos := a.pos 1
    exact Nat.eq_of_mul_eq_mul_left ha₁pos (Nat.add_left_cancel he)
  }

theorem getl' (a : PosFun 2) {k n:ℕ} (hmod₀: walk_' a k n = a.val 0)
:  {l : ℕ // n = a.val 0*k + 1 + a.val 1*l}
  := by {
    have hge : n ≥ (a.val 0)*k + 1 := by {
      unfold walk_' at hmod₀; by_contra hcontra; rw [if_neg hcontra] at hmod₀
      have : n % (a.val 0) < (a.val 0) := Nat.mod_lt _ (a.pos 0); rw [hmod₀] at this
      exact LT.lt.false this
    }
    let L := n - ((a.val 0)*k+1)
    have hL : n = (a.val 0)*k + 1 + L := (functional_eq_add_of_le hge).2
    rw [hL] at hmod₀; unfold walk_' at hmod₀; simp at hmod₀
    have : L = n - ((a.val 0)*k+1) := rfl; rw [← this] at hmod₀
    have h₁: (L/(a.val 1))*(a.val 1) = L := Nat.div_mul_cancel (Nat.modEq_zero_iff_dvd.mp hmod₀)
    have h₂: L = (a.val 1) * (L / (a.val 1)) := by {rw [mul_comm] at h₁; exact h₁.symm}
    let l := L / (a.val 1)
    have : n = (a.val 0) * k + 1 + (a.val 1) * l := by {rw [← h₂];exact hL}
    exact ⟨l,this⟩
  }

theorem walk_walks' (a : PosFun 2) (k:ℕ)
  : walk_in_cursive' a (walk_' a k) :=
  by {
    constructor; unfold walk_'
    have : ¬ 0 ≥ Nat.succ ((a.val 0) * k) := of_decide_eq_false rfl
    rw [if_neg this]
    exact rfl
    intro k_1; induction k_1; unfold walk_'
    have : ¬ Nat.zero ≥ Nat.succ ((a.val 0) * k) := of_decide_eq_false rfl
    rw [if_neg this]
    by_cases (k=0)
    have : Nat.succ Nat.zero ≥ Nat.succ ((a.val 0) * k)
      := Nat.succ_le_succ (Nat.le_zero.mpr (mul_eq_zero_of_right (a.val 0) h))
    rw [if_pos this,h]; simp; right; exact rfl
    have h₁: ¬ Nat.zero = ((a.val 0) * k) := by {
      intro hcontra; cases Nat.zero_eq_mul.mp hcontra
      have : 0 < (a.val 0) := (a.pos 0)
      rw [h_1] at this
      exact Nat.not_succ_le_zero 0 this
      exact h h_1
    }
    have h₂: ¬ Nat.zero ≥ ((a.val 0) * k) := by {
      intro hcontra
      exact h₁ (id (Nat.le_zero.mp hcontra).symm)
    }
    have : ¬ Nat.succ Nat.zero ≥ Nat.succ ((a.val 0) * k) := by {
      intro hcontra
      exact h₂ (Nat.lt_succ.mp hcontra)
    }
    rw [if_neg this]; left; rfl

    unfold walk_'
    by_cases hss : (Nat.succ (Nat.succ n) ≥ Nat.succ ((a.val 0) * k))
    rw [if_pos hss]
    by_cases hnk : (Nat.succ n ≥ Nat.succ ((a.val 0) * k))
    rw [if_pos hnk]
    simp
    have h₁ : n ≥ (a.val 0)*k := Nat.succ_le_succ_iff.mp hnk
    have h₂ : n + 1 - (a.val 0)*k = n - (a.val 0)*k + 1 := Nat.sub_add_comm h₁

    unfold cursive'; unfold cursive_step'; simp; rw [h₂]

    have : ¬ (a.val 0 = 0 ∧ (n - a.val 0 * k) % a.val 1 = 0) := by {
      intro hcontra
      have : 0 < 0 := by {
        let ha₀pos := a.pos 0
        rw [hcontra.1] at ha₀pos
        exact ha₀pos
      }
      exact LT.lt.false this
    }
    rw [if_neg this]
    simp
    rw [if_neg hnk];
    have h₅ : n.succ = (a.val 0)*k := (Nat.eq_of_lt_succ_of_not_lt hss hnk).symm
    have h₃: n+1 - (a.val 0)*k = 0 := tsub_eq_of_eq_add_rev h₅
    simp
    rw [h₃,h₅]; simp; right; exact rfl
    -- early times:
    rw [if_neg hss]
    have : ¬ Nat.succ n ≥ Nat.succ ((a.val 0) * k) := by {
      intro hcontra
      have : n.succ ≤ n.succ.succ := Nat.le_succ (Nat.succ n)
      exact hss (le_trans hcontra this)
    }
    rw [if_neg this]; by_cases (n.succ % (a.val 0) = 0); rw [h];
    have : n.succ.succ % (a.val 0) = 1 % (a.val 0) := by {
      rw [Nat.succ_eq_add_one,Nat.add_mod,h,];simp
    }
    rw [this]; left; exact rfl

    unfold cursive'; unfold cursive_step'; simp
    rw [if_neg h]; have : n.succ % (a.val 0) < (a.val 0) := Nat.mod_lt _ (a.pos 0)
    rw [if_pos this]; simp
  }

theorem walk__injective' (a : PosFun 2) (k₁ k₂ : ℕ)
(he : walk_' a k₁ = walk_' a k₂) : k₁ = k₂ :=
  by {
    contrapose he
    have : k₁ < k₂ ∨ k₂ < k₁ := Ne.lt_or_lt he
    cases this; exact walk__injective_lt' a h;
    exact (walk__injective_lt' a h).symm
  }

def walk_of_solution' (i:KnapsackInstance 2)
  : {p : ℕ×ℕ // i.target.succ = i.weight.val 0 * p.1 + 1 + i.weight.val 1 * p.2}
  → {w : ℕ → ℕ // walk_in_cursive' i.weight w ∧ w i.target.succ = i.weight.val 0}
  := by {
    intro p; let k := p.1.1
    exists walk_' i.weight k; constructor
    exact walk_walks' i.weight k; rw [p.2];
    let pfun : Fin 2 → ℕ := λ i ↦ [p.1.1, p.1.2].get i
    exact keep_arriving' i.weight pfun
  }

theorem walk_of_solution_injective' (i:KnapsackInstance 2) :
Function.Injective (walk_of_solution' i) := by {
  unfold Function.Injective
  intro p₁ p₂ hp
  unfold walk_of_solution' at hp
  simp at hp
  have h₁₁: p₁.1.1 = p₂.1.1 := walk__injective' i.weight p₁.1.1 p₂.1.1 hp
  have h₁₂: p₁.1.2 = p₂.1.2 := l_unique' i.weight (Eq.trans p₁.2.symm (by {rw [h₁₁]; exact p₂.2}))
  exact SetCoe.ext (Prod.ext h₁₁ h₁₂)
}

theorem walk_of_solution_surjective' (i:KnapsackInstance 2) :
Function.Surjective (walk_of_solution' i) := by {
  unfold Function.Surjective
  intro wpair
  let ⟨hw,hT⟩ := wpair.2; let k := getk1' i.weight hw hT
  have hwp : wpair.1 = walk_' i.weight k := getk2' i.weight _ _
  rw [hwp] at hT
  rename wpair.1 (Nat.succ i.target) = (i.weight.val 0) => hTold
  let lpair := (getl' i.weight hT); let l := lpair.1
  exists ⟨(k,l), lpair.2⟩; exact SetCoe.ext (id hwp.symm)
}

theorem walk_of_solution_bijective' (i:KnapsackInstance 2) :
Function.Bijective (walk_of_solution' i) := by {
  constructor;
  exact walk_of_solution_injective' i
  exact walk_of_solution_surjective' i
}

theorem main' (i:KnapsackInstance 2) : (∃! p : ℕ×ℕ, i.target.succ = i.weight.val 0 * p.1 + 1 + i.weight.val 1 * p.2)
↔ (∃! w, walk_in_cursive' i.weight w ∧ w i.target.succ = i.weight.val 0)
  := unique_iff_of_bijective (walk_of_solution_bijective' i)

-- We can now elegantly get rid of the successor in theorem main:
theorem main_n' {n:ℕ}  (a : PosFun 2)
: (∃! p : ℕ×ℕ, n = a.val 0 * p.1 + 1 + a.val 1 * p.2)
↔ (∃! w, walk_in_cursive' a w ∧ w n = a.val 0) :=
by {
  cases n;
  -- n is 0:
  constructor; intro h; exfalso; rcases h with ⟨p,hp⟩; let g := hp.1
  have : 1 ≤ 0 := calc
         1 ≤ (a.val 0) * p.1 + 1 := Nat.le_add_left 1 ((a.val 0) * p.1)
         _ ≤ (a.val 0) * p.1 + 1 + (a.val 1) * p.2 := Nat.le_add_right ((a.val 0) * p.1 + 1) ((a.val 1) * p.2)
         _ = 0 := self_eq_add_left.mp g
  exact Nat.not_succ_le_zero 0 this

  intro h; exfalso; rcases h with ⟨w,hw⟩; let G := hw.1.2; rw [hw.1.1.1] at G
  exact LT.lt.false (Nat.lt_of_lt_of_eq (a.pos 0) (id G.symm))
  -- n is T.succ:
  let i : KnapsackInstance 2 := {
    target := n_1
    weight := a
  }
  exact main' i
}

theorem main_prod' {n:ℕ} (a : PosFun 2)
: (∃! p : Fin 2 → ℕ, n = a.val 0 * p 0 + 1 + a.val 1 * p 1)
↔ (∃! w, walk_in_cursive' a w ∧ w n = a.val 0) :=
by {
  constructor; intro h
  rcases h with ⟨p,hp⟩
  exact (main_n' a).mp (by {
    exists (p 0, p 1); simp
    constructor; exact hp.1
    intro p'0 p'1 hp'; let g := hp.2 (λ i ↦ [p'0, p'1].get i) hp'
    constructor
    exact congr_arg (λ x ↦ x 0) g
    exact congr_arg (λ x ↦ x 1) g
  })
  intro h
  let g := (main_n' a).mpr h
  rcases g with ⟨p,hp⟩
  exists (λ i ↦ [p.1, p.2].get i)
  constructor; simp; exact hp.1; intro p' hp'
  let g := hp.2 (p' 0, p' 1) hp'; apply funext; intro i
  have : i ≤ 1 := Fin.le_last _
  have : i < 1 ∨ i = 1 := by exact lt_or_eq_of_le this
  cases this
  have : i ≤ 0 := by exact Fin.succ_le_succ_iff.mp h_1
  have : i = 0 := by exact Fin.le_zero_iff.mp this
  rw [this]; simp; exact congr_arg (λ x ↦ x.1) g; rw [h_1]
  simp; exact congr_arg (λ x ↦ x.2) g
}

theorem main_dot' {n:ℕ} (a : PosFun 2)
: (∃! p : Fin 2 → ℕ, n = Matrix.dotProduct a.val p + 1)
↔ (∃! w, walk_in_cursive' a w ∧ w n = a.val 0) :=
by {
  constructor; intro h; rcases h with ⟨p,hp⟩
  have : (∃! p : Fin 2 → ℕ, n = (a.val 0) * p 0 + 1 + (a.val 1) * p 1) := by {
    exists p; constructor; let g := hp.1
    unfold Matrix.dotProduct at g; rw [g];
    simp; ring; intro y h
    apply hp.2 y; rw [h]
    have : (a.val 0) * y 0 + 1 + (a.val 1) * y 1 = (a.val 0) * y 0 + (a.val 1) * y 1 + 1 := by ring
    rw [this];
    unfold Matrix.dotProduct
    rfl
  }
  exact (main_prod' a).mp this
  intro h
  have : (∃! p : Fin 2 → ℕ, n = (a.val 0) * p 0 + 1 + (a.val 1) * p 1) := (main_prod' a).mpr h
  rcases this with ⟨p,hp⟩
  exists p; constructor; let g := hp.1; rw [g]; simp;unfold Matrix.dotProduct
  simp; ring
  intro y hy; let g := hp.2 y; simp at g;apply g -- smart!
  rw [hy]; unfold Matrix.dotProduct
  have : (a.val 0) * y 0 + 1 + (a.val 1) * y 1 = (a.val 0) * y 0 + (a.val 1) * y 1 + 1 := by ring
  rw [this]; rfl
}


def my_reduction {c:PNat} (i : KnapsackInstance c) : CursiveWalkInstance c :=
-- change this to knapsack.instance
{
  length := i.target.succ
  cycleLength := i.weight
}


def walk_of_solution'' (i:Knapsack2.Instance)
: Knapsack2Solution i → CursiveWalkSolution (my_reduction i)
:= by {
  intro s
  -- let k := s.solution 0
  exact {
    w           := walk_' i.weight (s.val 0)
    walks       := walk_walks' _ _
    timed       := by {
      let g := keep_arriving' i.weight s.val
      unfold my_reduction
      simp
      rw [← g]
      rw [s.property]
      have : (Nat.succ (Matrix.dotProduct i.weight.val s.val)) =
             (i.weight.val 0 * s.val 0 + 1 + i.weight.val 1 * s.val 1)
      := by {
        have : (i.weight.val 0 * s.val 0 + 1 + i.weight.val 1 * s.val 1) =
               (i.weight.val 0 * s.val 0 + i.weight.val 1 * s.val 1) + 1 := by ring
        rw [this]
        rfl
      }
      exact congr_arg _ this
    }
  }
}



theorem main_dot_knapsack' (i : Knapsack2.Instance)
: (∃! p : Fin 2 → ℕ, i.target = Matrix.dotProduct i.weight.val p)
↔ (∃! w, walk_in_cursive' i.weight w ∧ w i.target.succ = i.weight.val 0) :=
by {
  constructor; intro h; rcases h with ⟨p,hp⟩; apply (main_dot' i.weight).mp
  exists p; constructor; simp; simp at hp; exact hp.1
  intro y; let g := hp.2 y; simp at g; intro h; simp at h; exact g h

  intro h
  have : (∃! p : Fin 2 → ℕ, i.target.succ = Matrix.dotProduct i.weight.val p + 1) := (main_dot' i.weight).mpr h
  rcases this with ⟨p,hp⟩; exists p; simp; simp at hp; exact hp
}

theorem main_dot_knapsack'' (i : Knapsack2.Instance)
: Nonempty (Unique (Knapsack2Solution i))
↔ Nonempty (Unique (CursiveWalkSolution (my_reduction i)))
:=
by {
  rw [unique_iff_exists_unique]
  rw [unique_iff_exists_unique]
  let H := main_dot_knapsack' i
  constructor
  intro h

  unfold KnapsackSolution at h
  rcases h with ⟨s,hs⟩
  exists {
    w := walk_' i.weight (s.val 0)
    walks := sorry
    timed := sorry
  }
  sorry
  sorry
}

def my_reduction' : Reduction Knapsack2 CursiveWalk := {
  Map := λ i ↦ {
    length := i.target.succ
    cycleLength := i.weight
  }
  Property := λ i ↦ by {
    constructor
    intro h
    rcases h with ⟨p,hp⟩
    exists walk_' i.weight (p 0)
    sorry
    sorry -- use "main"
  }
}
