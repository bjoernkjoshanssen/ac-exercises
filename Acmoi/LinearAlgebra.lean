import Mathlib.Topology.Clopen
-- import Mathlib.Data.Nat.Prime
import Mathlib.NumberTheory.SmoothNumbers
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Matrix.Reflection
import Mathlib.Tactic.NormNum.Prime
import Mathlib.LinearAlgebra.Matrix.ZPow
import Mathlib.Data.Fin.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.LinearAlgebra.Matrix.PosDef

import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Data.Matrix.Basis
import Acmoi.QuasTheorem
import Acmoi.Perm
import Acmoi.Theorem1_49
/-!

# Automatic complexity using linear algebra

-/

/-- ast for "asterisk": ast δ is what we in mathematics articles would
 call δ^*, the iteration of the transition function δ over a word in.
 To be able to talk about the identity matrix intelligently,
 we assume the field is at least `ℤ / 2ℤ`.
 -/
def astMat {α : Type*} {R : Type*} [Add R] [Mul R] [Zero R] [One R]
  {n q : ℕ} (word : Fin n → α) (matrices : α → Fin q → Fin q → R) :
  Fin q → Fin q → R := match n with
| 0 => fun x y => ite (x=y) 1 0
| Nat.succ m => Matrix.mulᵣ (matrices (word m)) (astMat (Fin.init word) matrices)

/-- The `q × 1` column vector representing a state. -/
def astCol {α R : Type*} [Add R] [Mul R] [Zero R] [One R] {n  q : ℕ}
  (word : Fin n → α)
  (matrices : α → Fin q → Fin q → R)
  (init : Fin q → Fin 1 → R) : Fin q → Fin 1 → R :=
  Matrix.mulᵣ (astMat word matrices) init

/-- The `q`-tuple representing a state. -/
def astM {α R : Type*} [Add R] [Mul R] [Zero R] [One R] {n q : ℕ} (word : Fin n → α)
  (matrices : α → Fin q → Fin q → R)
  (init : Fin q → R) : Fin q → R := fun a =>
    (astCol word matrices fun x => fun _ => init x) a 0

def Al_at_most {α : Type*} (R : Type*) [Add R] [Mul R] [Zero R] [One R] {n : ℕ}
  (word : Fin n → α) (q : ℕ) : Prop :=
  ∃ matrices : α → Fin q → Fin q → R,
  ∃ init final : Fin q → R, ∀ v : Fin n → α,
    astM v matrices init = final ↔ v = word

/-- A contrast with regular automatic complexity: -/
lemma emp_ring  {R : Type*} [Semiring R] [Nontrivial R] {A : Type*} (anything : R) :
    Al_at_most (R := R) (α := A) ![] 0 := by
  use (by intros; exact anything), 0, 0
  intro v
  constructor
  · intro;ext z;have := z.2;simp at this
  · intro hv;subst hv;simp;unfold astM astCol astMat
    ext z;have := z.2;simp at this

/-- A counterpoint to the contrast above.
Even though we need alphabet size 2 or more, we don't need 0 ≠ 1 in R.
 -/
lemma one_ring {A : Type*} {a b : A} {h : a ≠ b} {R : Type*} [Add R] [Mul R] [Zero R] [One R] :
    ¬ Al_at_most (R := R) (α := A) ![a] 0 := by
  unfold Al_at_most
  push_neg
  intro matrices init final
  use ![b]
  have : init = final := by
    ext z; have := z.2;simp at this
  subst this
  left
  constructor
  · ext z; have := z.2;simp at this
  · intro hc
    apply congrFun at hc
    specialize hc 0
    simp at hc
    exact h hc.symm

lemma one_ring₂ {A : Type*} [DecidableEq A] {a : A} :
    Al_at_most (R := ℕ) (α := A) ![a] 1 := by
  use (fun x _ _ => ite (x = a) 1 0), ![1], ![1]
  intro v
  constructor
  · intro hv
    unfold astM astCol astMat astMat at hv
    simp at hv
    ext i
    have : i = 0 := Fin.fin_one_eq_zero i
    subst this
    simp at hv ⊢
    by_cases h : v 0 = a
    · rw [h]
    · rw [if_neg h] at hv
      apply congrFun at hv
      specialize hv 0
      simp at hv
      have : (
        Matrix.mulᵣ (Matrix.mulᵣ (fun (z₀ z₁ : Fin 1) ↦ 0)
        (fun (x y : Fin 1) ↦ if x = y then 1 else 0)) (fun (x x : Fin 1) ↦ 1)) 0 0 = 0 := by
        simp
        conv =>
          lhs; arg 1; arg 1; change 0
        simp
      simp_all only [Fin.isValue, Matrix.mulᵣ_eq, one_ne_zero]
  · intro hv
    subst hv
    unfold astM astCol astMat astMat
    simp
    ext x : 1
    simp_all only [Fin.isValue, Matrix.cons_val_fin_one]
    rfl
/-- The linear-algebra automatic complexity of any word is actually `0` in a unary alphabet.
After all, `{0}` is a `0`-dimensional vector space but it is a nonempty set.
In essence, the `none` state does not contribute to the dimension count.
-/
lemma one_ring₁ {A R : Type*} [s : Subsingleton A] [Semiring R] {n : ℕ} (w : Fin n → A) :
    Al_at_most (R := R) (α := A) w 0 := by
  use (fun _ z => (not_lt_zero' z.2).elim)
  -- the empty function is defined by: "give me an input; oh it can't exist; done."
  use fun z => (not_lt_zero' z.2).elim, fun z => (not_lt_zero' z.2).elim
  intro v
  constructor
  · exact fun hv => funext <| fun i => subsingleton_iff.mp s (v i) (w i)
  · exact fun hv => funext <| fun i => (not_lt_zero' i.2).elim


open Classical
noncomputable def matrix_of_fn {R : Type*} { q : ℕ} [Add R] [Mul R] [Zero R] [One R] (f : Fin q → Fin q) :
  Fin q → Fin q → R :=
  fun y x => ite (y = f x) 1 0

noncomputable def matrix_of_fn' {Q R : Type*} [Add R] [Mul R] [Zero R] [One R] (f : Q → Q) :
  Q → Q → R :=
  fun y x => ite (y = f x) 1 0


lemma matrix_of_fn_mul_single {R : Type*} [Semiring R] {q : ℕ}
  (i : Fin q.succ) (g : Fin q.succ → Fin q.succ) (a : Fin q.succ) :
    (Matrix.mulᵣ (matrix_of_fn g)
      (fun (x : Fin q.succ) _ => Pi.single (I := Fin q.succ) (f := fun _ => R) a (1:R) x)
    ) i (0 : Fin 1) =
    Pi.single (I := Fin q.succ) (f := fun _ => R) (g a) (1 : R) i := by
  unfold Matrix.mulᵣ
  simp
  rw [Matrix.dotProduct]
  unfold Pi.single Function.update
  simp
  split_ifs with g₀
  · subst g₀
    unfold matrix_of_fn
    simp
  · unfold matrix_of_fn
    rw [if_neg g₀]

/-- This lets us convert automatic complexity to its linear algebraic version. -/
lemma astM_matrix_of_fn_ast_single {q n : ℕ} {α R : Type*} [Semiring R] [Fintype α] (w : Fin n → α)
  (δ : α → Fin q.succ → Fin q.succ) (init : Fin q.succ) :
    astM w ((matrix_of_fn (R := R)) ∘ δ) (Pi.single           init  1)
                                        = Pi.single  (ast δ w init) 1 := by
    induction n with
    | zero =>
      unfold astM ast astCol astMat
      ext i
      simp [Matrix.mulᵣ]
      rw [Matrix.dotProduct]
      simp
    | succ n ih =>
      specialize ih (Fin.init w)
      unfold ast astM astCol astMat
      ext i
      rw [← matrix_of_fn_mul_single, Fin.natCast_eq_last n, ← ih]
      repeat apply congrFun
      let D := fun y x ↦ if y = δ (w (Fin.last n)) x then (1:R) else 0
      let M₀ := astMat (Fin.init w) fun (b:α) (y x:Fin (q+1)) ↦ if y = δ b x then (1:R) else 0
      let e₀ := fun (x:Fin (q+1)) (x_1 : Fin 1) =>
        Pi.single (I := Fin q.succ) (f := fun _ => R) (init : Fin (q+1)) (1:R) x
      let V := (fun x (z : Fin 1) ↦ Matrix.mulᵣ (astMat (Fin.init w) fun (b:α) (y x:Fin (q+1)) ↦ if y = δ b x then (1:R) else 0) (fun (x:Fin (q+1)) (x_1 : Fin 1) =>
        Pi.single (I := Fin q.succ) (f := fun _ => R) (init : Fin (q+1)) (1:R) x) x (0 : Fin 1))
      show Matrix.mulᵣ (Matrix.mulᵣ D <|M₀) e₀ = Matrix.mulᵣ D V
      repeat rw [Matrix.mulᵣ_eq]
      rw  [(Matrix.mul_assoc D M₀ e₀)]
      simp [M₀, e₀, V]
      congr


/-- Total automatic complexity, relational form, assuming a `Fin` type.
Of course, A_at_most_Fin = A_at_most but that requires a proof.
-/
def A_at_most_Fin {A : Type} {n : ℕ} (w : Fin n → A) (q : ℕ): Prop :=
    ∃ δ init final p, (∀ a q, Fintype.card (δ a q) = 1) ∧ accepts_word_path δ w init final p
    ∧ ∀ v : Fin n → A, ∀ p' : Fin (n+1) → (Fin q),
      accepts_word_path δ v init final p' → p = p' ∧ w = v

lemma accepts_word_path_equiv {A : Type} {n : ℕ} (q : ℕ) (Q : Type)
    (e : Q ≃ Fin q) (δ : A → Q → Set Q) (init final : Q)
    (v : Fin n → A) (p' : Fin (n + 1) → Fin q)
    (h : accepts_word_path (fun a i ↦ e '' δ a (e.invFun i)) v (e init) (e final) p') :
    accepts_word_path δ v init final fun t ↦ e.invFun (p' t) := by
  unfold accepts_word_path at h ⊢
  constructor
  · simp
    rw [h.1]
    simp
  · constructor
    · simp
      rw [h.2.1]
      simp
    · intro i
      simp
      have := h.2.2 i
      simp at this
      exact this

theorem A_at_most_Fin_iff {A : Type} {n : ℕ} (w : Fin n → A) (q : ℕ) :
    A_at_most_Fin w q ↔ A_at_most w q := by
  constructor
  · exact fun h => ⟨Fin q, Fin.fintype q, Fintype.card_fin q, h⟩
  · intro h
    obtain ⟨Q,x,hQ⟩ := h
    have e : Q ≃ Fin q := Fintype.equivFinOfCardEq hQ.1
    obtain ⟨δ, init, final, p, hδ⟩ := hQ.2
    use (fun a i => e.toFun '' (δ a (e.invFun i)))
    use e.toFun init, e.toFun final
    use (fun t => e.toFun (p t))
    constructor
    · intro a i
      rw [← hδ.1 a (e.invFun i)]
      have := @Set.card_image_of_injective Q (Fin q) (δ a (e.invFun i)) _ e.toFun _
        (by
          apply Function.HasLeftInverse.injective
          have := e.left_inv
          use e.invFun
        )
      rw [← this]
      aesop
    · constructor
      · unfold accepts_word_path at hδ ⊢
        constructor
        · simp
          exact hδ.2.1.1
        · constructor
          · simp
            exact hδ.2.1.2.1
          · intro i
            simp
            exact hδ.2.1.2.2 i
      · intro v p' h
        constructor
        · simp
          have := (hδ.2.2 v (fun t => e.invFun (p' t)) (by
            apply accepts_word_path_equiv
            tauto
          )).1
          rw [this]
          simp
        · exact (hδ.2.2 v (fun t => e.invFun (p' t)) (by
            apply accepts_word_path_equiv
            tauto
          )).2

/-- Linear algebra automatic complexity over `R` is bounded by A(w) for
 any semiring `R` in which `0 ≠ 1`, including `ℕ ℤ ℚ ℝ ℂ`, `Fin 4`, etc. -/
lemma Al_le_A {R : Type*} [Semiring R] [Nontrivial R] {n a q : ℕ} {w : Fin n → Fin a}
     (hP : A_at_most w q.succ) :
    Al_at_most R w q.succ := by
  rw [← A_at_most_Fin_iff] at hP
  unfold A_at_most_Fin at hP
  unfold Al_at_most
  obtain ⟨δ,init,final,p,hδ⟩ := hP
  let Δ : Fin a → Fin q.succ → Fin q.succ :=
    fun b q => (Fin.find (δ b q)).get (by
      have := hδ.1 b q
      have : δ b q ≠ ∅ := by
        contrapose this
        simp at this
        rw [this]
        simp
      exact Fin.isSome_find_iff.mpr <| Set.nonempty_def.mp <| Set.nonempty_iff_ne_empty.mpr this
    )
  have hδΔ: (fun a q ↦ {Δ a q}) = δ := by
    ext  b q r
    have h₀ := hδ.1 b q
    have : ∃ d, δ b q = {d} := by
      have := Fintype.card_eq_one_iff.mp h₀
      obtain ⟨d,hd⟩ := this
      use d
      ext z
      constructor
      · intro hz;simp;
        have := hd ⟨z,hz⟩
        rw [← this]
      · simp
        intro hz
        rw [hz]
        exact Subtype.coe_prop d
    obtain ⟨d,hd⟩ := this
    rw [hd]
    simp
    have h₁ : Δ b q ∈ δ b q := by
      unfold Δ;
      apply Fin.find_spec
      simp
      congr
    constructor <;> (
      intro hr
      subst hr
      rw [hd] at h₁
      simp at h₁
      tauto)
  use matrix_of_fn ∘ Δ, Pi.single init 1, Pi.single final 1
  intro v
  conv =>
    lhs; arg 1; arg 2; change matrix_of_fn ∘ Δ
  rw [astM_matrix_of_fn_ast_single]
  constructor
  · intro h
    apply congrFun at h
    specialize h final
    simp at h
    have h₀ : ast Δ v init = final := by
      unfold Pi.single Function.update at h
      simp at h
      have : (0:R) ≠ 1 := by refine zero_ne_one' R
      tauto
    have := (@path_iff_star (Fin q.succ) init final (Fin a) _ Δ n v).mpr h₀
    obtain ⟨p',hp'⟩ := this
    symm

    rw [hδΔ] at hp'
    have := hδ.2.2 v p' hp'
    tauto
  · intro h
    symm at h
    subst h
    have : ast Δ w init = final := by
      rw [← path_iff_star]
      exact ⟨p, hδΔ ▸ hδ.2.1⟩
    rw [this]

/-- Should really make the alphabet an arbitrary type A -/
theorem Al_bounded (R : Type*) [Semiring R] [Nontrivial R]
    {n a : ℕ} (w : Fin n → Fin a) :
    ∃ q, Al_at_most R w q := by
  obtain ⟨q,hq⟩ := @A_bounded (Fin a) n w
  use q
  by_cases H : q = 0
  · exact (H ▸ A_N_ge_one w <| A_N_le_A_minus <| A_minus_le_A hq).elim
  · obtain ⟨m,hm⟩ := Nat.exists_eq_succ_of_ne_zero H
    subst hm
    exact Al_le_A hq

/-- The use of linear algebra in automatic complexity
was introduced in Theorem 3 of Shallit and Wang 2001.
The automatic complexity of `w` over a semiring `R` is denoted `Al R w`.
Here `l` is for `linear-algebraic` but also `lower` since
we have `Al w ≤ A w`.

-/
noncomputable def Al (R : Type*) [Semiring R] [Nontrivial R] {a : ℕ} {n : ℕ}
  (w : Fin n → Fin a) : ℕ := Nat.find (Al_bounded R w)


/- Over the field ℤ / 5ℤ and the alphabet {0,1},
  the word 00 has complexity at most 3.
  Should make this decidable however.
  -/
example : Al_at_most
  (α := Fin 2) (R := Fin 5) (word := ![0,0]) (q := 3) := by
  use (![
    !![
      1,0,0;
      0,1,0;
      0,0,1
    ],
    !![
      0,1,0;
      0,0,1;
      1,0,0
    ]
  ])
  use ![1,0,0], ![1,0,0]
  intro v
  unfold astM astCol astMat astMat astMat
  simp
  constructor
  · intro h
    by_cases h₀ : v 0 = 0
    · by_cases h₁ : v 1 = 0
      ext i
      fin_cases i
      · simp
        rw [h₀]
        rfl
      · simp
        rw [h₁]
        rfl
      · have h₁ : v 1 = 1 := Fin.eq_one_of_neq_zero (v 1) h₁
        have h₂ : v = ![0,1] := by ext i; fin_cases i <;> simp_all
        subst h₂
        simp at h
        contrapose h
        decide
    · have h₀ : v 0 = 1 := Fin.eq_one_of_neq_zero (v 0) h₀
      by_cases h₁ : v 1 = 0
      · have h₂ : v = ![1,0] := by ext i; fin_cases i <;> simp_all
        subst h₂
        contrapose h
        decide
      · have h₁ : v 1 = 1 := Fin.eq_one_of_neq_zero (v 1) h₁
        have h₂ : v = ![1,1] := by ext i; fin_cases i <;> simp_all
        subst h₂
        contrapose h
        decide
  · intro hv
    subst hv
    simp
    decide
