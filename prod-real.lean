import Mathlib.Data.Real.NNReal
--import data.Vector.basic
/-

Exercise 6.1: Let a1,_,ak,b1,_,bk ≥ 0 be real numbers such that for each 1≤i≤k, ai ≤bi. Then
∏^k_{i=1}ai ≤∏^k_{i=1}b_i.

Exercise 6.2: If f_i achieves maximum at c_i then prod_i f_i (x_i) achieves maximum at c.

To to do the inductive step we need List.rec_on and hence projections p1 and p2.
However, def dominates below shows a better way of working with Lists in some ways.
-/

def dominates (a : List (NNReal×NNReal)) : Prop := ∀ i, i ∈ a → (i.1:NNReal) ≤ i.2

lemma dom_cons (hd : NNReal×NNReal) (tl: List (NNReal×NNReal)): dominates (hd:: tl) → dominates tl :=
  λ h i hi ↦
  have : i ∈ hd :: tl := List.mem_cons_of_mem hd hi
  h i this

def p1 {U:Type}: List (U×U) → List U :=
λ l ↦ List.map (λ x : U×U ↦ x.1) l

def p2 {U:Type}: List (U×U) → List U :=
λ l ↦ List.map (λ x : U×U ↦ x.2) l


theorem p1_List_ofFn {U:Type} {n:ℕ} (Q1 Q2: Fin n → U):
p1 (List.ofFn (λ k ↦ (Q1 k, Q2 k))) = 
List.ofFn (λ k ↦ Q1 k) :=
List.map_ofFn _ _ 

theorem p2_List_ofFn {U:Type} {n:ℕ} (Q1 Q2: Fin n → U) : p2 (List.ofFn (λ k ↦ (Q1 k, Q2 k))) = 
List.ofFn (λ k ↦ Q2 k) :=
List.map_ofFn _ _ 

theorem exercise_6_1 (a : List (NNReal×NNReal)) :
  dominates (a) →
  (p1 a).prod ≤ (p2 a).prod := List.recOn a (
    λ _ ↦ le_refl _
  ) (
    λ hd tl h_ind hdom ↦
    have hhh: hd.1 ≤ hd.2 := hdom hd (List.mem_cons_self hd tl)
    calc
      (p1 (hd :: tl)).prod = hd.1   *  (p1 tl).prod := List.prod_cons
      _ ≤ hd.2   *  (p1 tl).prod := mul_le_mul_right' hhh (p1 tl).prod
      _ ≤ hd.2   *  (p2 tl).prod := mul_le_mul_left' (h_ind (dom_cons hd tl hdom)) _
      _ = (hd.2 :: (p2 tl)).prod := List.prod_cons.symm
  )


def diag {n:ℕ} (F: Fin n → NNReal → NNReal): Vector NNReal n → List NNReal :=  -- (x1, x2) -> (F 1 x1, F 2 x2)
λ x ↦ List.ofFn (λ i : Fin n ↦ F i (x.get i))

def prod_diag {n:ℕ} (F: Fin n → NNReal → NNReal) : Vector NNReal n → NNReal :=
λ (x: Vector NNReal n) ↦ (diag F x).prod

lemma mem_List {U:Type} {n:ℕ} (G : Fin n → U ) (z:U) :
  z ∈ List.ofFn (λ j : Fin n ↦ G j) → ∃ j, G j = z:=
  λ hz ↦
  have : z ∈ Set.range (λ j : Fin n ↦ G j) :=  (List.mem_ofFn _ _).mp hz
  Set.mem_range.mp this

theorem exercise_6_2 {n:ℕ} (F: Fin n → NNReal → NNReal) (c : Vector NNReal n)
(h : ∀ i, ∀ y, F i y ≤ F i (c.get i))
: ∀ x, prod_diag F x ≤ prod_diag F c
:= λ x ↦
  have h_easy: ∀ i, ∀ x : Vector NNReal n, F i (x.get i)≤ F i (c.get i) :=
    λ i x ↦ h i (x.get i)

  have : dominates (List.ofFn (
    λ j : Fin n ↦
    (F j (x.get j), F j (c.get j))
  )) := λ z ↦
    have hex:
      z ∈ List.ofFn (λ (j : Fin n) ↦ (F j (Vector.get x j), F j (c.get j)))
      →
      ∃ j, (F j (Vector.get x j), F j (c.get j)) = z := (mem_List _ _)
    λ hz ↦
    have : ∃ j, (F j (Vector.get x j), F j (c.get j)) = z := hex hz
    Exists.elim this (
      λ j hj ↦ calc
      z.1 = F j (Vector.get x j) := (congr_arg Prod.fst hj.symm).trans rfl
      _  ≤ F j (Vector.get c j)  := h_easy j x
      _ = z.2 := ((congr_arg Prod.snd (Eq.symm hj)).congr_right.mp rfl).symm
    )-- from h_easy

let a:= (List.ofFn (
    λ j : Fin n ↦
    (F j (x.get j), F j (c.get j))
  ))
have hp : (p1 a).prod ≤ (p2 a).prod := exercise_6_1 _ this

have hp1a: p1 a = (List.ofFn (
    λ j : Fin n ↦
    (F j (x.get j))
  )) := p1_List_ofFn _ _ -- probably have to prove from def. of a by List.rec_on

have hp2a: p2 a = (List.ofFn (
    λ j : Fin n ↦
    (F j (c.get j))
  )) := p2_List_ofFn _ _ -- probably have to prove by List.rec_on

have : (List.ofFn (λ i : Fin n ↦ F i (x.get i))).prod
          ≤ (List.ofFn (λ i : Fin n ↦ F i (c.get i))).prod := calc
        _ = (p1 a).prod := by rw [hp1a]
        _ ≤ (p2 a).prod := hp
        _ = _           := by rw [hp2a]

calc  _ = (diag F x).prod := rfl
      _ = (List.ofFn (λ i : Fin n ↦ F i (x.get i))).prod := rfl
      _ ≤ (List.ofFn (λ i : Fin n ↦ F i (c.get i))).prod := this
      _ = (diag F c).prod := rfl
      _ = prod_diag F c:= rfl
