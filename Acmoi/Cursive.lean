import Mathlib.Computability.NFA
import Mathlib.Data.Matrix.Basic
import Acmoi.Ch7Tools
import Acmoi.DecisionProblem
-- #check (5 : PNat).val
/- The following data structure PF is useful.
  The alternative would be Fin c → PNat
  but this way we can talk about
  a.val 0
  instead of the cumbersome
  (a 0).val
  And we can write Matrix.dotProduct a.val p
  instead of Matrix.dotProduct (λ i ↦ a.val) p
-/


structure PF (c:ℕ) where
  val : Fin c → ℕ
  pos : ∀ i, 0 < val i


-- Some properties of walks in cursive NFAs:
structure cursiveish (a :PF 2) (f:ℕ → ℕ) where
  (h00 : f 0 = 0)
  (h0: ∀ t, f t = 0 → f t.succ = 1 % (a.val 0) ∨ f t.succ = (a.val 0))
  (h1: ∀ i t : ℕ, i % (a.val 0) ≠ 0 → f t = i % (a.val 0) → f t.succ = (i.succ) % (a.val 0))
  (h2s: ∀ i t, f t = (a.val 0) + (i%(a.val 1)) → f t.succ = (a.val 0) + (i.succ %(a.val 1)))


theorem walk_mod_a0 (a : PF 2) {f:ℕ → ℕ}(ish : cursiveish a f)(t: ℕ)
    (hs : ∀ s, s ≤ t → f s < (a.val 0)) : f t = t % (a.val 0) := by
  induction  t
  rw [ish.h00]
  rfl
  rename ℕ => n
  rename (∀ s ≤ n, f s < PF.val a 0) → f n = n % PF.val a 0 => n_ih
  have hfn : f n = n % (a.val 0) := n_ih (λ s hsn ↦ hs s (Nat.le_step hsn))
  by_cases hna : (n % (a.val 0) = 0); rw [hna] at hfn
  let g := ish.h0 n hfn; cases g
  rename f n.succ = 1 % (a.val 0) => cg; rw [cg]
  have : (n+1) % (a.val 0) = (n % (a.val 0) + 1 % (a.val 0)) % (a.val 0) := Nat.add_mod _ _ _
  rw [hna,zero_add,Nat.mod_mod] at this; exact id this.symm
  rename f (Nat.succ n) = PF.val a 0 => h
  rw [h]; exfalso; let gg := hs n.succ (le_refl _)
  have : (a.val 0) < (a.val 0) := Eq.trans_lt (id h.symm) gg
  exact LT.lt.false this; exact ish.h1 n n hna hfn

theorem get_a0dvd (a : PF 2) {f:ℕ → ℕ}(ish : cursiveish a f)(t: ℕ)
    (h : (∀ s, s ≤ t → f s < a.val 0)) (h2: f t.succ = a.val 0): t % a.val 0 = 0 := by
  have ftt : f t = t % (a.val 0) := walk_mod_a0 a ish t h
  by_contra hcontra
  let g := ish.h1 t t hcontra ftt
  have ht1: t.succ % (a.val 0) = (a.val 0) := Eq.trans g.symm h2
  have ht2: t.succ % (a.val 0) < (a.val 0) := Nat.mod_lt _ (a.pos 0)
  have : (a.val 0) < (a.val 0) := Eq.trans_lt ht1.symm ht2
  exact LT.lt.false this


theorem strengthen {a : PF 2}  {t₀:ℕ} {f:ℕ → ℕ}
    (ish : cursiveish a f) (ht₀ : (∀ s, s ≤ t₀ → f s ≠ (a.val 0))) :  ∀ s, s ≤ t₀ → f s < (a.val 0) := by
  induction t₀ with
  | zero =>
    intro s; intro;
    rename s ≤ 0 => a_1
    have : s = 0 := Nat.le_zero.mp a_1
    rw [this,ish.h00]; exact (a.pos 0)
  | succ n ih =>
    intro s hs; cases hs
    rename ℕ => n
    rename  (∀ s ≤ n, f s ≠ PF.val a 0) → ∀ s ≤ n, f s < PF.val a 0 => n_ih
    let g := n_ih (fun _ hsn => ht₀ _ (Nat.le_step hsn)) n (le_refl _)
    by_cases h : (f n = 0);
    let gg := ish.h0 n h; cases gg;
    rename f (Nat.succ n) = 1 % PF.val a 0 => h_1
    rw [h_1]

    let G := ht₀ n.succ (le_refl _); rw [h_1] at G
    exact Nat.mod_lt _ (a.pos 0)

    let ggg := ht₀ n.succ (le_refl _); exfalso;
    rename f (Nat.succ n) = PF.val a 0 => h_1
    exact ggg h_1

    let g1 := ish.h1 (f n) n (by
      contrapose h; simp; simp at h
      exact zero_of_mod (Nat.one_le_iff_ne_zero.mpr (Nat.not_eq_zero_of_lt (a.pos 0))) h g
    ) (Nat.mod_eq_of_lt g).symm
    rw [g1]

    exact Nat.mod_lt _ ((a.pos 0))
    let g := ih (by {intro _ hsn; exact ht₀ _ (Nat.le_step hsn)}) s (by tauto)
    exact g


-- Our running example will be the "cursive" NFA that has a cycle of length (a.val 0) and then a cycle of length (a.val 1).
-- We implement it as an infinite NFA where only the first (a.val 0)+(a.val 1) states are reachable,
-- in order to avoid type casting issues.


-- ideally, define this over PF c for any c
def cursive_step (a : PF 2)  : ℕ → Set (ℕ) :=
  fun q ↦ ite (q=0)
  {1 % (a.val 0),(a.val 0)}
  (ite (q<(a.val 0)) {(q+1) % (a.val 0)} {(((a.val 0) + (((q-(a.val 0)+1) % (a.val 1)))):ℕ)})

def CursiveNFA (a : PF 2) : NFA (Fin 1) (ℕ) where
  step := fun q _ ↦ cursive_step a q
  start := {0}
  accept := {a.val 0}

def walk_in_NFA (f : ℕ → ℕ) (M : NFA (Fin 1) ℕ) :=
  f 0 ∈ M.start ∧ ∀ k, f k.succ ∈ M.step (f k) 0

def curs_walks (a : PF 2) (f : ℕ → ℕ) := walk_in_NFA f (CursiveNFA a)

structure CursiveWalkInstance (c: PNat) where
  length : PNat
  cycleLength : PF c

def CursiveWalk : DecisionProblem where
  Instance := CursiveWalkInstance 2
  Space := fun _ ↦ (ℕ → ℕ)
  Solution := fun ⟨i,w⟩ ↦ curs_walks i.cycleLength w ∧  w i.length = i.cycleLength.val 0

structure CursiveWalkSolution (i : CursiveWalkInstance 2) where
  w : ℕ → ℕ
  walks : curs_walks (i.cycleLength) w
  timed : w i.length = i.cycleLength.val 0


theorem generalh2s' (a : PF 2) (F: ℕ → ℕ) (hw: curs_walks a F) :
    ∀ (i t : ℕ), (F t) = a.val 0 + i % a.val 1 → (F (Nat.succ t)) = a.val 0 + Nat.succ i % a.val 1 := by
  intro i t hit; let g := hw.2 t; unfold curs_walks at g; rw [hit] at g
  unfold CursiveNFA at g;
  unfold cursive_step at g; simp at g;
  have : a.val 0 ≠ 0 := by
    intro hcontra;
    let ha₀pos := a.pos 0
    rw [hcontra] at ha₀pos
    exact LT.lt.false ha₀pos
  have : ¬ ( a.val 0 = 0 ∧ i % a.val 1 = 0) := by {intro hcontra; exact this hcontra.1}
  rw [if_neg this] at g
  rw [g]

theorem getish' (F:ℕ → ℕ) (a : PF 2) (hw : curs_walks a F) : cursiveish a (λ n ↦ (F n)) where
    h00 := by
      have : F 0 = 0 := Set.eq_of_mem_singleton hw.1
      rw [this]
    h0 := by
      intro t ht; let g := hw.2 t
      rw [ht] at g
      cases g <;> tauto
    h1 := by
      intro i t hi ht;
      unfold curs_walks at hw; unfold CursiveNFA at hw
      unfold cursive_step at hw;
      unfold walk_in_NFA at hw
      simp at hw
      let g := hw.2 t
      have : F t ≠ 0 := Eq.trans_ne ht hi
      rw [if_neg this] at g
      have : i % (a.val 0) < (a.val 0) := Nat.mod_lt _ (a.pos 0)
      rw [← ht] at this; rw [if_pos this] at g
      simp at g; rw [Nat.add_mod,ht] at g
      rw [g]; simp
    h2s := generalh2s' _ _ hw

def walk_' (a : PF 2) (k:ℕ) (i: ℕ) : ℕ :=
  ite (i ≥ ((a.val 0)*k).succ)
  ((a.val 0) + ((i-((a.val 0)*k).succ) % (a.val 1)))
  (i % (a.val 0))

theorem walk__injective_lt' (a : PF 2) {k₁ k₂ : ℕ} (hk : k₁ < k₂) : walk_' a k₁ ≠ walk_' a k₂ := by
  intro hcontra
  have : ∀ n, walk_' a k₁ n = walk_' a k₂ n := fun n ↦ congrFun hcontra n
  let g := this (a.val 0 * k₁).succ
  unfold walk_' at g;
  simp at g
  have h₀: ¬ (k₂) ≤ (k₁) := Nat.not_le.mpr hk
  have : ¬ (a.val 0 * k₂) ≤ (a.val 0 * k₁) := by
    intro hcontra
    have : k₂ ≤ k₁ := Nat.le_of_mul_le_mul_left hcontra ((a.pos 0))
    exact h₀ this
  rw [if_neg this] at g
  have : ∀ x : ℕ, x % a.val 0 < a.val 0 := by {intro x;exact Nat.mod_lt _ (a.pos 0)}
  let G := this (a.val 0*k₁).succ;
  rw [← g] at G; exact LT.lt.false G

-- This one should be "private":
theorem keep_arriving' (a : PF 2) (p : Fin 2 → ℕ) :
    walk_' a (p 0) (a.val 0*(p 0) + 1 + a.val 1*(p 1)) = a.val 0 := by
    let k := p 0
    let l := p 1
    unfold walk_'; rw [if_pos _]; simp;
    rw [add_assoc]
    have : PF.val a 0 * k + (1 + PF.val a 1 * l) = (PF.val a 0 * k + (PF.val a 1 * l)) + 1 := by ring
    rw [this,← Nat.succ_eq_add_one]
    apply Nat.succ_le_succ_iff.mpr
    exact Nat.le_add_right _ _

-- This one should be "public" in order to reduce use of moveOne:
theorem keep_arriving (a : PF 2) (p : Fin 2 → ℕ) :
    walk_' a (p 0) (Matrix.dotProduct a.val p).succ = a.val 0 := by
  rw [moveOne]
  exact keep_arriving' _ _

theorem unique_walk_cursive_helper' {a : PF 2} {w : ℕ → ℕ} {k : ℕ}
    (hw: curs_walks a w)
    (hwk: w (a.val 0*k).succ = a.val 0 ∧ ∀ n < (a.val 0*k).succ, w n ≠ a.val 0) :
    ∀ n < (a.val 0*k).succ, w n < a.val 0 := by
  intro n
  induction n with
  | zero =>
    intro; rw [hw.1]; exact (a.pos 0)
  | succ n_1 ih =>
    intro hn_1; by_cases h : (n_1 < (a.val 0*k).succ)
    let G:= hwk.2 n_1.succ hn_1
    unfold curs_walks at hw; unfold CursiveNFA at hw; unfold cursive_step at hw
    unfold walk_in_NFA at hw
    simp at hw;
    let g := hw.2 n_1; let gg := ih h; rw [if_pos gg] at g
    by_cases h' : (w n_1=0); rw [if_pos h'] at g; simp at g; cases g with
    | inl h => rw [h]; exact Nat.mod_lt _ (a.pos 0)
    | inr h => exfalso; exact G h
    let H := hw.2 n_1
    rw [if_neg h',if_pos gg] at H; simp at H; rw [H]; exact Nat.mod_lt _ (a.pos 0)

    let g := hw.2 n_1; unfold CursiveNFA at g; unfold cursive_step at g; simp at g
    have : n_1 < (a.val 0*k).succ := Nat.lt_of_succ_lt hn_1
    let G := ih this; rw [if_pos G] at g
    have : w n_1 ≠ 0 := by
      intro hcontra; rw [if_pos hcontra] at g; simp at g; cases g
      exact h this; let H := hwk.2 n_1.succ hn_1
      tauto
    rw [if_neg _] at g; simp at g; rw [g]; exact Nat.mod_lt _ (a.pos 0); exact this

theorem afterwards {a : PF 2}{w: ℕ → ℕ}{k n: ℕ} (hnks: n ≥ (a.val 0 * k).succ)
    (g: w (Nat.succ n) ∈ NFA.step (CursiveNFA a) (a.val 0 + (n - Nat.succ (a.val 0 * k)) % a.val 1) 0) :
    w (Nat.succ n) = a.val 0 + (n - a.val 0 * k) % a.val 1 := by
  have h₄: n - Nat.succ (a.val 0 * k) + 1 = n - a.val 0 * k :=
    sub_succ_add_one hnks

  unfold CursiveNFA at g; unfold cursive_step at g; simp at g; rw [← h₄];
  have : ¬ (a.val 0 = 0 ∧ (n - Nat.succ (a.val 0 * k)) % a.val 1 = 0) := by
    intro hcontra
    have ha₀pos := a.pos 0
    rw [hcontra.1] at ha₀pos
    omega
  rw [if_neg this] at g
  exact g

theorem unique_walk_CursiveNFA {a : PF 2} {w : ℕ → ℕ} {k : ℕ} (hw: curs_walks a w)
    (hwk': w (a.val 0*k).succ = a.val 0 ∧ ∀ n < (a.val 0*k).succ, w n ≠ a.val 0) : w = walk_' a k := by
  have hwk : w ((a.val 0)*k).succ = (a.val 0) ∧ ∀ n < ((a.val 0)*k).succ, w n < (a.val 0) :=
    ⟨ hwk'.1, (unique_walk_cursive_helper' hw hwk')⟩
  apply funext; intro x
  induction x with
  | zero =>
    unfold curs_walks at hw; unfold walk_'
    rw [if_neg _]; simp; exact hw.1
    omega
  | succ n ih =>
    by_cases hnk : (n.succ ≥ ((a.val 0)*k).succ)
    unfold walk_'; rw [if_pos _]; simp; let g := hw.2 n; rw [ih] at g
    unfold walk_' at g; by_cases hnks : (n ≥ ((a.val 0)*k).succ )


    rw [if_pos hnks] at g; exact afterwards hnks g

    have hn2k: n = (a.val 0)*k := (Nat.eq_of_lt_succ_of_not_lt hnk hnks).symm
    rw [hn2k]; simp; rw [if_neg hnks] at g; have : (a.val 0) ∣ n := Dvd.intro k (id hn2k.symm)
    have : n % (a.val 0) = 0 := Nat.mod_eq_zero_of_dvd this
    rw [this] at g
    cases g with
    | inl h => exact hwk.1
    | inr h => rw [hn2k] at h; exact h
    exact hnk
    unfold walk_';
    rw [if_neg hnk]
    unfold walk_' at ih

    have hnss : n.succ < ((a.val 0)*k).succ := Nat.not_le.mp hnk
    have hnlt : n < ((a.val 0)*k).succ := Nat.lt_of_succ_lt hnss
    have hn2k : ¬ n ≥ ((a.val 0)*k).succ := by omega
    rw [if_neg hn2k] at ih; unfold curs_walks at hw
    let g₂ := hw.2 n; rw [ih] at g₂

    unfold CursiveNFA at g₂; unfold cursive_step at g₂
    simp at g₂
    have : n % (a.val 0) < (a.val 0) := Nat.mod_lt _ ((a.pos 0))
    rw [if_pos this] at g₂; by_cases h : (n % (a.val 0) = 0);
    rw [if_pos h] at g₂
    have h1: n.succ % (a.val 0) = 1 % (a.val 0) := by
      rw [Nat.succ_eq_add_one,Nat.add_mod,h,]
      simp
    rw [h] at ih; let g := hw.2 n; rw [ih] at g
    unfold CursiveNFA at g; unfold cursive_step at g
    simp at g
    cases g₂ with
    | inl h =>
      rw [h1]
      cases g with
      | inl h => exact h
      | inr h => tauto
    | inr h_1 =>
      simp at h_1
      rw [h1]
      exfalso
      let G := hwk'.2 n.succ hnss
      exact G h_1
    rw [if_neg h] at g₂; simp at g₂; exact g₂

theorem ne_of_le' (a : PF 2) {w : ℕ → ℕ} {t₀:ℕ} (hw: curs_walks a w)
    (ht₀ : w (Nat.succ t₀) = a.val 0 ∧ ∀ (v : ℕ), w (Nat.succ v) = a.val 0 → t₀ ≤ v) :
    ∀ (s : ℕ), s ≤ t₀ → (w s) ≠ a.val 0 := by
  intro s hs
  cases s with
  | zero =>
    intro hcontra
    let gg := hw.1
    simp at gg
    rw [gg] at hcontra
    let ha₀pos := a.pos 0
    rw [← hcontra] at ha₀pos
    exact LT.lt.false ha₀pos
  | succ n =>
    intro hcontra
    let g := ht₀.2 n (hcontra)
    have : n < n := Nat.succ_le.mp (le_trans hs g)
    exact LT.lt.false this

theorem ne_first' (a : PF 2) {w : ℕ → ℕ} {t₀ k:ℕ} (hk: t₀ = a.val 0 * k) (hw: curs_walks a w)
    (ht₀ : w (Nat.succ t₀) = a.val 0 ∧ ∀ (v : ℕ), w (Nat.succ v) = a.val 0 → t₀ ≤ v) :
    w (a.val 0*k).succ = a.val 0 ∧ ∀ n, n < (a.val 0 * k).succ → w n ≠ a.val 0 := by
  constructor; rw [hk] at ht₀; exact ht₀.1
  intro u hu hu2; cases u with
  | zero =>
    let g := hw.1
    rw [hu2] at g
    let ha₀pos := a.pos 0
    rw [← g] at ha₀pos
    exact LT.lt.false ha₀pos
  | succ n =>
    have : (a.val 0)*k < (a.val 0)*k := calc
      _ = t₀  := id hk.symm
      _ ≤ n   := ht₀.2 n hu2
      _ < (a.val 0)*k := Nat.succ_lt_succ_iff.mp hu
    exact LT.lt.false this

-- January 6: Why not this?
def getk (i : CursiveWalk.Instance) (s : Solution_of i) : { k : ℕ // s.1 = walk_' i.cycleLength (k)} := by
  let W := s; let w := W.1; let hw := W.2.1; let hu := W.2.2
  let u := i.length.val.pred
  have : u.succ = i.length.val := PNat.natPred_add_one _
  rw [← this] at hu
  let ⟨t₀,ht₀⟩  := (find_spec_le (λ s ↦ w (Nat.succ s) = (i.cycleLength.val 0)) u hu)
  let ish := getish' w i.cycleLength hw
  have hlt :  ∀ (s : ℕ), s ≤ t₀ → (w s) < (i.cycleLength.val 0) := by {
    intro _ hs
    exact strengthen ish (ne_of_le' i.cycleLength hw ht₀) _ hs
  }
  have h02 : t₀ % (i.cycleLength.val 0) = 0 % (i.cycleLength.val 0) :=
    get_a0dvd i.cycleLength ish _ hlt ht₀.1
  let k := (get_equation' (Nat.zero_le _) h02).1
  exists k

  let a := i.cycleLength;

  let hk := (get_equation' (Nat.zero_le _) h02).2

  rw [zero_add] at hk
  exact unique_walk_CursiveNFA hw (ne_first' a hk hw ht₀)

/-- December 30. This needs a corresponding getk2 version, getk2'' -/
def getk1'' (i : CursiveWalk.Instance) (s : Solution_of i) : ℕ  := by
  let W := s; let w := W.1; let hw := W.2.1; let hu := W.2.2
  let u := i.length.val.pred
  have : u.succ = i.length.val := PNat.natPred_add_one _
  rw [← this] at hu
  let ⟨t₀,ht₀⟩  := (find_spec_le (λ s ↦ w (Nat.succ s) = (i.cycleLength.val 0)) u hu)
  let ish := getish' w i.cycleLength hw
  have hlt :  ∀ (s : ℕ), s ≤ t₀ → (w s) < (i.cycleLength.val 0) := by {
    intro _ hs
    exact strengthen ish (ne_of_le' i.cycleLength hw ht₀) _ hs
  }
  have h02 : t₀ % (i.cycleLength.val 0) = 0 % (i.cycleLength.val 0) :=
    get_a0dvd i.cycleLength ish _ hlt ht₀.1
  let k := (get_equation' (Nat.zero_le _) h02).1
  exact k

theorem getk2'' (i : CursiveWalk.Instance) (s : Solution_of i) :
    s.1 = walk_' i.cycleLength (getk1'' i s) := by
  let W := s; let w := W.1; let hw := W.2.1; let hu := W.2.2
  let a := i.cycleLength; let u := i.length.val.pred
  have : u.succ = i.length.val := PNat.natPred_add_one _
  rw [← this] at hu

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
  exact unique_walk_CursiveNFA hw (ne_first' a hk hw ht₀)


def getk1  {u:ℕ} (a : PF 2) (W : { W : ℕ → ℕ // curs_walks a W ∧ W (Nat.succ u) = a.val 0}) : ℕ := by
  let w := W.1
  let hw := W.2.1
  let hu := W.2.2
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

def getk1' (a : PF 2) {w : ℕ → ℕ} {u:ℕ} (hw: curs_walks a w) (hu: w (Nat.succ u) = a.val 0) : ℕ := by
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

theorem getk2' (a : PF 2) {w : ℕ → ℕ} {u:ℕ} (hw: curs_walks a w) (hu: w (Nat.succ u) = a.val 0) :
    w = walk_' a (getk1' a hw hu) := by
  let t₀ := (find_spec_le (λ s ↦ w (Nat.succ s) = (a.val 0)) u hu).1
  let ht₀ := (find_spec_le (λ s ↦ w (Nat.succ s) = (a.val 0)) u hu).2
  let ish := getish' w a hw
  have hlt :  ∀ (s : ℕ), s ≤ t₀ → (w s) < (a.val 0) := fun _ hs => strengthen ish (ne_of_le' a hw ht₀) _ hs
  have h02 : t₀ % (a.val 0) = 0 % (a.val 0) := get_a0dvd a ish _ hlt ht₀.1
  let hk := (get_equation' (Nat.zero_le _) h02).2
  rw [zero_add] at hk
  exact unique_walk_CursiveNFA hw (ne_first' a hk hw ht₀)

theorem l_unique' (a : PF 2) {k l₁ l₂ : ℕ} (he: a.val 0*k + 1 + a.val 1*l₁ = a.val 0*k + 1 + a.val 1*l₂) :
    l₁=l₂ :=  by
  let ha₁pos := a.pos 1
  exact Nat.eq_of_mul_eq_mul_left ha₁pos (Nat.add_left_cancel he)

theorem l_unique (a : PF 2) (k l₁ l₂ : ℕ)
    (he: Matrix.dotProduct a.val (λ i ↦ [k,l₁].get i)
       = Matrix.dotProduct a.val (λ i ↦ [k,l₂].get i)) : l₁=l₂ :=  by
  unfold Matrix.dotProduct at he
  simp at he
  cases he with
  | inl h =>
  exact h
  | inr h =>
  exfalso
  let ha₁pos := a.pos 1
  rw [h] at ha₁pos
  exact LT.lt.false ha₁pos

def getl' (a : PF 2) {k n:ℕ} (hmod₀: walk_' a k n = a.val 0) :
    {l : ℕ // n = a.val 0*k + 1 + a.val 1*l} := by
  have hge : n ≥ (a.val 0)*k + 1 := by
    unfold walk_' at hmod₀; by_contra hcontra; rw [if_neg hcontra] at hmod₀
    have : n % (a.val 0) < (a.val 0) := Nat.mod_lt _ (a.pos 0); rw [hmod₀] at this
    exact LT.lt.false this
  let L := n - ((a.val 0)*k+1)
  have hL : n = (a.val 0)*k + 1 + L := (functional_eq_add_of_le hge).2
  rw [hL] at hmod₀; unfold walk_' at hmod₀;
  simp at hmod₀
  have : L = n - ((a.val 0)*k+1) := rfl;
  let l := L / (a.val 1)
  have : n = (a.val 0) * k + 1 + (a.val 1) * l := by
    have h₁: (L/(a.val 1))*(a.val 1) = L := by
      refine Nat.div_mul_cancel ?H
      exact Nat.dvd_of_mod_eq_zero hmod₀
    have h₂: L = (a.val 1) * (L / (a.val 1)) := by {rw [mul_comm] at h₁; exact h₁.symm}
    rw [← h₂]
    exact hL
  exact ⟨l,this⟩

def getl (a : PF 2) {k n:ℕ} (hmod₀: walk_' a k n = a.val 0) :
    {l : ℕ // n = Nat.succ (Matrix.dotProduct a.val (λ i ↦ [k,l].get i))} := by
  let ⟨l,lproof⟩ := getl' a hmod₀
  exists l
  rw [lproof,moveOne]
  simp

theorem walk_walks' (a : PF 2) (k:ℕ) : curs_walks a (walk_' a k) := by
  constructor; unfold walk_'
  have : ¬ 0 ≥ Nat.succ ((a.val 0) * k) := of_decide_eq_false rfl
  rw [if_neg this]
  exact rfl
  intro k_1
  induction k_1 with
  | zero =>
    unfold walk_'
    have : ¬ Nat.zero ≥ Nat.succ ((a.val 0) * k) := of_decide_eq_false rfl
    rw [if_neg this]
    by_cases h : (k=0)
    have : Nat.succ Nat.zero ≥ Nat.succ ((a.val 0) * k)
      := Nat.succ_le_succ (Nat.le_zero.mpr (mul_eq_zero_of_right (a.val 0) h))
    rw [if_pos this,h]; simp; right; exact rfl
    have h₁: ¬ Nat.zero = ((a.val 0) * k) := by
      intro hcontra
      cases Nat.zero_eq_mul.mp hcontra
      have : 0 < (a.val 0) := (a.pos 0)
      omega
      omega
    have h₂: ¬ Nat.zero ≥ ((a.val 0) * k) := by
      intro hcontra
      exact h₁ (id (Nat.le_zero.mp hcontra).symm)
    have : ¬ Nat.succ Nat.zero ≥ Nat.succ ((a.val 0) * k) := by
      intro hcontra
      exact h₂ (Nat.lt_succ.mp hcontra)
    rw [if_neg this]; left; rfl
  | succ n ih =>
    unfold walk_'
    by_cases hss : (Nat.succ (Nat.succ n) ≥ Nat.succ ((a.val 0) * k))
    rw [if_pos hss]
    by_cases hnk : (Nat.succ n ≥ Nat.succ ((a.val 0) * k))
    rw [if_pos hnk]
    simp
    have h₁ : n ≥ (a.val 0)*k := Nat.succ_le_succ_iff.mp hnk
    have h₂ : n + 1 - (a.val 0)*k = n - (a.val 0)*k + 1 := Nat.sub_add_comm h₁

    unfold CursiveNFA; unfold cursive_step; simp; rw [h₂]

    have : ¬ (a.val 0 = 0 ∧ (n - a.val 0 * k) % a.val 1 = 0) := by
      intro hcontra
      have : 0 < 0 := by
        let ha₀pos := a.pos 0
        rw [hcontra.1] at ha₀pos
        exact ha₀pos
      exact LT.lt.false this
    rw [if_neg this]
    simp
    rw [if_neg hnk];
    have h₅ : n.succ = (a.val 0)*k := (Nat.eq_of_lt_succ_of_not_lt hss hnk).symm
    have h₃: n+1 - (a.val 0)*k = 0 := tsub_eq_of_eq_add_rev h₅
    simp
    rw [h₃]
    simp at h₅
    rw [h₅]
    simp;
    right
    exact rfl
    -- early times:
    rw [if_neg hss]
    have : ¬ Nat.succ n ≥ Nat.succ ((a.val 0) * k) := by
      intro hcontra
      have : n.succ ≤ n.succ.succ := Nat.le_succ (Nat.succ n)
      exact hss (le_trans hcontra this)
    rw [if_neg this]; by_cases h : (n.succ % (a.val 0) = 0); rw [h];
    have : n.succ.succ % (a.val 0) = 1 % (a.val 0) := by
      rw [Nat.succ_eq_add_one,Nat.add_mod,h,];simp
    rw [this]; left; exact rfl

    unfold CursiveNFA; unfold cursive_step; simp
    rw [if_neg h]; have : n.succ % (a.val 0) < (a.val 0) := Nat.mod_lt _ (a.pos 0)
    rw [if_pos this]; simp

theorem walk__injective' (a : PF 2) (k₁ k₂ : ℕ) (he : walk_' a k₁ = walk_' a k₂) : k₁ = k₂ := by
  contrapose he
  cases Ne.lt_or_lt he with
  | inl h => exact walk__injective_lt' a h
  | inr h => exact (walk__injective_lt' a h).symm
