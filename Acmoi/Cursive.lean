import Acmoi.Ch7Tools
import Acmoi.DecisionProblem
/-!

  # Cursive NFAs

-/


/-

 # Properties not requiring positivity

-/

open Nat

-- Some properties of walks in cursive NFAs:
structure cursiveFun (a :Fin 2 → ℕ) (f:ℕ → ℕ) where
  init : f 0 = 0
  branch (t) (h₀ : f t = 0) :     f t.succ = 1 % (a 0)
                                ∨ f t.succ = a 0
  loop₁ (i t) (h : i % a 0 ≠ 0) : f t      = i      % a 0
                                → f t.succ = i.succ % a 0
  loop₂ (i t):                    f t      = a 0 + (i      % a 1)
                                → f t.succ = a 0 + (i.succ % a 1)

theorem walk_mod_a0' (a : Fin 2 → ℕ) {f:ℕ → ℕ}(c : cursiveFun a f)(t: ℕ)
    (hs : ∀ s, s ≤ t → f s < (a 0)) : f t = t % (a 0) := by
  induction  t with
  | zero =>
    rw [c.init]
    rfl
  | succ n ih =>
    have hfn : f n = n % (a 0) := ih (fun s hsn ↦ hs s (Nat.le_step hsn))
    by_cases hna : (n % (a 0) = 0)
    · rw [hna] at hfn
      have g := c.branch n hfn
      cases g with
      | inl h =>
      · rw [h]
        have : (n+1) % (a 0) = (n % (a 0) + 1 % (a 0)) % (a 0) := Nat.add_mod _ _ _
        rw [hna,zero_add,Nat.mod_mod] at this; exact id this.symm
      | inr h =>
      · rw [h]; exfalso; have gg := hs n.succ (le_refl _)
        omega
    · exact c.loop₁ n n hna hfn


/-
Our running example will be the "cursive" NFA that has a cycle of length (a.val 0) and then a cycle of length (a.val 1).
We implement it as an infinite NFA where only the first (a.val 0)+(a.val 1) states are reachable,
in order to avoid type casting issues.
-/

-- ideally, define this over Fin c → ℕ for any c
def cursive_step' (a : Fin 2 → ℕ)  : ℕ → Set ℕ :=
  fun q ↦ ite (q = 0) {1 % a 0, a 0}
  (ite (q < a 0) {(q+1) % a 0} {a 0 + ((q-(a 0)+1) % a 1)})


def CursiveNFA (a : Fin 2 → ℕ) : NFA (Fin 1) (ℕ) where
  step := fun q _ ↦ cursive_step' a q
  start := {0}
  accept := {a 0}

def walk_in_NFA (f : ℕ → ℕ) (M : NFA (Fin 1) ℕ) :=
  f 0 ∈ M.start ∧ ∀ k, f k.succ ∈ M.step (f k) 0

def curs_walks (a : Fin 2 → ℕ) (f : ℕ → ℕ) := walk_in_NFA f (CursiveNFA a)

def cwalk (a : Fin 2 → ℕ) (k:ℕ) (i: ℕ) : ℕ :=
      ite (i ≥ (a 0 * k).succ)
  (a 0 + ((i - (a 0 * k).succ) % a 1)) (i % a 0)

-- This one should be "private":
theorem keep_arriving' (a : Fin 2 → ℕ) (p : Fin 2 → ℕ) :
    cwalk a (p 0) (a 0*(p 0) + 1 + a 1*(p 1)) = a 0 := by
    unfold cwalk
    rw [if_pos _]
    · simp
    · omega

-- This one should be "public" in order to reduce use of moveOne:
theorem keep_arriving (a : Fin 2 → ℕ) (p : Fin 2 → ℕ) :
    cwalk a (p 0) (Matrix.dotProduct a p).succ = a 0 := by
  rw [moveOne]
  exact keep_arriving' _ _


/-

# Properties requiring positivity
-/

/--
The following data structure PF is useful.
  The alternative would be Fin c → PNat
  but this way we can talk about
  `a.val 0`
  instead of the cumbersome
  `(a 0).val`.
  And we can write `Matrix.dotProduct a.val p`
  instead of `Matrix.dotProduct (fun i ↦ a.val) p`.
-/
structure PF (c:ℕ) where
  val : Fin c → ℕ
  pos : ∀ i, 0 < val i

theorem get_a0dvd (a : PF 2) {f:ℕ → ℕ} (c : cursiveFun a.val f) (t : ℕ)
    (h₀ : ∀ s, s ≤ t → f s < a.val 0)
    (h₁ : f t.succ = a.val 0) : t % a.val 0 = 0 := by
  have ftt : f t = t % (a.val 0) := walk_mod_a0' a.val c t h₀
  by_contra hc
  have g := c.loop₁ t t hc ftt
  have ht1: t.succ % (a.val 0) = (a.val 0) := Eq.trans g.symm h₁
  have ht2: t.succ % (a.val 0) < (a.val 0) := Nat.mod_lt _ (a.pos 0)
  omega


theorem before_nexus {a : PF 2}  {t₀ : ℕ} {f : ℕ → ℕ} (c : cursiveFun a.val f)
    (ht₀ : (∀ s, s ≤ t₀ → f s ≠ a.val 0)) :
            ∀ s, s ≤ t₀ → f s < a.val 0 := by
  induction t₀ with
  | zero =>
    intro s hs
    rw [Nat.le_zero.mp hs, c.init]
    exact a.pos 0
  | succ n ih =>
    intro s hs
    cases hs with
    | refl =>
      by_cases h : f n = 0
      · cases c.branch n h with
        | inl h₀ => exact h₀ ▸ Nat.mod_lt _ (a.pos 0)
        | inr h₀ => exact (ht₀ n.succ (le_refl _) h₀).elim
      · specialize ih (fun _ hsn => ht₀ _ (Nat.le_step hsn)) n (le_refl _)
        have : f n % a.val 0 ≠ 0 := by
          contrapose h
          simp only [Decidable.not_not] at h ⊢
          exact zero_of_mod (Nat.one_le_iff_ne_zero.mpr (Nat.not_eq_zero_of_lt (a.pos 0))) h ih
        rw [c.loop₁ (f n) n this (Nat.mod_eq_of_lt ih).symm]
        exact Nat.mod_lt _ ((a.pos 0))
    | step h₀ => exact ih (fun h hsn => ht₀ h (Nat.le_step hsn)) s h₀


structure CursiveWalkInstance (c: PNat) where
  length : PNat
  cycleLength : PF c

def CursiveWalk : DecisionProblem where
  Instance := CursiveWalkInstance 2
  Space := fun _ ↦ (ℕ → ℕ)
  Solution := fun i w ↦ curs_walks i.cycleLength.val w ∧  w i.length = i.cycleLength.val 0

structure CursiveWalkSolution (i : CursiveWalkInstance 2) where
  w : ℕ → ℕ
  walks : curs_walks (i.cycleLength.val) w
  timed : w i.length = i.cycleLength.val 0


theorem general_loop₂ (a : PF 2) (F : ℕ → ℕ) (hw : curs_walks a.val F)
    (i t : ℕ) (h : F t      = a.val 0 + i      % a.val 1) :
                   F t.succ = a.val 0 + i.succ % a.val 1 := by
  have g := hw.2 t
  rw [h] at g
  have := a.pos 0
  simp [CursiveNFA, cursive_step'] at g
  have : ¬ ( a.val 0 = 0 ∧ i % a.val 1 = 0) := by omega
  rw [if_neg this] at g
  rw [g]

theorem getc' (F:ℕ → ℕ) (a : PF 2) (hw : curs_walks a.val F) : cursiveFun a.val (fun n ↦ (F n)) where
    init := by rw [Set.eq_of_mem_singleton hw.1]
    branch := by
      intro t ht
      have g := hw.2 t
      rw [ht] at g
      cases g <;> tauto
    loop₁ := by
      intro i t hi ht
      unfold curs_walks CursiveNFA cursive_step' walk_in_NFA at hw
      simp at hw
      have g := hw.2 t
      have : F t ≠ 0 := Eq.trans_ne ht hi
      rw [if_neg this] at g
      have : i % (a.val 0) < (a.val 0) := Nat.mod_lt _ (a.pos 0)
      rw [← ht] at this; rw [if_pos this] at g
      simp at g; rw [Nat.add_mod,ht] at g
      rw [g]; simp
    loop₂ := general_loop₂ _ _ hw


theorem walkInjective (a : PF 2) {k₁ k₂ : ℕ} (hk : k₁ < k₂) : cwalk a.val k₁ ≠ cwalk a.val k₂ := by
  intro hc
  have : ¬ (a.val 0 * k₂) ≤ (a.val 0 * k₁) := by
    intro hc
    have : k₂ ≤ k₁ := Nat.le_of_mul_le_mul_left hc ((a.pos 0))
    omega
  have hc := congrFun hc (a.val 0 * k₁).succ
  simp [cwalk] at hc
  rw [if_neg this] at hc
  have h := Nat.mod_lt (a.val 0 * k₁).succ (a.pos 0)
  rw [← hc] at h
  omega


theorem unique_walk_cursive_helper' {a : PF 2} {w : ℕ → ℕ} {k : ℕ}
    (hw: curs_walks a.val w)
    (hwk: w (a.val 0*k).succ = a.val 0 ∧ ∀ n < (a.val 0*k).succ, w n ≠ a.val 0) :
    ∀ n < (a.val 0*k).succ, w n < a.val 0 := by
  intro n
  induction n with
  | zero =>
    intro; rw [hw.1]; exact a.pos 0
  | succ n ih =>
    have hw := hw.2
    simp [curs_walks, CursiveNFA, cursive_step', walk_in_NFA] at hw
    specialize hw n
    intro hn
    by_cases h : n < (a.val 0*k).succ
    · specialize ih h
      rw [if_pos ih] at hw
      by_cases h' : (w n=0)
      · rw [if_pos h'] at hw
        simp at hw
        cases hw with
        | inl h => rw [h]; exact Nat.mod_lt _ (a.pos 0)
        | inr h => exact (hwk.2 n.succ hn h).elim
      · rw [if_neg h'] at hw
        simp at hw
        rw [hw]
        exact Nat.mod_lt _ (a.pos 0)
    · have := Nat.lt_of_succ_lt hn
      specialize ih this
      specialize h this
      rw [if_pos ih, if_neg h.elim] at hw
      exact hw ▸ Nat.mod_lt _ (a.pos 0)

theorem afterwards {a : PF 2}{w: ℕ → ℕ}{k n: ℕ} (hnks: n ≥ (a.val 0 * k).succ)
    (g: w n.succ ∈ NFA.step (CursiveNFA a.val) (a.val 0 + (n - Nat.succ (a.val 0 * k)) % a.val 1) 0) :
    w (Nat.succ n) = a.val 0 + (n - a.val 0 * k) % a.val 1 := by
  have := a.pos 0
  unfold CursiveNFA cursive_step' at g
  simp at g
  rw [if_neg (by omega)] at g
  rw [← sub_succ_add_one hnks]
  exact g

theorem unique_walk_CursiveNFA {a : PF 2} {w : ℕ → ℕ} {k : ℕ} (hw: curs_walks a.val w)
    (hwk₀: w (a.val 0*k).succ = a.val 0) (hwk₁: ∀ n < (a.val 0*k).succ, w n ≠ a.val 0) :
    w = cwalk a.val k := by
  apply funext; intro x
  induction x with
  | zero =>
    unfold curs_walks at hw; unfold cwalk
    rw [if_neg (by omega)]
    simp
    exact hw.1
  | succ n ih =>
    have hw := hw.2
    specialize hw n
    by_cases hnk : n.succ ≥ ((a.val 0)*k).succ
    · unfold cwalk
      rw [if_pos hnk]; simp
      rw [ih] at hw
      unfold cwalk at hw
      by_cases hnks : n ≥ ((a.val 0)*k).succ
      · rw [if_pos hnks] at hw
        exact afterwards hnks hw
      · have hn2k: n = (a.val 0) * k := (Nat.eq_of_lt_succ_of_not_lt hnk hnks).symm
        rw [hn2k]
        simp
        rw [if_neg hnks] at hw
        have : (a.val 0) ∣ n := Dvd.intro k (id hn2k.symm)
        have : n % (a.val 0) = 0 := Nat.mod_eq_zero_of_dvd this
        rw [this] at hw
        cases hw with
        | inl h => exact hwk₀
        | inr h => rw [hn2k] at h; exact h
    · unfold cwalk
      rw [if_neg hnk]
      unfold cwalk at ih
      rw [if_neg (by omega)] at ih
      rw [ih] at hw
      simp [CursiveNFA, cursive_step'] at hw
      have : n % (a.val 0) < (a.val 0) := Nat.mod_lt _ (a.pos 0)
      rw [if_pos this] at hw
      by_cases h : n % a.val 0 = 0
      · rw [if_pos h] at hw
        have h1: n.succ % (a.val 0) = 1 % (a.val 0) := by
          rw [Nat.succ_eq_add_one,Nat.add_mod,h,]
          simp
        rw [h] at ih
        cases hw with
        | inl h =>
          rw [h1]
          exact h
        | inr h_1 =>
          simp at h_1
          rw [h1]
          exact (hwk₁ n.succ (Nat.not_le.mp hnk) h_1).elim
      · rw [if_neg h] at hw
        simp at hw
        exact hw

theorem ne_of_le' (a : PF 2) {w : ℕ → ℕ} {t₀:ℕ} (hw: curs_walks a.val w)
    (ht₀ : w (Nat.succ t₀) = a.val 0 ∧ ∀ (v : ℕ), w (Nat.succ v) = a.val 0 → t₀ ≤ v) :
    ∀ (s : ℕ), s ≤ t₀ → (w s) ≠ a.val 0 := by
  intro s hs
  cases s with
  | zero =>
    intro hc
    have gg := hw.1
    simp at gg
    rw [gg] at hc
    have ha₀pos := a.pos 0
    rw [← hc] at ha₀pos
    exact LT.lt.false ha₀pos
  | succ n =>
    intro hc
    have g := ht₀.2 n (hc)
    have : n < n := Nat.succ_le.mp (le_trans hs g)
    exact LT.lt.false this


theorem ne_first₁ (a : PF 2) {w : ℕ → ℕ} {t₀ k:ℕ} (hk: t₀ = a.val 0 * k) (hw: curs_walks a.val w)
    (ht₀ : ∀ (v : ℕ), w (Nat.succ v) = a.val 0 → t₀ ≤ v) :
    ∀ n, n < (a.val 0 * k).succ → w n ≠ a.val 0 := by
  have ha₀pos := a.pos 0
  intro u hu hu2
  cases u with
  | zero =>
    have g := hw.1
    rw [hu2] at g
    rw [← g] at ha₀pos
    omega
  | succ n =>
    have : (a.val 0)*k < (a.val 0)*k := calc
      _ = t₀            := hk.symm
      _ ≤ n             := ht₀ n hu2
      _ < (a.val 0) * k := Nat.succ_lt_succ_iff.mp hu
    omega

-- January 6: Why not this?
def getk (i : CursiveWalk.Instance) (s : Solution_of i) :
    { k : ℕ // s.1 = cwalk i.cycleLength.val k} := by
  let W := s; let w := W.1; let hw := W.2.1; let hu := W.2.2
  let u := i.length.val.pred
  have : u.succ = i.length.val := PNat.natPred_add_one _
  rw [← this] at hu
  have ⟨t₀,ht₀⟩  := @find_spec_le (fun s ↦ w (Nat.succ s) = (i.cycleLength.val 0)) u hu _
  have c := getc' w i.cycleLength hw
  have hlt :  ∀ (s : ℕ), s ≤ t₀ → (w s) < (i.cycleLength.val 0) :=
    before_nexus c (ne_of_le' i.cycleLength hw ht₀)
  have h02 : t₀ % (i.cycleLength.val 0) = 0 % (i.cycleLength.val 0) :=
    get_a0dvd i.cycleLength c _ hlt ht₀.1
  let k := (get_equation' (Nat.zero_le _) h02).1
  exists k
  have hk := (get_equation' (Nat.zero_le _) h02).2
  rw [zero_add] at hk
  exact unique_walk_CursiveNFA hw (by rw [hk] at ht₀; tauto) (ne_first₁ i.cycleLength hk hw ht₀.2)

/-- December 30. This needs a corresponding getk2 version, getk2'' -/
def getk1'' {i : CursiveWalk.Instance} (s : Solution_of i) : ℕ  := by
  let W := s; let w := W.1; let hw := W.2.1; let hu := W.2.2
  let u := i.length.val.pred
  have : u.succ = i.length.val := PNat.natPred_add_one _
  rw [← this] at hu
  have ⟨t₀,ht₀⟩  := @find_spec_le (fun s ↦ w (Nat.succ s) = (i.cycleLength.val 0)) u hu _
  have c := getc' w i.cycleLength hw
  have hlt :  ∀ (s : ℕ), s ≤ t₀ → (w s) < (i.cycleLength.val 0) :=
    before_nexus c (ne_of_le' i.cycleLength hw ht₀)
  have h02 : t₀ % (i.cycleLength.val 0) = 0 % (i.cycleLength.val 0) :=
    get_a0dvd i.cycleLength c _ hlt ht₀.1
  exact (get_equation' (Nat.zero_le _) h02).1

-- theorem ne_first₀ (a : PF 2) {w : ℕ → ℕ} {t₀ k : ℕ} (hk: t₀ = a.val 0 * k)
--     (ht₀ : w (Nat.succ t₀) = a.val 0) :
--     w (a.val 0*k).succ = a.val 0 := by
--   rw [hk] at ht₀
--   exact ht₀

theorem getk2'' (i : CursiveWalk.Instance) (s : Solution_of i) :
    s.1 = cwalk i.cycleLength.val (getk1'' s) := by
  let w := s.1
  have hw := s.2.1; have hu := s.2.2
  let a := i.cycleLength; let u := i.length.val.pred
  have : u.succ = i.length.val := PNat.natPred_add_one _
  rw [← this] at hu
  let t₀ := (@find_spec_le (fun s ↦ w (Nat.succ s) = (a.val 0)) u hu _).1
  have ht₀ := (@find_spec_le (fun s ↦ w (Nat.succ s) = (a.val 0)) u hu _).2
  have c := getc' w a hw
  have hlt :  ∀ (s : ℕ), s ≤ t₀ → (w s) < (a.val 0) := before_nexus c (ne_of_le' a hw ht₀)
  have h02 : t₀ % (a.val 0) = 0 % (a.val 0) := get_a0dvd a c _ hlt ht₀.1
  have hk := (get_equation' (Nat.zero_le _) h02).2
  rw [zero_add] at hk
  exact unique_walk_CursiveNFA hw
    (by simp_all only [u, w, a, t₀]; exact ht₀.1) (ne_first₁ i.cycleLength hk hw ht₀.2)


def getk1  {u:ℕ} (a : PF 2) (W : { W : ℕ → ℕ // curs_walks a.val W ∧ W (Nat.succ u) = a.val 0}) : ℕ := by
  let w := W.1
  have hw := W.2.1
  have hu := W.2.2
  let t₀ := (@find_spec_le (fun s ↦ w (Nat.succ s) = (a.val 0)) u hu).1
  have ht₀ := (@find_spec_le (fun s ↦ w (Nat.succ s) = (a.val 0)) u hu).2
  have c := getc' w a hw
  have hlt :  ∀ (s : ℕ), s ≤ t₀ → (w s) < (a.val 0) := by {
    intro _ hs
    exact before_nexus c (ne_of_le' a hw ht₀) _ hs
  }
  have h02 : t₀ % (a.val 0) = 0 % (a.val 0) := get_a0dvd a c _ hlt ht₀.1
  exact (get_equation' (Nat.zero_le _) h02).1

def getk1' (a : PF 2) {w : ℕ → ℕ} {u:ℕ} (hw: curs_walks a.val w) (hu: w (Nat.succ u) = a.val 0) : ℕ := by
  let t₀ := (@find_spec_le (fun s ↦ w (Nat.succ s) = (a.val 0)) u hu).1
  have ht₀ := (@find_spec_le (fun s ↦ w (Nat.succ s) = (a.val 0)) u hu).2
  have c := getc' w a hw
  have hlt :  ∀ (s : ℕ), s ≤ t₀ → (w s) < (a.val 0) :=
    before_nexus c (ne_of_le' a hw ht₀)
  have h02 : t₀ % (a.val 0) = 0 % (a.val 0) := get_a0dvd a c _ hlt ht₀.1
  exact (get_equation' (Nat.zero_le _) h02).1

theorem getk2' (a : PF 2) {w : ℕ → ℕ} {u:ℕ} (hw: curs_walks a.val w) (hu: w (Nat.succ u) = a.val 0) :
    w = cwalk a.val (getk1' a hw hu) := by
  let t₀ := (@find_spec_le (fun s ↦ w (Nat.succ s) = (a.val 0)) u hu).1
  have ht₀ := (@find_spec_le (fun s ↦ w (Nat.succ s) = (a.val 0)) u hu).2
  have c := getc' w a hw
  have hlt :  ∀ (s : ℕ), s ≤ t₀ → (w s) < (a.val 0) := before_nexus c (ne_of_le' a hw ht₀)
  have h02 : t₀ % (a.val 0) = 0 % (a.val 0) := get_a0dvd a c _ hlt ht₀.1
  have hk := (get_equation' (Nat.zero_le _) h02).2
  rw [zero_add] at hk
  exact unique_walk_CursiveNFA hw
    (by simp_all only [succ_eq_add_one, Fin.isValue, implies_true, t₀]; exact ht₀.1) (ne_first₁ a hk hw ht₀.2)

theorem l_unique' (a : PF 2) {k l₁ l₂ : ℕ} (he: a.val 0*k + 1 + a.val 1*l₁ = a.val 0*k + 1 + a.val 1*l₂) :
    l₁ = l₂ := Nat.eq_of_mul_eq_mul_left (a.pos 1) (Nat.add_left_cancel he)

theorem l_unique (a : PF 2) (k l₁ l₂ : ℕ)
    (he: Matrix.dotProduct a.val (fun i ↦ [k,l₁].get i)
       = Matrix.dotProduct a.val (fun i ↦ [k,l₂].get i)) : l₁=l₂ :=  by
  simp [Matrix.dotProduct] at he
  have := a.pos 1
  omega

def getl' (a : PF 2) {k n:ℕ} (hmod₀: cwalk a.val k n = a.val 0) :
    {l : ℕ // n = a.val 0*k + 1 + a.val 1*l} := by
  have hge : n ≥ (a.val 0)*k + 1 := by
    unfold cwalk at hmod₀
    by_contra hc
    rw [if_neg hc] at hmod₀
    have : n % (a.val 0) < (a.val 0) := Nat.mod_lt _ (a.pos 0)
    rw [hmod₀] at this
    omega
  let L := n - ((a.val 0)*k+1)
  have hL : n = (a.val 0)*k + 1 + L := (functional_eq_add_of_le hge).2
  rw [hL] at hmod₀; unfold cwalk at hmod₀;
  simp at hmod₀
  have : L = n - ((a.val 0)*k+1) := rfl;
  let l := L / (a.val 1)
  have h₁: (L/(a.val 1))*(a.val 1) = L := Nat.div_mul_cancel <| Nat.dvd_of_mod_eq_zero hmod₀
  have h₂: L = (a.val 1) * (L / (a.val 1)) := by rw [mul_comm] at h₁; exact h₁.symm
  have : n = (a.val 0) * k + 1 + (a.val 1) * l := by
    rw [← h₂]
    exact hL
  exact ⟨l,this⟩

def getl (a : PF 2) {k n:ℕ} (hmod₀: cwalk a.val k n = a.val 0) :
    {l : ℕ // n = Nat.succ (Matrix.dotProduct a.val (fun i ↦ [k,l].get i))} := by
  have ⟨l,lproof⟩ := getl' a hmod₀
  exists l
  rw [lproof,moveOne]
  simp

theorem walk_walks' (a : PF 2) (k:ℕ) : curs_walks a.val (cwalk a.val k) := by
  constructor
  · unfold cwalk
    rw [if_neg (by omega)]
    exact rfl
  · intro k_1
    induction k_1 with
    | zero =>
      unfold cwalk
      have : ¬ Nat.zero ≥ Nat.succ ((a.val 0) * k) := of_decide_eq_false rfl
      rw [if_neg this]
      by_cases h : k = 0
      · right
        have : 1 ≥ ((a.val 0) * k).succ :=
          Nat.succ_le_succ (Nat.le_zero.mpr (mul_eq_zero_of_right (a.val 0) h))
        rw [if_pos this,h]
        simp
      · left
        have h₁: ¬ 0 = ((a.val 0) * k) := by
          intro hc
          have := (a.pos 0)
          cases Nat.zero_eq_mul.mp hc <;> omega
        have : ¬ Nat.succ 0 ≥ Nat.succ ((a.val 0) * k) := by omega
        rw [if_neg this]
    | succ n ih =>
      unfold cwalk
      by_cases hss : (Nat.succ (Nat.succ n) ≥ Nat.succ ((a.val 0) * k))
      · rw [if_pos hss]
        by_cases hnk : (Nat.succ n ≥ Nat.succ ((a.val 0) * k))
        · rw [if_pos hnk]
          simp
          have h₂ : n + 1 - (a.val 0)*k = n - (a.val 0)*k + 1 := by omega
          unfold CursiveNFA cursive_step'
          simp
          have : ¬ (a.val 0 = 0 ∧ (n - a.val 0 * k) % a.val 1 = 0) := by
            have := a.pos 0
            omega
          rw [h₂, if_neg this]
          simp
        · rw [if_neg hnk];
          have h₅ : n.succ = (a.val 0)*k := (Nat.eq_of_lt_succ_of_not_lt hss hnk).symm
          have h₃: n+1 - (a.val 0)*k = 0 := tsub_eq_of_eq_add_rev h₅
          simp
          rw [h₃]
          simp at h₅
          rw [h₅]
          simp
          right
          exact rfl
      -- early times:
      · rw [if_neg hss]
        rw [if_neg (by omega)]
        by_cases h : (n.succ % (a.val 0) = 0)
        · rw [h]
          have : n.succ.succ % (a.val 0) = 1 % (a.val 0) := by
            rw [Nat.succ_eq_add_one,Nat.add_mod, h]
            simp
          rw [this]
          left
          exact rfl

        · unfold CursiveNFA cursive_step'; simp
          rw [if_neg h]
          rw [if_pos (Nat.mod_lt _ (a.pos 0))]
          rfl

theorem walk__injective' (a : PF 2) (k₁ k₂ : ℕ) (he : cwalk a.val k₁ = cwalk a.val k₂) : k₁ = k₂ := by
  contrapose he
  cases Ne.lt_or_lt he with
  | inl h => exact walkInjective a h
  | inr h => exact (walkInjective a h).symm
