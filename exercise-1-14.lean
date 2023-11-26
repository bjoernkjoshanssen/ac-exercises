import Mathlib.Computability.DFA

-- Solution to Exercise 1.14.

open List
/-
In this file we quite simply prove that the automatic complexity of a "repeat" word like
000000000
is at most 2.
The dependency structure:

theorem complexity_of_repeat
  def TwoState (the 2-state DFA in question)
  theorem TwoState_accepts_only_repeat
    theorem TwoState_accepts_only_starts_z
      TwoState_stay_q0
      TwoState_stay_q1
      q0_ne_q1
    either_or_strong
    theorem TwoState_no_return_to_q0
  theorem TwoState_accepts_repeat
    TwoState_step

-/
-- open Classical


axiom u:ℕ
def α := Fin u --{l : ℕ // l < u} -- The input alphabet

-- def (Fin 2) := Fin 2 -- The set of states

noncomputable instance : DecidableEq α := by exact Classical.decEq α
noncomputable instance : DecidableEq (Fin 2) := by exact Classical.decEq (Fin 2)

def q0 := (⟨0, Nat.succ_pos 1⟩:(Fin 2))
def q1 := (⟨1, Nat.one_lt_succ_succ 0⟩:(Fin 2))


noncomputable def TwoState (z:α) : DFA α (Fin 2) := -- the two-state DFA that accepts z^n
  DFA.mk
    (λ q ↦ λ b : α ↦ -- transition ("step") function
    ite (q=q0) (ite (b=z) q0 q1) q1)
    q0             -- start state
    {q0}           -- set of accept states
    
def uniquely_accepts {τ: Type} (M: DFA α τ) (s: List α) :=
    ∀ t : List α,
      t.length = s.length  →
         (M.accepts t ↔ t=s)


def automatic_complexity_is_at_most : List α → ℕ → Prop := λ s k ↦
-- this should be: ∃ k' ≤ k, because *intentionally* it is not guaranteed that the set of cardinalities
-- for which a uniquely accepting DFA exists is closed upward.
  ∃ M : DFA α (Fin k), -- the set of states is a prefix and subtype of ℕ
  uniquely_accepts M s


theorem q0_ne_q1: q0 ≠ q1 :=
  λ he ↦ zero_ne_one (congr_arg (λ x:(Fin 2) ↦ x.1) he)

theorem TwoState_stay_q0 {a z:α} (h: (TwoState z).eval [a] = q0) : a = z :=
  let M := (TwoState z)
  have : a ≠ z → (TwoState z).eval [a] ≠ q0 :=
    λ h ↦
      have hw: (TwoState z).eval [a] = q1 :=
        calc
        (TwoState z).step q0 a = (ite (true) (ite (a = z) q0 q1) q1)  := eq_ite_iff.mpr (by {
          left
          constructor
          rfl
          unfold TwoState
          exact if_pos rfl
        })
        _ = q1                                     := by {
        have : (if true = true then if a = z then q0 else q1 else q1)
             = (if a = z then q0 else q1)
        := rfl
        rw [this]
        exact if_neg h
        }
      have : q0 ≠ q1 := q0_ne_q1
      by {
        intro hcontra
        rw [hw] at hcontra
        exact this hcontra.symm
      }
  by {
    by_contra H
    exact this H h
  }


theorem TwoState_stay_q1 (z:α) (x:List α): (TwoState z).evalFrom q1 x = q1 :=
  List.recOn x rfl (λ a y h ↦ by {
    have t3 : q1 ≠ q0 := q0_ne_q1.symm
    have t2 : DFA.evalFrom (TwoState z) q1 [a] = q1 := by {
      have t1: DFA.evalFrom (TwoState z) q1 [a] =
      DFA.step (TwoState z) q1 a :=
        DFA.evalFrom_singleton _ _ _
      rw [t1]
      exact if_neg t3      
    }
    have t1 : DFA.evalFrom (TwoState z) q1 (a :: y) =
    DFA.evalFrom (TwoState z) (DFA.evalFrom (TwoState z) q1 [a]) y := rfl
    rw [t2] at t1
    rw [h] at t1
    exact t1
  }) -- kind of surprised this works


theorem TwoState_accepts_repeat {z :α} {n : ℕ} : (TwoState z).eval (List.replicate n z) = q0:=

  let M := (TwoState z)
  have TwoState_step: M.step M.start z = q0 :=
    (
    calc
    M.step M.start z = ite (M.start = q0) (ite (z = z) q0 q1)  q1 := rfl
    _ = ite (M.start = q0) (q0)                                q1 := by {
      exact congr_arg (λ q ↦ if M.start = q0 then q else q1) (if_pos rfl)
    }
    _ = q0 := by exact if_pos rfl
    )
  Nat.recOn n (rfl) (λ n h ↦ calc
  _ = foldl M.step (M.step M.start z) (List.replicate n z) := rfl
  _ = foldl M.step q0                 (List.replicate n z) := by rw [TwoState_step]
  _ = q0 := h
  )




theorem either_or {a : (Fin 2)}  (h : a.1≠ 1) : a.1=0 := by {
  have : a.1 < 2 := a.2
  have : a.1 ≤ 1 := by exact Fin.is_le a
  have : a.1 < 1 := by exact Nat.lt_of_le_of_ne this h
  exact Nat.lt_one_iff.mp this
}


  --Iff.elim_left Nat.lt_one_iff (array.push_back_idx a.2 h)

theorem either_or_strong {a : (Fin 2)} (not_zero : a ≠ q0) : a = q1 :=
  have h1: a.1 = 1 := by_contra (
    λ not_one ↦ not_zero (Fin.eq_of_veq (either_or not_one))
  )
  Fin.eq_of_veq h1

theorem TwoState_no_return_to_q0 {q:(Fin 2)} {z:α}{x:List α}
  (h:(TwoState z).evalFrom q x = q0): q=q0 :=
  by_contra (
    λ hh: q ≠ q0 ↦
    have h1: q = q1 := either_or_strong hh

    have h01: q0 = q1 := calc
              q0 = (TwoState z).evalFrom q  x := h.symm
             _ = (TwoState z).evalFrom q1 x   := congr_arg (λ r ↦ (TwoState z).evalFrom r x) h1
             _ = q1                           := TwoState_stay_q1 z x
    q0_ne_q1 h01
  )

theorem TwoState_accepts_only_starts_z {a z:α} {y:List α}
  (hq0:(TwoState z).eval (a :: y) = q0): a = z :=
  TwoState_stay_q0 (
    by_contra (
      λ h ↦
      let M := (TwoState z)
      have h1: M.step q0 a = q1 := either_or_strong h
      have hq1: M.eval (a :: y) = q1 :=
        calc M.evalFrom (M.step q0 a) y
        = M.evalFrom q1 y := by rw [h1]
        _ = q1                := TwoState_stay_q1 z y

      (ne_of_eq_of_ne hq1 (Ne.symm q0_ne_q1)) hq0
    )
  )

theorem TwoState_accepts_only_repeat {z :α} {x:List α}:
(TwoState z).eval x = q0 → x = List.replicate x.length z := -- proof long because a::x deFined "backwards"
List.recOn x (λ h ↦ rfl) (
    λ a x h_ind hq0 ↦
    let M := (TwoState z)
    have h0 : M.step q0 a = q0 := TwoState_no_return_to_q0 hq0

    have can_ind: M.eval x = q0 :=
      by_contra (λ hh: M.eval x ≠ q0 ↦
        have : q0 = q1 :=
          calc q0 = M.evalFrom (M.step q0 a) x := hq0.symm
              _ = M.evalFrom q0 x              := congr_arg (λ u ↦ M.evalFrom u x) h0
              _ = q1                           := either_or_strong hh
        q0_ne_q1 this
      )

    calc _ = a :: (List.replicate x.length z) := congr_arg _ (h_ind can_ind)
    _ = z :: (List.replicate x.length z)   := congr_arg (
      λ b ↦ b :: replicate (length x) z
    ) (TwoState_accepts_only_starts_z hq0)
)

theorem complexity_of_repeat (z:α) (n:ℕ): automatic_complexity_is_at_most (List.replicate n z) 2 :=
  let M := (TwoState z)
  have n2: M.accepts (List.replicate n z) := TwoState_accepts_repeat
  Exists.intro M (λ t h ↦
    have mp: M.accepts t → t=(List.replicate n z) :=
      λ ha ↦
      calc t = List.replicate t.length z            := TwoState_accepts_only_repeat ha
      _ = List.replicate (List.replicate n z).length z := by rw [h]
      _ = List.replicate n z                   := by rw [List.length_replicate n z]

    have mpr: t=(List.replicate n z) → M.accepts t := λ his ↦ by {rw [← his] at n2;exact n2}

    Iff.intro mp mpr
  )
