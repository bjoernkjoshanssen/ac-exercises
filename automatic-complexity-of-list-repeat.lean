import computability.DFA computability.NFA
import data.fintype.basic
import data.fintype.fin

open list
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
constant u:ℕ
def α := {l : ℕ // l < u} -- The input alphabet

def σ := fin 2 -- The set of states


def q0 := (⟨0,zero_lt_two⟩:σ)
def q1 := (⟨1, one_lt_two⟩:σ)

def TwoState (z:α) : DFA α σ := -- the two-state DFA that accepts z^n
  DFA.mk
    (λ q, λ b : α, -- transition ("step") function
    ite (q=q0) (ite (b=z) q0 q1) q1)
    q0             -- start state
    {q0}           -- set of accept states
    
def uniquely_accepts {τ: Type} (M: DFA α τ) (s: list α) :=
    ∀ t : list α,
      t.length = s.length  →
         (M.accepts t ↔ t=s)


def automatic_complexity_is_at_most : list α → ℕ → Prop := λ s, λ k,
-- this should be: ∃ k' ≤ k, because *intentionally* it is not guaranteed that the set of cardinalities
-- for which a uniquely accepting DFA exists is closed upward.
  ∃ M : DFA α (fin k), -- the set of states is a prefix and subtype of ℕ
  uniquely_accepts M s


theorem q0_ne_q1: q0 ≠ q1 :=
  λ he, zero_ne_one (congr_arg (λ x:σ, x.1) he)

theorem TwoState_stay_q0 {a z:α} (h: (TwoState z).eval [a] = q0) : a = z :=
  let M := (TwoState z) in
  have a ≠ z → M.eval [a] ≠ q0, from
    λ h,
      have hw: M.eval [a] = q1, from
        calc M.step q0 a = (ite (true) (ite (a = z) q0 q1) q1): rfl
                     ... = q1: by {cc,},
      have q0 ≠ q1, from q0_ne_q1,
      by cc,
  by cc

theorem TwoState_stay_q1 (z:α) (x:list α): (TwoState z).eval_from q1 x = q1 :=
  list.rec_on x rfl (λ _ _ h, h) -- kind of surprised this works


theorem TwoState_accepts_repeat {z :α} {n : ℕ} : (TwoState z).eval (repeat z n) = q0:=

  let M := (TwoState z) in
  have TwoState_step: M.step M.start z = q0, from
    calc M.step M.start z = ite (M.start = q0) (ite (z = z) q0 q1)  q1: rfl
                      ... = ite (M.start = q0) (q0)                 q1: by cc,
  nat.rec_on n (rfl) (λ n h, calc
      _ = foldl M.step (M.step M.start z) (repeat z n) : rfl
    ... = foldl M.step q0                 (repeat z n) : by rw TwoState_step
    ... = q0: h
  )




lemma either_or {a : σ}  (h : a.1≠ 1) : a.1=0 :=
  iff.elim_left nat.lt_one_iff (array.push_back_idx a.2 h)

lemma either_or_strong {a : σ} (not_zero : a ≠ q0) : a = q1 :=
  have h1: a.1 = 1, from by_contra (
    λ not_one, not_zero (fin.eq_of_veq (either_or not_one))
  ),
  fin.eq_of_veq h1

theorem TwoState_no_return_to_q0 {q:σ} {z:α}{x:list α}
  (h:(TwoState z).eval_from q x = q0): q=q0 :=
  by_contra (
    λ hh: q ≠ q0,
    have h1: q = q1, from either_or_strong hh,

    have h01: q0 = q1, from calc
              q0 = (TwoState z).eval_from q  x : h.symm
             ... = (TwoState z).eval_from q1 x : congr_arg (λ r, (TwoState z).eval_from r x) h1
             ... = q1                          : TwoState_stay_q1 z x,
    q0_ne_q1 h01
  )

theorem TwoState_accepts_only_starts_z {a z:α} {y:list α}
  (hq0:(TwoState z).eval (a :: y) = q0): a = z :=
  TwoState_stay_q0 (
    by_contra (
      λ h,
      let M := (TwoState z) in
      have h1: M.step q0 a = q1, from either_or_strong h,
      have hq1: M.eval (a :: y) = q1, from
        calc M.eval_from (M.step q0 a) y
          = M.eval_from q1 y : by rw h1
      ... = q1               : TwoState_stay_q1 z y,

      (ne_of_eq_of_ne hq1 (ne.symm q0_ne_q1)) hq0
    )
  )

theorem TwoState_accepts_only_repeat {z :α} {x:list α}:
(TwoState z).eval x = q0 → x = repeat z x.length := -- proof long because a::x defined "backwards"
list.rec_on x (λ h, rfl) (
    λ a x h_ind hq0,
    let M := (TwoState z) in
    have h0 : M.step q0 a = q0, from TwoState_no_return_to_q0 hq0,

    have can_ind: M.eval x = q0, from
      by_contra (λ hh: M.eval x ≠ q0,
        have q0 = q1, from
          calc q0 = M.eval_from (M.step q0 a) x : hq0.symm
              ... = M.eval_from q0 x            : congr_arg (λ u, M.eval_from u x) h0
              ... = q1                          : either_or_strong hh,
        q0_ne_q1 this
      ),

    calc _ = a :: (repeat z x.length): congr_arg _ (h_ind can_ind)
       ... = z :: (repeat z x.length): congr_arg _ (TwoState_accepts_only_starts_z hq0)
)

theorem complexity_of_repeat (z:α) (n:ℕ): automatic_complexity_is_at_most (repeat z n) 2 :=
  let M := (TwoState z) in
  have n2: M.accepts (repeat z n), from TwoState_accepts_repeat,
  exists.intro M (λ t h,
    have mp: M.accepts t → t=(repeat z n), from
      λ ha,
      calc t = repeat z t.length            : TwoState_accepts_only_repeat ha
         ... = repeat z (repeat z n).length : by rw h
         ... = repeat z n                   : by rw (length_repeat z n),

    have mpr: t=(repeat z n) → M.accepts t, from λ his, by {rw ← his at n2,exact n2,},

    iff.intro mp mpr
  )
