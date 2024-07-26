import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Prod

-- Solution to Exercises 3.1 and 3.2.

def sat_eq (a: ℕ×ℕ) (n: ℕ) (x: ℕ×ℕ) : Prop :=
a.1*x.1+a.2*x.2=n

def unique_sol (a : ℕ×ℕ) (n : ℕ) : Prop :=
  ∃! x : ℕ×ℕ, sat_eq a n x

/-
uniquely satisfies = satisfies ∧ if_any
-/

theorem paireq (a b c d :ℕ) (ha : a=c) (hb: b=d): (a,b) = (c,d) :=
congr (congr_arg Prod.mk ha) hb

theorem proj1eq {a b c d : ℕ} (h: (a,b) = (c,d))
: a=c := by
  simp only [Prod.mk.injEq] at h
  tauto

theorem proj2eq {a b c d : ℕ} (h: (a,b) = (c,d))
: b=d := by
  simp only [Prod.mk.injEq] at h
  tauto

theorem reduce (a) (n:ℕ) (x₀ u v : ℕ)
  (original:unique_sol a (n+a.2*v) ∧ sat_eq a (n+a.2*v) (x₀, u+v)):
  unique_sol a n := by {
  use (x₀,u)
  apply And.intro
  rcases original with ⟨_, orig_sat⟩
  unfold sat_eq at orig_sat
  simp at orig_sat
  have  : a.1 * x₀ + a.2 * u + a.2 * v = n + a.2 * v := calc
     _  = a.1 * x₀ + (a.2 * u + a.2 * v) := Nat.add_assoc _ _ _
    _ = a.1 * x₀ + a.2 * (u + v)       := by rw [← Nat.left_distrib a.2 u v]
    _ = n + a.2 * v                    := orig_sat
  exact Nat.add_right_cancel this
  intros y hy
  unfold sat_eq at hy
  have new_sat : sat_eq a (n+a.2*v) (y.1, y.2+v) := (calc
  a.1 * y.1 + a.2 * (y.2+v) =  a.1 * y.1 +( a.2 * y.2 + a.2* v) := by rw [Nat.left_distrib a.2 y.2 v]
  _ = (a.1 * y.1 + a.2 * y.2) + a.2* v                          := (Nat.add_assoc _ _ _).symm
  _ = n+a.2*v                                                   := by rw [hy])

  let orig_unique := original.1
  let orig_sat := original.2

  -- let unique_sol := orig_unique.2
  -- let if_any := unique_sol.2

  -- rcases original with orig_unique | orig_sat
  rcases orig_unique with ⟨_, unique_sol⟩
  rcases unique_sol with ⟨_, if_any⟩
  have eq_with_u: (y.1, y.2+v) = (x₀, u+v) := (calc
  _ = _ := (if_any _) new_sat
  _ = _ := ((if_any _) orig_sat).symm)
  have : y = (y.1,y.2) := Prod.mk.eta.symm
  rw [this]
  apply paireq
  exact proj1eq eq_with_u
  exact Nat.add_right_cancel (proj2eq eq_with_u)

  }


/-
if ax+by=n has a unique solution (x0,uv) then
ax+buy=n has a unique solution
-/
theorem amplify (a) (n:ℕ) (x₀ u v : ℕ) (u_pos: 0 < u)
  (original:unique_sol a n ∧ sat_eq a n (x₀, u*v)):
            unique_sol (a.1, a.2*u) n := by {
  exists (x₀,v)

  constructor
  let orig_sat := original.2
  exact calc _ = a.1 * x₀ + a.2 * (u * v) := by rw [Nat.mul_assoc]
           _ = _ := orig_sat
  intros y hy
  have new_sat : sat_eq a n (y.1, u*y.2) := (calc
  a.1 * y.1 + a.2 * (u * y.2) =  a.1 * y.1 + a.2 * u * y.2 := by rw [← Nat.mul_assoc]
  _ = _ := hy)
  let orig_unique := original.1
  let orig_sat := original.2
  rcases orig_unique with ⟨_, unique_sol⟩

  rcases unique_sol with ⟨_, if_any⟩
  have eq_with_u: (y.1, u*y.2) = (x₀, u*v) := calc
                             _ = _ := (if_any _) new_sat
                           _ = _ := ((if_any _) orig_sat).symm
  have : y = (y.1,y.2) := Prod.mk.eta.symm
  rw [this]
  apply paireq
  exact proj1eq eq_with_u
  exact Nat.eq_of_mul_eq_mul_left u_pos (proj2eq eq_with_u)
}
