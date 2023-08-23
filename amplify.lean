import tactic.basic
import tactic.ring
def sat_eq (a: ℕ×ℕ) (n: ℕ) (x: ℕ×ℕ) : Prop :=
a.1*x.1+a.2*x.2=n

def unique_sol (a : ℕ×ℕ) (n : ℕ) : Prop :=
  ∃! x : ℕ×ℕ, sat_eq a n x

/-
uniquely satisfies = satisfies ∧ if_any
-/

theorem paireq (a b c d :ℕ) (ha : a=c) (hb: b=d): (a,b) = (c,d) :=
congr (congr_arg prod.mk ha) hb

theorem proj1eq {a b c d : ℕ} (h: (a,b) = (c,d))
: a=c :=
prod.mk.inj_arrow h (λ h1 h2, h1)

theorem proj2eq {a b c d : ℕ} (h: (a,b) = (c,d))
: b=d :=
prod.mk.inj_arrow h (λ h1 h2, h2)

theorem reduce (a) (n:ℕ) (x₀ u v : ℕ)
  (original:unique_sol a (n+a.2*v) ∧ sat_eq a (n+a.2*v) (x₀, u+v)):
  unique_sol a n := by {
  existsi (x₀,u),
  split,
  cases original with _ orig_sat,
  unfold sat_eq at orig_sat,
  simp at orig_sat,
  have  : a.1 * x₀ + a.2 * u + a.2 * v = n + a.2 * v, from calc 
     _  = a.1 * x₀ + (a.2 * u + a.2 * v) : nat.add_assoc _ _ _
    ... = a.1 * x₀ + a.2 * (u + v)       : by rw ← nat.left_distrib a.2 u v
    ... = n + a.2 * v                    : orig_sat,
  exact nat.add_right_cancel this,
  intros y hy,
  unfold sat_eq at hy,
  have new_sat : sat_eq a (n+a.2*v) (y.1, y.2+v), from calc 
         a.1 * y.1 + a.2 * (y.2+v)
      =  a.1 * y.1 +( a.2 * y.2 + a.2* v): by rw nat.left_distrib a.2 y.2 v
  ... = (a.1 * y.1 + a.2 * y.2) + a.2* v : (nat.add_assoc _ _ _).symm
  ... = n+a.2*v: by rw hy,
  cases original with orig_unique orig_sat,
  cases orig_unique with _ unique_sol,
  cases unique_sol with _ if_any,
  have eq_with_u: (y.1, y.2+v) = (x₀, u+v), from calc
                             _ = _: (if_any _) new_sat
                           ... = _: ((if_any _) orig_sat).symm,
  have : y = (y.1,y.2), from prod.mk.eta.symm,
  rw this,
  apply paireq,
  exact proj1eq eq_with_u,
  exact nat.add_right_cancel (proj2eq eq_with_u)
  }


/-
if ax+by=n has a unique solution (x0,uv) then
ax+buy=n has a unique solution
-/
theorem amplify (a) (n:ℕ) (x₀ u v : ℕ) (u_pos: 0 < u)
  (original:unique_sol a n ∧ sat_eq a n (x₀, u*v)):
            unique_sol (a.1, a.2*u) n := by {
  existsi (x₀,v),
  split,
  cases original with _ orig_sat,
  exact calc _ = a.1 * x₀ + a.2 * (u * v): by rw nat.mul_assoc
           ... = _: orig_sat,
  intros y hy,
  have new_sat : sat_eq a n (y.1, u*y.2), from calc 
         a.1 * y.1 + a.2 * (u * y.2)
      =  a.1 * y.1 + a.2 * u * y.2: by rw ← nat.mul_assoc
  ... = _: hy,
  cases original with orig_unique orig_sat,
  cases orig_unique with _ unique_sol,
  cases unique_sol with _ if_any,
  have eq_with_u: (y.1, u*y.2) = (x₀, u*v), from calc
                             _ = _: (if_any _) new_sat
                           ... = _: ((if_any _) orig_sat).symm,
  have : y = (y.1,y.2), from prod.mk.eta.symm,
  rw this,
  apply paireq,
  exact proj1eq eq_with_u,
  exact nat.eq_of_mul_eq_mul_left u_pos (proj2eq eq_with_u)
}

