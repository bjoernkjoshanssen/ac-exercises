import tactic.basic

def sat_eq (a: ℕ×ℕ) (n: ℕ) (x: ℕ×ℕ) : Prop :=
a.1*x.1+a.2*x.2=n

def unique_sol (a : ℕ×ℕ) (n : ℕ) : Prop :=
  ∃! x : ℕ×ℕ, sat_eq a n x

/-
uniquely satisfies = satisfies ∧ if_any
-/

/-
if ax+by=n has a unique solution (x0,uv) then
ax+buy=n has a unique solution
-/


theorem paireq (a b c d :ℕ) (ha : a=c) (hb: b=d): (a,b) = (c,d) :=
congr (congr_arg prod.mk ha) hb

theorem proj1eq {a b c d : ℕ} (h: (a,b) = (c,d))
: a=c :=
prod.mk.inj_arrow h (λ h1 h2, h1)

theorem proj2eq {a b c d : ℕ} (h: (a,b) = (c,d))
: b=d :=
prod.mk.inj_arrow h (λ h1 h2, h2)


theorem amplify (a) (n:ℕ) (x₀ u v : ℕ) (u_pos: 0 < u)
  (original:unique_sol a n ∧ sat_eq a n (x₀, u*v)):
            unique_sol (a.1, a.2*u) n := by {
  existsi (x₀,v),
  split,
  cases original with _ orig_sat,
  exact calc _ = a.1 * x₀ + a.2 * (u * v): by rw nat.mul_assoc
           ... = _: orig_sat,
  intros y hy,
  cases original with orig_unique orig_sat,
  have new_sat : sat_eq a n (y.1, u*y.2), from calc 
         a.1 * y.1 + a.2 * (u * y.2)
      =  a.1 * y.1 + a.2 * u * y.2: by rw ← nat.mul_assoc
  ... = _: hy,
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
