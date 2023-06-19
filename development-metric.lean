import tactic.basic
import tactic.ring
import topology.metric_space.basic
import data.real.basic
import analysis.special_functions.log.basic

/- Development of automatic complexity distance function -/

constants b n : ℕ 
def α : Type := vector (fin b) n

constant A_cond : α → α → pnat
noncomputable def A : α → α → ℝ := λ x y, ((A_cond x y) : ℝ) 

noncomputable def dis : α → α → ℝ :=
  λ x y, real.log ((A x y) * (A y x))

/- Axioms: -/
axiom one_axiom : ∀ (x : α), A x x = 1            /- A_N(x|x)=1 -/
axiom one_only_axiom {x y : α}: A x y = 1 → x = y
axiom tri_axiom {x y z : α}: A x z ≤ A x y * A y z

/- Theorems: -/

theorem pnat_one {x y:α}: (1:ℝ) ≤ (A x y : ℝ) :=
by {
  let Q := pnat.one_le (A_cond x y),
  unfold A,norm_cast,exact Q, 
}

theorem pos_one {x y:α}: (0:ℝ) < (A x y : ℝ) :=
  calc 0 < 1: one_pos
     ... ≤ _: pnat_one

lemma nonzero_one {x y : α}: A x y ≠ 0                            := ne_of_gt pos_one
lemma nonzero_two {w x y z : α}: A w x * A y z ≠0                 := mul_ne_zero nonzero_one nonzero_one

lemma pos_two {w x y z : α} : 0 < A w x * A y z                   := mul_pos pos_one pos_one
lemma pos_four  {x y z : α} : 0 < A x y * A y z * (A z y * A y x) := mul_pos pos_two pos_two

lemma nonneg_one  {x y:α} : 0 ≤ A x y                             := le_of_lt pos_one
lemma nonneg_two {w x y z : α} : 0 ≤ A w x * A y z                := le_of_lt pos_two


theorem A_self (x : α): dis x x = 0 :=
  calc  _ = real.log ((A x x) * (A x x)):rfl
      ... = real.log ((1) * (1)): by repeat{rw one_axiom}
      ... = real.log 1          : by rw mul_one
      ... = 0                   : real.log_one


lemma le_of_ge {x y: ℝ} (hx:1 ≤x )(hy:1 ≤ y)(h1:1 =x*y): x≤1  :=
  have 0 ≤ x, from calc
       0 ≤ 1: zero_le_one
     ... ≤ x: hx,
  calc x = x*1   : (mul_one _).symm
     ... ≤ x * y : mul_le_mul_of_nonneg_left hy this
     ... = 1     : h1.symm 

theorem mycomm: ∀ (x y : α), dis x y = dis y x :=
  λ x y, by {unfold dis,rw mul_comm,}

theorem myeqof : ∀ (x y : α), dis x y = 0 → x = y :=
  λ x y h₁,
  have h₂: dis y x = 0, by rwa mycomm,
  have H₁: (((A x y) * (A y x)):ℝ) = (1:ℝ), from real.eq_one_of_pos_of_log_eq_zero pos_two h₁,
  have H₂ : 1 ≥ (A x y : ℝ), from le_of_ge pnat_one pnat_one H₁.symm,
  one_only_axiom (ge_antisymm pnat_one H₂)

lemma A_main {x y z : α}:
  A x z * A z x ≤ (A x y * A y z) * (A z y * A y x) :=
         calc _ ≤ (A x y * A y z) * A z x           : mul_le_mul_of_nonneg_right tri_axiom nonneg_one
            ... ≤ _                                 : mul_le_mul_of_nonneg_left  tri_axiom nonneg_two

theorem triangle: ∀ (x y z : α), dis x z ≤ dis x y + dis y z :=
λ x y z, 
calc dis x z = real.log ((A x z)            *          (A z x)): rfl
         ... ≤ real.log (
              ((A x y) * (A y z))
            * ((A z y) * (A y x))
          ): (real.log_le_log (pos_two) pos_four).mpr A_main
         ... = real.log (((A x y) * (A y x)) * ((A y z)*(A z y))): by ring_nf
         ... = real.log ((A x y) * (A y x)) + real.log ((A y z)*(A z y)): real.log_mul (nonzero_two) (nonzero_two)

noncomputable instance automatic_complexity_metric : metric_space α :=
{
        dist               := dis,
        dist_self          := A_self,
        eq_of_dist_eq_zero := myeqof,
        dist_comm          := mycomm,
        dist_triangle      := triangle
    }
