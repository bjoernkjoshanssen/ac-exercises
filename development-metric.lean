import Mathlib.Data.PNat.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Topology.MetricSpace.Basic

/- Development of automatic complexity distance function -/

axiom α : Type /- For example α could be 0{0,1}^{n-1} -/

axiom A_cond : α → α → PNat /- A_N(x ∣ y) -/
noncomputable def A : α → α → Real := λ x y ↦ ((A_cond x y) : Real) 

noncomputable def dis : α → α → Real :=
  λ x y ↦ Real.log ((A x y) * (A y x))

noncomputable def dis_max : α → α → Real :=
  λ x y ↦ max (Real.log (A x y))
             (Real.log (A y x))

axiom f : Real → Real → Real  
axiom f00 : f 0 0 = 0
axiom fcomm: Commutative f
axiom fonly: ∀ x y, f x y = 0 → x = 0 ∧ y = 0 
axiom fmonotone:    ∀ a b c d, a ≤ b → c ≤ d → f a c ≤ f b d   
axiom fsubadditive: ∀ a b c d, f (a+b) (c+d) ≤ f a c + f b d 

noncomputable def dis_f : α → α → Real :=
  λ x y ↦ f (Real.log (A x y))
           (Real.log (A y x))


/- Axioms: -/
axiom one_axiom : ∀ (x : α), A x x = 1            /- A_N(x|x)=1 -/
axiom one_only_axiom {x y : α}: A x y = 1 → x = y
axiom tri_axiom {x y z : α}: A x z ≤ A x y * A y z

/- Theorems: -/


theorem pnat_one {x y:α}: (1:Real) ≤ (A x y : Real) :=
by {
  let Q := PNat.one_le (A_cond x y)
  unfold A;norm_cast;
}

theorem pos_one {x y:α}: (0:Real) < (A x y : Real) := calc
  0 < 1 := one_pos
  _ ≤ _ := pnat_one

lemma nonzero_one {x y : α}: A x y ≠ 0                            := ne_of_gt pos_one
lemma nonzero_two {w x y z : α}: A w x * A y z ≠0                 := mul_ne_zero nonzero_one nonzero_one

lemma pos_two {w x y z : α} : 0 < A w x * A y z                   := mul_pos pos_one pos_one
lemma pos_four  {x y z : α} : 0 < A x y * A y z * (A z y * A y x) := mul_pos pos_two pos_two

lemma nonneg_one  {x y:α} : 0 ≤ A x y                             := le_of_lt pos_one
lemma nonneg_two {w x y z : α} : 0 ≤ A w x * A y z                := le_of_lt pos_two


theorem dis_self (x : α): dis x x = 0 :=
  calc  _ = Real.log ((A x x) * (A x x)) := rfl
      _ = Real.log ((1) * (1)) := by repeat{rw [one_axiom]}
      _ = Real.log 1           := by rw [mul_one]
      _ = 0                    := Real.log_one

theorem dis_max_self (x : α): dis_max x x = 0 :=
  calc  _ = max (Real.log (A x x)) (Real.log (A x x)) := rfl
      _ = max (Real.log 1) (Real.log 1) := by repeat{rw [one_axiom]}
      _ = Real.log 1          := max_eq_left (le_refl _)
      _ = 0                   := Real.log_one

theorem dis_f_self (x : α): dis_f x x = 0 :=
  calc  _ = f (Real.log (A x x)) (Real.log (A x x)) := rfl
      _ = f (Real.log 1) (Real.log 1) := by repeat{rw [one_axiom]}
      _ = f 0 0                       := by repeat{rw [Real.log_one]}
      _ = 0                           := f00

lemma le_of_ge {x y: Real} (hx:1 ≤x )(hy:1 ≤ y)(h1:1 =x*y): x≤1  :=
  have : 0 ≤ x := calc
       0 ≤ 1 := zero_le_one
       _ ≤ x := hx
  calc
  x = x*1   := (mul_one _).symm
  _ ≤ x * y := mul_le_mul_of_nonneg_left hy this
  _ = 1     := h1.symm 

theorem dis_comm: ∀ (x y : α), dis x y = dis y x :=
  λ x y ↦ by {unfold dis;rw [mul_comm]}

theorem dis_max_comm: ∀ (x y : α), dis_max x y = dis_max y x :=
  λ x y ↦ by {unfold dis_max;rw [max_comm]}

theorem dis_f_comm: ∀ (x y : α), dis_f x y = dis_f y x :=
  λ x y ↦ by {unfold dis_f;rw [fcomm]}

theorem dis_eq_of {x y : α}: dis x y = 0 → x = y :=
  λ h₁ ↦
  have h₂: dis y x = 0 := by rwa [dis_comm]
  have H₁: (((A x y) * (A y x)):Real) = (1:Real) := Real.eq_one_of_pos_of_log_eq_zero pos_two h₁
  have H₂ : 1 ≥ (A x y : Real) := le_of_ge pnat_one pnat_one H₁.symm
  one_only_axiom (ge_antisymm pnat_one H₂)

theorem dis_max_eq_of : ∀ (x y : α), dis_max x y = 0 → x = y :=
  λ x y h₁ ↦
  by {
    have K: max (Real.log (A x y)) (Real.log (A y x)) = 0 := h₁
    
    have G: Real.log (A x y) ≤ Real.log 1 := calc
                           _ ≤  max (Real.log (A x y)) (Real.log (A y x)) := le_max_left _ _
                         _ = 0 := K
                         _ = Real.log 1 := Real.log_one.symm

    have J : A x y ≤ 1 := (Real.log_le_log pos_one zero_lt_one).mp G
    have J₁ : A x y = 1 := le_antisymm J pnat_one
    exact one_only_axiom J₁
  }

theorem dis_f_eq_of : ∀ (x y : α), dis_f x y = 0 → x = y :=
  λ x y h₁ ↦
  by {
    have thethis: (Real.log (A x y)) = 0 ∧ (Real.log (A y x)) = 0 := fonly  (Real.log (A x y)) (Real.log (A y x)) h₁
    rcases thethis with ⟨this_left,this_right⟩
    have : A x y = 1 := Real.eq_one_of_pos_of_log_eq_zero pos_one this_left
    exact one_only_axiom this
  }

lemma A_main {x y z : α}:
  A x z * A z x ≤ (A x y * A y z) * (A z y * A y x) :=
         calc _ ≤ (A x y * A y z) * A z x           := mul_le_mul_of_nonneg_right tri_axiom nonneg_one
            _ ≤ _                                 := mul_le_mul_of_nonneg_left  tri_axiom nonneg_two

theorem triangle: ∀ (x y z : α), dis x z ≤ dis x y + dis y z :=
λ x y z ↦ calc
  dis x z = Real.log ((A x z)            *          (A z x)) := rfl
  _ ≤ Real.log (((A x y) * (A y z)) * ((A z y) * (A y x))) := (Real.log_le_log (pos_two) pos_four).mpr A_main
  _ = Real.log (((A x y) * (A y x)) * ((A y z)*(A z y))) := by ring_nf
  _ = Real.log ((A x y) * (A y x)) + Real.log ((A y z)*(A z y)) := Real.log_mul (nonzero_two) (nonzero_two)

lemma max_example1 {a b c d : Real} : (a+b) ≤ max a d + max b c := calc
_ ≤(max a d) + b := add_le_add_right (le_max_left _ _) _
_ ≤ _ := add_le_add_left (le_max_left _ _) _

lemma max_example2 {a b c d : Real} : (c+d) ≤ max a d + max b c :=
calc _ = d + c := add_comm _ _
_ ≤(max a d) + c := add_le_add_right (le_max_right _ _) _
_ ≤ _ := add_le_add_left (le_max_right _ _) _

lemma max_example (a b c d : Real) : max (a+b) (c+d) ≤ max a d + max b c :=
max_le max_example1 max_example2


lemma log_le_mul {x y z : α}  :
Real.log (A x z) ≤ Real.log (A x y * (A y z)) := (Real.log_le_log pos_one pos_two).mpr tri_axiom

theorem R {x y z : α}: Real.log (A x z) ≤ Real.log (A x y) + Real.log (A y z) :=
calc _ ≤ Real.log (A x y * (A y z)) := (Real.log_le_log pos_one pos_two).mpr tri_axiom
_ = _ := Real.log_mul nonzero_one nonzero_one

theorem triangle_f: ∀ (x y z : α), dis_f x z ≤ dis_f x y + dis_f y z :=
let r := Real.log
λ x y z ↦ by {
  unfold dis_f
  exact calc 
      f (r (A x z))             (r (A z x))
    ≤ f (r (A x y) + r (A y z)) (r (A z x))             := fmonotone _ _ _ _ R (le_refl _)
_ ≤ f (r (A x y) + r (A y z)) (r (A z y) + r (A y x)) := fmonotone _ _ _ _ (le_refl _) R
_ = f (r (A x y) + r (A y z)) (r (A y x) + r (A z y)) := by rw [add_comm (r (A z y)) (r (A y x))]
_ ≤ _ := fsubadditive _ _ _ _
}
theorem triangle_max: ∀ (x y z : α), dis_max x z ≤ dis_max x y + dis_max y z :=
λ x y z ↦ calc
dis_max x z = max (Real.log (A x z))          (Real.log (A z x)) := rfl
_ ≤ max (Real.log (A x y * (A y z))) (Real.log (A z x)) := max_le_max log_le_mul (le_refl _)
_ ≤ max (Real.log ((A x y) * (A y z)))
                   (Real.log ((A z y) * (A y x))) := max_le_max (le_refl _) log_le_mul

_ = max (Real.log (A x y) + Real.log (A y z))
                   (Real.log (A z y) + Real.log (A y x)) := by {
                    rw [Real.log_mul _ _]
                    rw [Real.log_mul _ _]
                    exact nonzero_one
                    exact nonzero_one
                    exact nonzero_one
                    exact nonzero_one
                    }


         _ ≤ max (Real.log (A x y))
                   (Real.log (A y x)) +
               max (Real.log (A y z))
                   (Real.log (A z y)) := max_example _ _ _ _


noncomputable instance automatic_complexity_metric : MetricSpace α :=
{
        dist               := dis
        dist_self          := dis_self
        eq_of_dist_eq_zero := dis_eq_of
        dist_comm          := dis_comm
        dist_triangle      := triangle
        edist_dist         := sorry
    }
-- The definition of metric space has changed in Lean 4.
-- We only provide the fields needed according to Lean 3.
