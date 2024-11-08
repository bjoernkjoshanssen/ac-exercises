import Mathlib.Tactic.Ring
import Mathlib.Algebra.GCDMonoid.Basic
import Mathlib.RingTheory.Int.Basic

-- Solutions to Exercises 3.3 and 3.4.

def sat_eq' (a: ℤ×ℤ) (n: ℤ) (x: ℤ×ℤ) : Prop :=
a.1*x.1+a.2*x.2=n

def sat_eq3 (a b c: ℤ) (n: ℤ) (x y z: ℤ) : Prop :=
a*x+b*y+c*z=n

theorem depth1 {a b x y k n : ℤ}
  (hsat:sat_eq' (a,b) n (x,y)):
  sat_eq' (a,b) n (x-k*b,y+k*a) :=
  calc  a*(x-k*b)+b*(y+k*a)
      = a*x+b*y := by ring
  _ = n := hsat

  theorem depth2 {a b n : ℤ}
  (h : GCDMonoid.gcd a b = 1): ∃ x y : ℤ, sat_eq' (a,b) n (x,y) := by {
  have unknown: ∃ x y, GCDMonoid.gcd a b = a * x + b * y :=
    exists_gcd_eq_mul_add_mul _ _
  rcases unknown with ⟨x, hx⟩
  rcases hx with ⟨y, hy⟩
  have : a*x+b*y = 1 := Eq.trans hy.symm h
  use x*n
  use y*n
  --use [x*n, y*n]
  exact calc a*(x*n)+b*(y*n) = (a*x+b*y)*n := by ring
  _ = 1*n := by rw [this]
  _ = n := by ring
  }

theorem depth3 (a b n : ℤ)
(h: GCDMonoid.gcd a b = 1): ∃ x y, ∀ k, sat_eq' (a,b) n (x-k*b, y+k*a) :=
by {
  have : ∃ x y : ℤ, sat_eq' (a,b) n (x,y) := depth2 h
  rcases this with ⟨x, hx⟩
  rcases hx with ⟨y, hxy⟩
  use x
  use y
  intro k
  exact depth1 hxy
}

theorem solve3 (a b c n : ℤ) (
  h : GCDMonoid.gcd (GCDMonoid.gcd a b) c = 1)
  : ∃ x y z : ℤ, sat_eq3 a b c n x y z :=
  by {
  have h1: ∃ x y : ℤ, sat_eq' ((GCDMonoid.gcd a b),c) n (x,y) := depth2 h
  have h2: ∃ u v : ℤ, gcd a b = a*u+b*v := exists_gcd_eq_mul_add_mul _ _
  rcases h1 with ⟨x, hx⟩
  rcases hx with ⟨y, hxy⟩
  rcases h2 with ⟨u, hu⟩
  rcases hu with ⟨v, huv⟩
  have : (a*u+b*v) * x + c*y = n := by rwa [huv] at hxy
  use u*x
  use v*x
  use y
  exact calc _ =  (a*u+b*v) * x + c*y := by ring
           _ = _ := this
  }
