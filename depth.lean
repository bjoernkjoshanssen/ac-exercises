import ring_theory.int.basic
import ring_theory.principal_ideal_domain

def sat_eq (a: ℤ×ℤ) (n: ℤ) (x: ℤ×ℤ) : Prop :=
a.1*x.1+a.2*x.2=n

theorem depth1 {a b x y k n : ℤ}
  (hsat:sat_eq (a,b) n (x,y)):
  sat_eq (a,b) n (x-k*b,y+k*a) :=
  calc  a*(x-k*b)+b*(y+k*a)
      = a*x+b*y: by ring
  ... = n: hsat
  
  theorem depth2 {a b n : ℤ}
  (h : gcd_monoid.gcd a b = 1): ∃ x y : ℤ, sat_eq (a,b) n (x,y) := by {
  have : ∃ (x y), gcd_monoid.gcd a b = a * x + b * y, from exists_gcd_eq_mul_add_mul _ _,
  cases this with x hx,
  cases hx with y hy,
  have : a*x+b*y = 1, from eq.trans hy.symm h,
  existsi [x*n, y*n],
  exact calc a*(x*n)+b*(y*n) = (a*x+b*y)*n: by ring
  ... = 1*n: by rw this
  ... = n: by ring
  }

theorem depth3 (a b n : ℤ) 
(h: gcd_monoid.gcd a b = 1): ∃ x y, ∀ k, sat_eq (a,b) n (x-k*b, y+k*a) :=
by {
  have : ∃ x y : ℤ, sat_eq (a,b) n (x,y), from depth2 h,
  cases this with x hx,
  cases hx with y hxy,
  existsi [x,y],
  intro k,
  exact depth1 hxy
}
