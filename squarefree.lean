import data.vector
import data.nat.basic
import data.pnat.prime

def squarefree {k:ℕ} (w: vector (fin 2) k) : Prop :=
∀ l:ℕ, l < w.length → ∀ v : vector (fin 2) l,
v.1 ≠ list.nil → ¬ list.is_infix (v.1 ++ v.1) w.1

instance (w : vector (fin 2) 4) : decidable (squarefree w)
:=
decidable_of_iff (∀ l:ℕ, l < w.length → ∀ v : vector (fin 2) l,
v.1 ≠ list.nil → ¬ list.is_infix (v.1 ++ v.1) w.1
) (by rw squarefree)

example : ∀ w : vector (fin 2) 4,
¬ squarefree w := dec_trivial
