def kbo_alpha_morph (l:Nat) : Fin l.succ → List (Fin l.succ) :=
λ i ↦ ite (i.1=l) [0] [0,i+1]  

def kbo_morph (l:Nat): List (Fin l.succ) → List (Fin l.succ) :=
λ x ↦ match x with
| List.nil => List.nil
| List.cons hd tl =>
(
  (kbo_alpha_morph l hd) ++ (kbo_morph l tl)
)

theorem is_morph (l:Nat) (x: List (Fin l.succ)) : ∀ y : List (Fin l.succ),
kbo_morph l (x ++ y) = kbo_morph l x ++ kbo_morph l y :=
List.recOn x (λ y ↦ rfl) (
  λ hd tl h_ind y ↦
  show kbo_morph l (hd :: tl ++ y) = kbo_morph l (hd :: tl) ++ kbo_morph l y from
  calc _ = (kbo_alpha_morph l hd) ++ kbo_morph l (tl ++ y)            := rfl
       _ = (kbo_alpha_morph l hd) ++ (kbo_morph l tl ++ kbo_morph l y):= by rw [h_ind y]
       _ = ((kbo_alpha_morph l hd) ++ kbo_morph l tl) ++ kbo_morph l y:= (List.append_assoc _ _ _).symm
       _ = _ := rfl
)
