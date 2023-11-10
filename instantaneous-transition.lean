import Mathlib.Tactic.LibrarySearch

def π : List (Fin 3) → List (Fin 2) :=
  λ y ↦ match y with
  |List.nil => List.nil
  | hd::tl =>
    dite (hd < 2)
      (λh ↦ ⟨hd.1,h⟩::π tl)
      (λ _ ↦ π tl)
  

example: π [1,1,0,0,0,1,2,1,0,1,0,1,1,0,1,1,1,1,0] = [1,1,0,0,0,1,1,0,1,0,1,1,0,1,1,1,1,0]
:= rfl
