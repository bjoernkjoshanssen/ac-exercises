
def π : list (fin 3) → list (fin 2) :=
  λ y, list.rec_on y list.nil (λ hd, λ tl, λ π_ind,
    dite (hd < 2)
      (λh, ⟨hd.1,h⟩::π_ind)
      (λh, π_ind)
  )

example: π [1,1,0,0,0,1,2,1,0,1,0,1,1,0,1,1,1,1,0] = [1,1,0,0,0,1,1,0,1,0,1,1,0,1,1,1,1,0]
:= dec_trivial
