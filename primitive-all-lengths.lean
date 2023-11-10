import Mathlib.Data.List.Basic
import Mathlib.Tactic.Ring

/- We deFine primitive words and prove that

* List.replicate a k.succ.succ is not primitive,
* any word of length 0 or 1 is primitive
* if 01ⁿ is a concatenation of two nonempty words u,v then v starts with a 1
  (so 01ⁿ is not primitive_)

-/

def power' (u : List (Fin 2)) (k:ℕ) :
                     List (Fin 2) :=
  Nat.recOn k List.nil (λ _ pow_ind ↦ u ++ pow_ind)

theorem power_length' (u : List (Fin 2)) (k:ℕ) :
  (power' u k).length = k * u.length
  :=
  Nat.recOn k (by {rw [Nat.zero_mul];exact rfl}) (
    λ n h_ind ↦ (calc
    _ = u.length + (power' u n).length := u.length_append (power' u n)
    _ = Nat.succ n * u.length := by {
      rw [h_ind]
      rw [Nat.succ_eq_add_one]
      ring
    }
  )
)

def nontrivial_power' (x : List (Fin 2)) :=
∃ k : ℕ, ∃ u:List (Fin 2), 1 ≤ u.length  ∧ x = (power' u k.succ.succ)

def c' : List (Fin 2) := [0,0]

example : nontrivial_power' [0,0,0,0] := by {
  exists 0; exists c'
}

def primitive' (x : List (Fin 2)) := ¬ nontrivial_power' x

theorem short_primitive' (x: List (Fin 2)) (h: x.length ≤ 1) : primitive' x :=
by {
    intro h_contra
    unfold nontrivial_power' at h_contra
    rcases h_contra with ⟨k, hk⟩
    rcases hk with ⟨u, huu⟩
    rcases huu with ⟨huu_left, hu⟩
    have hh: 2 ≤ 1 := calc
           2 = 2      * 1                     := (mul_one 2).symm
         _ ≤ 2 * u.length                     := mul_le_mul_left' (huu_left) _
         _ ≤ k.succ.succ * u.length           := mul_le_mul_right'  (Nat.succ_le_succ (Nat.succ_le_succ (zero_le _))) _
         _ = (power' u k.succ.succ).length := (power_length' _  _).symm
         _ ≤ 1                              := by {rw [← hu];exact h}
    exact Nat.not_succ_le_self 1 hh
}

theorem List_nil_primitive' : primitive' List.nil :=
  have : List.nil.length ≤ 1 := by (calc
  _ = 0 := rfl
  _ ≤ 1 := zero_le_one)
  short_primitive' _ this

theorem singleton_primitive' : primitive' [0] :=
  have : [0].length ≤ 1 := by (calc
  _ = 1 := rfl
  _ ≤ 1 := le_refl _)
  short_primitive' _ this

theorem repeat_is_power' {k:ℕ} :
  List.replicate k.succ.succ (0:Fin 2) = (power' [0] k.succ.succ) :=
Nat.recOn k rfl (
  λ n h_ind ↦
  calc _ = [(0:Fin 2)] ++ List.replicate (Nat.succ n).succ (0:Fin 2) := rfl
     _ = [(0:Fin 2)] ++ (power' [0] (Nat.succ n).succ) := by {rw [h_ind]}
)

theorem repeat_not_primitive' {k:ℕ} : nontrivial_power' (List.replicate k.succ.succ (0:Fin 2))
:= by {
  unfold nontrivial_power'
  exists k
  exists ([0]: List (Fin 2))
  constructor
  exact le_refl _
  exact repeat_is_power'
}

theorem List_nil_length : (List.nil : List (Fin 2)).length = 0 := by {
  have : (List.nil : List (Fin 2)).length = 0 ↔ List.nil = List.nil := List.length_eq_zero
  refine this.mpr rfl
  }

example (k:ℕ) (h:1≤ k): k ≠ 0 := Nat.one_le_iff_ne_zero.mp h

theorem List_ne_nil (x:List (Fin 2)) (h:x.length ≠ 0):  x ≠ List.nil :=
  λ hn ↦ by {
    rw [hn] at h
    rw [List_nil_length] at h
    exact h (Eq.refl 0)
  }


theorem middle_of_List_repeat {b : Fin 2} {v : List (Fin 2)} {u : List (Fin 2)}:
List.replicate (u.length+v.length).succ 1= u ++ (b :: v) → b = 1 :=
List.recOn u (
  by {
    rw [List_nil_length, zero_add, List.nil_append]
    intro h;
    unfold List.replicate at h
    refine List.head_eq_of_cons_eq h.symm
  }
) (
  by {
    intros _ tl h_ind hyp
    have help : (tl.length + 1 + v.length) = (tl.length + v.length).succ :=
    (List.length tl).succ_add (List.length v)
    rw [List.cons_append,List.length_cons,help] at hyp
    exact h_ind (List.tail_eq_of_cons_eq hyp)
  }
)


theorem why_01n_is_primitive (u v : List (Fin 2)) (a b : Fin 2)
(h: 0 :: List.replicate (u.length+v.length).succ 1 = (a :: u) ++ (b :: v))
: a = 0 ∧ b = 1 := by {
  constructor
  have :[a] = [0] := calc
        [a] = (a :: (u ++ (b :: v))).take 1 := rfl
        _ = ((a :: u) ++ (b :: v)).take 1   := by rw [List.cons_append]
        _ = (0 :: List.replicate (u.length+v.length).succ 1).take 1 := by rw [h]
  exact List.singleton_inj.mp this
  exact middle_of_List_repeat (List.tail_eq_of_cons_eq h)
}

lemma power_manipulations (l:ℕ) {u v:List (Fin 2)} {a:Fin 2}  (hv: u = a :: v):
       power' u l.succ.succ = (a :: v) ++ (a :: (v ++ power' u l)) :=
      have P: power' u l.succ.succ = (a :: v) ++ ((a :: v) ++ power' u l) := by {
        rw [←hv]; rfl
      }
      by {rw [List.cons_append] at P; exact P}

lemma power_succ (l:ℕ) (u:List (Fin 2))
: (power' u l.succ.succ).length = (power' u l).length + u.length + u.length
:= by rw [power_length',power_length',Nat.succ_mul,Nat.succ_mul]

lemma length_manipulations {k l:ℕ} {u v:List (Fin 2)} {a:Fin 2}  (hv: u = a :: v)
 (hu2: 0 :: List.replicate k.succ 1                                     = power' u l.succ.succ) :
       0 :: List.replicate (v.length + (v ++ power' u l).length).succ 1 = a :: v ++ a :: (v ++ power' u l) :=

      have PR0: 0 :: List.replicate k.succ 1 = (a :: v) ++ (a :: (v ++ power' u l)) := (calc
      _ = power' u l.succ.succ  := hu2
      _ = _                     := power_manipulations l hv)

      have R: ((0:Fin 2) :: List.replicate k.succ 1).length -- repeat only
                          = k.succ.succ := by rw [List.length_cons,List.length_replicate]
      have PR: (power' u l.succ.succ).length = k.succ.succ := by {rw [hu2] at R;exact R}--both

      have PR1: k.succ.succ = (v.length + (v ++ power' u l).length).succ.succ := (calc
      _ = (power' u l.succ.succ).length             := PR.symm
      _ = (power' u l).length + u.length + u.length := power_succ l u
      _ = _ := by {
        rw [List.length_append,hv,List.length_cons]
        rw [Nat.add_succ,Nat.add_succ]
        apply congrArg Nat.succ
        rw [Nat.succ_eq_add_one]
        ring
      }
      )

      by {
        rw [← Nat.succ_injective (Nat.succ_injective PR1)]
        exact PR0
      }

theorem primitive_words_of_length_two_or_more (k:ℕ) :
  ∃ x : List (Fin 2), x.length = k.succ.succ ∧ primitive' x :=
  by {
      exists ((0:Fin 2)::List.replicate k.succ 1)
      constructor
      rw [List.length_cons]
      rw [List.length_replicate]
      unfold primitive';unfold nontrivial_power';intro h_contra;
      rcases h_contra with ⟨l,hl⟩
      rcases hl with ⟨u, hu⟩

      have : u.length ≠ 0 := Nat.one_le_iff_ne_zero.mp hu.1
      have hnl: u ≠ List.nil := List_ne_nil _ this
      have : ∃ a: Fin 2, ∃ v: List (Fin 2), u = a :: v := List.exists_cons_of_ne_nil hnl
      rcases this with ⟨a, ha⟩
      rcases ha with ⟨v, hv⟩

      have H0: 0 :: List.replicate (v.length + (v ++ power' u l).length).succ 1
           = a :: v ++ a :: (v ++ power' u l) := length_manipulations hv hu.2

      have : a = 0 ∧ a = 1 := why_01n_is_primitive v (v ++ power' u l) a a H0
      exact Fin.zero_ne_one (Eq.trans this.1.symm this.2)

  }

lemma succ_succ {n:ℕ}(h:n≠0 )(hn:n≠1 ): ∃ k:ℕ, n = k.succ.succ :=
  by {
    have hnn: ∃ l:ℕ, n = l.succ := Nat.exists_eq_succ_of_ne_zero h
    rcases hnn with ⟨l, hl⟩
    have hz: l ≠ 0 := by{
      intro hi
      rw [hi] at hl
      exact hn hl
    }
    have hm: ∃ m:ℕ, l = m.succ := Nat.exists_eq_succ_of_ne_zero hz
    rcases hm with ⟨s, hs⟩
    exists s
    rw [← hs]
    exact hl
  }


theorem primitive_words_of_every_length (n:ℕ) :
  ∃ x : List (Fin 2), x.length = n ∧ primitive' x :=
  (em (n = 0)).elim (
    by {
      intro h
      exists List.nil
      constructor
      rw [h]
      rfl
      exact List_nil_primitive'
    }
  ) (
    λ h ↦ (em (n=1)).elim (
      by {
        intro h1
        exists ([0]: List (Fin 2))
        constructor
        rw [h1]
        rfl
        exact short_primitive' _ (le_refl _)
      }
    ) (
      λ hn ↦ by {
        rcases (succ_succ h hn) with ⟨k, hk⟩
        have : ∃ (x : List (Fin 2)), x.length = k.succ.succ ∧ primitive' x := primitive_words_of_length_two_or_more k
        rw [← hk] at this
        exact this
      }
    )
  )
