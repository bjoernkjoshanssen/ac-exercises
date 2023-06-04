import tactic.ring
import tactic.linarith
import data.vector.basic

/- We define primitive words and prove that

* list.repeat a k.succ.succ is not primitive,
* any word of length 0 or 1 is primitive
* if 01ⁿ is a concatenation of two nonempty words u,v then v starts with a 1
  (so 01ⁿ is not primitive...)

-/

def power' (u : list (fin 2)) (k:ℕ) :
                     list (fin 2) :=
  nat.rec_on k list.nil (λ n pow_ind, u ++ pow_ind)

theorem power_length' (u : list (fin 2)) (k:ℕ) :
  (power' u k).length = k * u.length
  :=
  nat.rec_on k (by {rw zero_mul,refl,}) (
    λ n h_ind, calc
    _ = u.length + (power' u n).length : u.length_append (power' u n)
  ... = nat.succ n * u.length : by {rw [h_ind],ring,}
)

def nontrivial_power' (x : list (fin 2)) :=
∃ k : ℕ, ∃ u:list (fin 2), 1 ≤ u.length  ∧ x = (power' u k.succ.succ)

def c' : list (fin 2) := [0,0]

example : nontrivial_power' [0,0,0,0] := by {
  existsi 0, existsi c', split, dec_trivial,dec_trivial,
}

def primitive' (x : list (fin 2)) := ¬ nontrivial_power' x

theorem short_primitive' (x: list (fin 2)) (h: x.length ≤ 1) : primitive' x :=
by {
    intro h_contra, cases h_contra with k hk, cases hk with u huu,cases huu with huu_left hu,
  have hh: 2 ≤ 1, from calc
           2 = 2      * 1                     : rfl
         ... ≤ 2 * u.length                     : mul_le_mul_left' (huu_left) _
         ... ≤ k.succ.succ * u.length           : mul_le_mul_right'  (nat.succ_le_succ (nat.succ_le_succ (zero_le _))) _
         ... = (power' u k.succ.succ).length : (power_length' _  _).symm
         ... ≤ 1                              : by {rw ← hu,exact h,},
  exact nat.not_succ_le_self 1 hh
}

theorem list_nil_primitive' : primitive' list.nil :=
  have list.nil.length ≤ 1, by calc _ = 0: rfl ... ≤ 1: zero_le_one, 
  short_primitive' _ this 

theorem singleton_primitive' : primitive' [0] :=
  have [0].length ≤ 1, by calc _ = 1: rfl ... ≤ 1: le_refl _, 
  short_primitive' _ this 

theorem repeat_is_power' {k:ℕ} : list.repeat (0:fin 2) k.succ.succ
                                  = (power' [0] k.succ.succ) :=
nat.rec_on k rfl (
  λ n h_ind,
  calc _ = [(0:fin 2)] ++ list.repeat (0:fin 2) (nat.succ n).succ: rfl
     ... = [(0:fin 2)] ++ (power' [0] (nat.succ n).succ): by {rw h_ind}
)

theorem repeat_not_primitive' {k:ℕ} : nontrivial_power' (list.repeat (0:fin 2) k.succ.succ)
:= by {
  unfold nontrivial_power',
  existsi k,
  existsi ([0]: list (fin 2)),
  split,
  exact le_refl _,
  exact repeat_is_power'
}

theorem list_nil_length : (list.nil : list (fin 2)).length = 0 := by {
  have : (list.nil : list (fin 2)).length = 0 ↔ list.nil = list.nil, from list.length_eq_zero,
  refine this.mpr _,refl, -- cool use of refine!
  }

example (k:ℕ) (h:1≤ k): k ≠ 0 := nat.one_le_iff_ne_zero.mp h

theorem list_ne_nil (x:list (fin 2)) (h:x.length ≠ 0):  x ≠ list.nil :=
  λ hn, by {rw hn at h,rw list_nil_length at h,exact h (eq.refl 0),}


theorem middle_of_list_repeat {b : fin 2} {v : list (fin 2)} {u : list (fin 2)}:
list.repeat 1 (u.length+v.length).succ = u ++ (b :: v) → b = 1 :=
list.rec_on u (
  by {
    rw [list_nil_length, zero_add, list.nil_append],
    intro h, refine list.head_eq_of_cons_eq _,
    exact v, exact (list.repeat 1 (v.length)), symmetry,exact h,
  }
) (
  by {
    intros _ tl h_ind hyp,    
    have help : (tl.length + 1 + v.length) = (tl.length + v.length).succ,
    from (list.length tl).succ_add (list.length v),
    rw [list.cons_append,list.length_cons,help] at hyp,
    exact h_ind (list.tail_eq_of_cons_eq hyp),
  }
)


theorem why_01ⁿ_is_primitive (u v : list (fin 2)) (a b : fin 2)
(h: 0 :: list.repeat 1 (u.length+v.length).succ = (a :: u) ++ (b :: v))
: a = 0 ∧ b = 1 := by {
  split,
  have :[a] = [0], from calc
        [a] = (a :: (u ++ (b :: v))).take 1: rfl
        ... = ((a :: u) ++ (b :: v)).take 1: by rw list.cons_append
        ... = (0 :: list.repeat 1 (u.length+v.length).succ).take 1: by rw h,
  exact list.singleton_inj.mp this,
  exact middle_of_list_repeat (list.tail_eq_of_cons_eq h)
}

lemma power_manipulations (l:ℕ) {u v:list (fin 2)} {a:fin 2}  (hv: u = a :: v):
       power' u l.succ.succ = (a :: v) ++ (a :: (v ++ power' u l)) :=
      have P: power' u l.succ.succ = (a :: v) ++ ((a :: v) ++ power' u l), by {
        rw ←hv, refl, 
      },
      by {rw list.cons_append at P, exact P,}

lemma power_succ (l:ℕ) (u:list (fin 2))
: (power' u l.succ.succ).length = (power' u l).length + u.length + u.length
:= by {rw power_length',rw power_length',rw nat.succ_mul,rw nat.succ_mul,}

lemma length_manipulations {k l:ℕ} {u v:list (fin 2)} {a:fin 2}  (hv: u = a :: v) (hu1: 1 ≤ u.length)
 (hu2: 0 :: list.repeat 1 k.succ                                     = power' u l.succ.succ) :
       0 :: list.repeat 1 (v.length + (v ++ power' u l).length).succ = a :: v ++ a :: (v ++ power' u l) :=

      have PR0: 0 :: list.repeat 1 k.succ = (a :: v) ++ (a :: (v ++ power' u l)),
                              from calc _ = power' u l.succ.succ: hu2
                                      ... = _                   : power_manipulations l hv,

      have R: ((0:fin 2) :: list.repeat 1 k.succ).length -- repeat only
                          = k.succ.succ, by {rw list.length_cons,rw list.length_repeat,},
      have PR: (power' u l.succ.succ).length = k.succ.succ, by {rw hu2 at R,exact R,},--both
      
      have PR1: k.succ.succ = (v.length + (v ++ power' u l).length).succ.succ, from
          calc            _ = (power' u l.succ.succ).length             : PR.symm
                        ... = (power' u l).length + u.length + u.length : power_succ l u
                        ... = _ : by {rw list.length_append,rw hv,rw list.length_cons,ring_nf,},
      
      by {rw ← nat.succ_injective (nat.succ_injective PR1),exact PR0,}

theorem primitive_words_of_length_two_or_more (k:ℕ) :
  ∃ x : list (fin 2), x.length = k.succ.succ ∧ primitive' x :=
  by {
      existsi ((0:fin 2)::list.repeat 1 k.succ),
      split,rw list.length_cons,
      rw ← nat.succ_eq_add_one,rw list.length_repeat,
      unfold primitive',unfold nontrivial_power',intro h_contra,cases h_contra with l hl,
      cases hl with u hu,

      have : u.length ≠ 0, from nat.one_le_iff_ne_zero.mp hu.1,
      have hnl: u ≠ list.nil, from list_ne_nil _ this,
      have : ∃ a: fin 2, ∃ v: list (fin 2), u = a :: v, from list.exists_cons_of_ne_nil hnl,
      cases this with a ha, cases ha with v hv,

      have H0: 0 :: list.repeat 1 (v.length + (v ++ power' u l).length).succ
           = a :: v ++ a :: (v ++ power' u l),
        from length_manipulations hv hu.1 hu.2,

      have : a = 0 ∧ a = 1, from why_01ⁿ_is_primitive v (v ++ power' u l) a a H0,
      exact fin.zero_ne_one (eq.trans this.1.symm this.2)

  }

lemma succ_succ {n:ℕ}(h:n≠0 )(hn:n≠1 ): ∃ k:ℕ, n = k.succ.succ := 
  by {
    have hnn: ∃ l:ℕ, n = l.succ, from nat.exists_eq_succ_of_ne_zero h,
    cases hnn with l hl,
    have hz: l ≠ 0, by{by_contra,rw h at hl,exact hn hl,}, 
    have hm: ∃ m:ℕ, l = m.succ, from nat.exists_eq_succ_of_ne_zero hz,
    cases hm with s hs, existsi s,rw ← hs,exact hl,
  }


theorem primitive_words_of_every_length (n:ℕ) :
  ∃ x : list (fin 2), x.length = n ∧ primitive' x :=
  (em (n = 0)).elim (
    by {
      intro h, existsi list.nil,split,rw h,refl,exact list_nil_primitive',
    }
  ) (
    λ h, (em (n=1)).elim (
      by {
        intro h1,existsi ([0]: list (fin 2)),split,rw h1,refl,
        exact short_primitive' _ (le_refl _)
      }
    ) (
      λ hn, by {
        cases (succ_succ h hn) with k hk,
        have : ∃ (x : list (fin 2)), x.length = k.succ.succ ∧ primitive' x,
        from primitive_words_of_length_two_or_more k,
        rw ← hk at this,exact this,
      }
    )
  )
