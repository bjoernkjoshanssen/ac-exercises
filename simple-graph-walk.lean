import combinatorics.simple_graph.connectivity

theorem second_vertex_in_walk {V : Type} (G : simple_graph V) (v0 v1 : V)
(hv : v0 ≠ v1)
(wa : G.walk v0 v1) : ∃ a : V, a ≠ v0 ∧ G.adj v0 a :=
  exists.elim (
    simple_graph.walk.exists_eq_cons_of_ne hv wa
  ) (
    λ a ha, exists.elim ha (
      λ hh hhh, exists.elim hhh (
        λ p' hp', 
        exists.intro a (
          and.intro (
            λ hav₀, G.loopless a (by {rw hav₀.symm at hh,exact hh,})) hh
        )
      )
    )
  )

def rewrite  {V : Type} {G : simple_graph V} {v₀ a w : V} {k:ℕ}
  (p' : {pp : G.walk a  w // pp.length=k}) (heq: a = v₀)
      : {pp : G.walk v₀ w // pp.length=k}
:=
by {rw heq at p',exact p',}

/-
Given v₀ and v₁, let w be neither of them.
For each walk from v₀ to w, there is an a with G.adj v₀ a or G.adj v₁ a, and a ¬∈{v₀,v₁}
For each walk from v₁ to w, there is an a with G.adj v₀ a or G.adj v₁ a, and a ¬∈{v₀,v₁}
-/

lemma reverse_cons_length {V : Type} {G : simple_graph V} (a v₀ w : V)
  (p' : G.walk a  w)
  (p  : G.walk v₀ w)
  (h: G.adj v₀ a) {k:ℕ}
  (hp: simple_graph.walk.length p = nat.succ k)
  (hp': p = simple_graph.walk.cons h p')
  : p'.length = k :=
  have p'.length.succ = k.succ, from
              calc _ = (simple_graph.walk.cons h p').length : (simple_graph.walk.length_cons _ _).symm
                ... = p.length                             : by rw hp'
                ... = _                                    : hp,
  nat.succ.inj this

theorem third_vertex_in_walk_induction {V : Type} {G : simple_graph V} (v₀ v₁ w : V)
  (hv : v₀ ≠ v₁) (hv₀w: v₀ ≠ w) (hv₁w: v₁ ≠ w) (n:ℕ):
(∀ p : G.walk v₀ w, p.length = n → ∃ a, (G.adj v₀ a ∨ G.adj v₁ a) ∧ a ≠ v₀ ∧ a ≠ v₁) ∧
(∀ p : G.walk v₁ w, p.length = n → ∃ a, (G.adj v₀ a ∨ G.adj v₁ a) ∧ a ≠ v₀ ∧ a ≠ v₁)
:=
nat.rec_on n (
  and.intro
    (λ _ hpl, false.elim (hv₀w (simple_graph.walk.eq_of_length_eq_zero hpl)))
    (λ _ hpl, false.elim (hv₁w (simple_graph.walk.eq_of_length_eq_zero hpl)))
) (λ k h_ind, (and.intro (
  λ p hp,
  exists.elim (simple_graph.walk.exists_eq_cons_of_ne hv₀w p) (
    λ a ha, exists.elim ha (
      λ h hh, exists.elim hh (
        exists.elim hh (
          λ p' hp' _ _, 
          have h_can_ind: p'.length = k, from reverse_cons_length a v₀ w p' p h hp hp',
          --rw the type of p' when a is v₀ or v₁
          (classical.em (a = v₀)).elim (λheq, -- case a is v₀. 
              h_ind.1 ((rewrite ⟨p',h_can_ind⟩ heq)) (rewrite ⟨p',h_can_ind⟩ heq).2
          ) ( λ hneq0, 
            (classical.em (a=v₁)).elim (λheq, -- case a is v₁ (basically identical to the v₀ case)
              h_ind.2 ((rewrite ⟨p',h_can_ind⟩ heq)) (rewrite ⟨p',h_can_ind⟩ heq).2
            ) (λ hneq1,-- case a is neither v₀ nor v₁
              exists.intro a (and.intro (or.inl h) (and.intro hneq0 hneq1))
            )
          )
        )
      )
    )
  )
) (
    λ p hp,-- exactly same with v₀, v₁ switched:
    exists.elim (simple_graph.walk.exists_eq_cons_of_ne hv₁w p) (
      λ a ha, exists.elim ha (
        λ h hh, exists.elim hh (
          exists.elim hh (
            λ p' hp' _ _, 
          have h_can_ind: p'.length = k, from reverse_cons_length a v₁ w p' p h hp hp',
              (classical.em (a=v₀)).elim (--rw the type of p' under cases of whether a is v₀ or v₁ or neither
                λheq, h_ind.1 ((rewrite ⟨p',h_can_ind⟩ heq)) (rewrite ⟨p',h_can_ind⟩ heq).2
              ) (
                λ hneq0, 
                (classical.em (a=v₁)).elim (
                  λ heq, h_ind.2 ((rewrite ⟨p',h_can_ind⟩ heq)) (rewrite ⟨p',h_can_ind⟩ heq).2
                ) (λ hneq1,
                  exists.intro a (and.intro (
                    or.inr h
                  ) (and.intro hneq0 hneq1))
                )
              )
            )
          )
        )
      )
    )
  )
)

theorem third_vertex_in_walk {V : Type} (G : simple_graph V) (v₀ v₁ w : V)
  (hv : v₀ ≠ v₁) (hv₀w: v₀ ≠ w) (hv₁w: v₁ ≠ w):
  (∀ p : G.walk v₀ w,  ∃ a, (G.adj v₀ a ∨ G.adj v₁ a) ∧ a ≠ v₀ ∧ a ≠ v₁) ∧
  (∀ p : G.walk v₁ w,  ∃ a, (G.adj v₀ a ∨ G.adj v₁ a) ∧ a ≠ v₀ ∧ a ≠ v₁) :=

  and.intro (
    λ p, (third_vertex_in_walk_induction v₀ v₁ w hv hv₀w hv₁w p.length).1 p rfl
  ) (
    λ p, (third_vertex_in_walk_induction v₀ v₁ w hv hv₀w hv₁w p.length).2 p rfl
  )
