import Acmoi.HydePrelim
import Acmoi.QuasTheorem

/-!

  # Kjos-Hanssen / Quas theorem

We prove that permutation automatic complexity A^perm can be characterized by
A^perm(x) = |x| + 1.
The upper bound was asserted in [SAM] 2017.
and the lower bound uses [Quas] 2020.
The full result appears as Theorems 4.41 and 4.42 in [ACMOI] 2024.
-/

open Finset Fintype Nat Classical

theorem least_not_in_range_nonempty {n q : ℕ} (h : q < n) (f : Fin (q + 1) → Fin (n + 1)) :
    (filter (fun k ↦ ∀ l, f l ≠ k) univ).Nonempty := by
  by_contra h₂
  simp at h₂
  have (k : Fin (n+1)) : k ∉  filter (fun k ↦ ∀ l, ¬ f l = k) univ := by
      simp at h₂ ⊢
      apply h₂
  simp at this
  have := Fintype.card_le_of_surjective f this
  simp at this
  omega

/-- The least element not hit by a function into a larger set. -/
def least_not_in_range {n q : ℕ} (h : q < n) (f : Fin (q+1) → Fin (n+1)) : Fin (n+1) :=
  min' (filter (fun k => ∀ l, f l ≠ k) univ) (least_not_in_range_nonempty h _)

/-- The DFA `δ` witnessing the permutation-automatic complexity
 of a word `w`. -/
noncomputable def Perm_δ {A : Type*} {n : ℕ} (w : Fin n → A)
    (a : A) (q : Fin (n+1)) :  (Fin (n+1)) := match q with
| 0 => by
  by_cases hn : n = 0
  · exact 0
  · by_cases h₀ : a = w ⟨0, by omega⟩
    · exact ⟨1, by omega⟩
    · exact 0
| Fin.mk (succ q) hq => by
  by_cases h₀ : ∃ (h₁ : q+1 < n), a = w ⟨q+1, h₁⟩
  · exact ⟨q+2, by
      obtain ⟨h₁,_⟩ := h₀
      exact Order.lt_add_one_iff.mpr h₁⟩
  · have hqn : q < n := by omega
    exact least_not_in_range
      hqn (fun i => Perm_δ w a ⟨i.1, by omega⟩)

/-- The minimum of a set `s` belongs to `s`. This version does not require mentioning `s` explicitly. -/
theorem mem_of_eq_min {α : Type*} [LinearOrder α] {s : Finset α} {H : s.Nonempty} {a : α} (h : a = min' s H) : a ∈ s :=
  h ▸ min'_mem s H

/-- If `q+2` is the least element not in the range of a function with domain size `m+1` then `q+2≤ m+1`. -/
theorem least_not_in_range_small {n : ℕ} {q : ℕ} {δa : Fin (n+1) → Fin (n+1)}
    {l : Fin (n + 1)} {m : ℕ} (hm : ↑l = m + 1)
    (hq₂ : q + 2 < n + 1)
    (hc : (least_not_in_range (by omega) fun i : Fin (m + 1) ↦ δa ⟨i.1, by omega⟩) = ⟨q + 1, by omega⟩ + 1) :
    -- Fintype.card (Fin (q + 2)) ≤ Fintype.card (Fin (m + 1))
    q + 2 ≤ m + 1 := by
  have : ∀ x : Fin (q+2), ∃ y : Fin (m+1),
    δa ⟨y.1, by omega⟩ = ⟨x.1, by omega⟩ := by
    intro x
    by_contra H
    push Not at H
    unfold least_not_in_range at hc
    have : (⟨q+2, hq₂⟩ : Fin (n+1)) ≤ ⟨x.1, by omega⟩ := by
        rw [Fin.add_def] at hc
        simp at hc
        have : q + 1 + 1 < n + 1 := hq₂ -- as above
        have : (q+1+1) % (n+1) = q+1+1 := by exact mod_eq_of_lt this
        simp_rw [this] at hc
        rw [← hc]
        apply min'_le
        simp
        tauto
    have : q + 2 ≤ x.1 := this
    have : x.1 < q + 2 := x.2
    omega
  sorry
  -- let f := fun k : Fin (q+2) => (@Fin.find (m+1)
  --   (fun y : Fin (m+1) =>
  --       δa ⟨y.1, by omega⟩ = ⟨k.1, by omega⟩) _
  --   ).get (Fin.isSome_find_iff.mpr <| this k)
  -- have : Function.Injective f := by
  --   intro u v huv
  --   unfold f at huv
  --   have hu := @Fin.find_spec (m+1)
  --       (fun y : Fin (m+1) =>
  --       δa ⟨y.1, by omega⟩ = ⟨u.1, by omega⟩) _
  --       (@Option.get (Fin (m + 1))
  --       (Fin.find fun y ↦ δa ⟨↑y, by omega⟩ = ⟨↑u, by omega⟩) (by
  --           exact Fin.isSome_find_iff.mpr (this u)
  --       ) : Fin (m + 1)) (by aesop)
  --   have hv := @Fin.find_spec (m+1)
  --       (fun y : Fin (m+1) =>
  --       δa ⟨y.1, by omega⟩ = ⟨v.1, by omega⟩) _
  --       (@Option.get (Fin (m + 1))
  --       (Fin.find fun y ↦ δa ⟨↑y, by omega⟩ = ⟨↑u, by omega⟩) (by
  --           exact Fin.isSome_find_iff.mpr (this u)
  --       ) : Fin (m + 1)) (by aesop)
  --   simp at hu hv
  --   suffices (⟨u.1, by omega⟩ : Fin (n+1)) = ⟨v.1, by omega⟩ by aesop
  --   apply hu.symm.trans
  --   tauto
  -- exact Fintype.card_fin (q + 2) ▸ Fintype.card_fin (m + 1) ▸ Fintype.card_le_of_injective f this

/-- The DFA `Perm_δ` does not advance by more than one at each step. -/
theorem Perm_δ_bound {A : Type*} {n : ℕ} (w : Fin n → A) (a : A) {r : Fin (n+1)}
    (hqn : r ≠ Fin.last n):
    (Perm_δ w a r) ≤ r + 1 := match r with
  | 0 => by
    by_cases hn : n = 0
    · subst hn
      simp
    · by_cases h₀ : a = w ⟨0, by omega⟩
      · subst h₀
        unfold Perm_δ
        simp
        rw [dif_neg hn]
        exact le_of_eq <| Fin.eq_mk_iff_val_eq.mpr <| .symm <| one_mod_eq_one.mpr <| by simp;omega
      · unfold Perm_δ
        rw [dif_neg hn]
        simp
        exact if_neg h₀ ▸ Fin.zero_le 1
  | Fin.mk (succ q) hq => by
    have hn : n ≠ 0 := by omega
    by_cases h₀ : ∃ (h₁ : q+1 < n), a = w ⟨q+1, h₁⟩
    · apply le_of_eq
      unfold Perm_δ
      rw [dif_pos h₀]
      apply Fin.eq_mk_iff_val_eq.mpr
      symm
      simp
      obtain ⟨a,b⟩ := h₀
      omega
    · have hqn' : q < n := by omega
      unfold Perm_δ
      rw [dif_neg h₀]
      simp
      unfold least_not_in_range
      apply min'_le
      simp
      intro l
      unfold Perm_δ
      rw [dif_neg hn]
      by_cases hl : l = 0
      · subst hl
        simp
        intro hc
        by_cases h₁ : a = w ⟨0, by omega⟩
        · by_cases h₂ : q = n - 1
          · subst h₂
            simp_all
            conv at hc =>
              left
              change ⟨1, by omega⟩
            conv at hc =>
              right
              rw [Fin.add_def] -- yes!!
            simp at hc -- yes!
            have : n - 1 + 1 = n := by omega
            rw [this] at hc
            simp at hc
          rw [h₁] at hc
          simp at hc
          conv at hc =>
              left
              change ⟨1, by omega⟩
          conv at hc =>
              right
              right
              change ⟨1 % (n+1), by apply mod_lt 1;omega⟩
          conv at hc =>
              right
              rw [Fin.add_def]
          simp at hc
          have : q + 1 + 1 < n + 1 := by omega
          have : (q + 1 + 1) % (n + 1) = q + 1 + 1 := by exact mod_eq_of_lt this
          rw [this] at hc
          omega
        · rw [if_neg h₁] at hc
          conv at hc =>
              left
              change 0
          conv at hc =>
              right
              rw [Fin.add_def]
          simp at hc
          sorry
          -- apply congrArg (fun x => x.1) at hc
          -- simp at hc
          -- by_cases h : q + 1 + 1 < n + 1
          -- · have : (q + 1 + 1) % (n + 1) = q + 1 + 1 := by exact mod_eq_of_lt h
          --   rw [this] at hc
          --   omega
          -- · have : q = n - 1 := by omega
          --   subst this
          --   apply hqn
          --   have : (n-1).succ = n := by omega
          --   simp_rw [this]
          --   rfl
      · have ⟨m,hm⟩ : ∃ m, l.1 = m + 1 := exists_eq_succ_of_ne_zero fun hc => hl <| Fin.eq_of_val_eq hc
        simp_rw [hm]
        by_cases h₁ : ∃ (h₁ : m + 1 < n), a = w ⟨m + 1, h₁⟩
        · rw [dif_pos h₁]
          -- easyish again
          intro hc
          rw [Fin.add_def] at hc
          simp at hc
          by_cases h : q + 1 + 1 < n + 1
          · have : (q + 1 + 1) % (n + 1) = q + 1 + 1 := by exact mod_eq_of_lt h
            rw [this] at hc
            omega
          · have : q = n - 1 := by omega
            subst this

            have : n - 1 + 1 + 1 = n + 1 := by omega
            rw [this] at hc
            simp at hc
        · have hq₂ : q + 2 < n + 1 := by
            suffices q + 1 ≠ n by omega
            contrapose hqn
            simp_all
            exact rfl
          rw [dif_neg h₁]
          intro hc
          have : q + 2 ≤ m + 1 :=
            @least_not_in_range_small n q _ ⟨l.1, by omega⟩ m (by rw [hm]) hq₂ hc
          clear hc h₁ h₀ hqn hq hqn' a w A r hn hl hq₂
          omega

/-- Casting the DFA `Perm_δ` into an NFA. -/
noncomputable def Permδ {A : Type*} {n : ℕ} (w : Fin n → A) (a : A) (q : Fin (n+1)) :  Set (Fin (n+1)) :=
    {Perm_δ w a q}

/-- The DFA `Perm_δ w` does accept the word `w`.  -/
theorem accepts_perm  {A : Type*} {n : ℕ} (w : Fin n → A) :
    accepts_word_path (Permδ w) w 0 (Fin.last n) id := by
  constructor
  · rfl
  · constructor
    · rfl
    · intro i
      unfold Permδ Perm_δ
      simp
      by_cases hn : n = 0
      · subst hn
        exact (not_lt_zero i.2).elim
      · simp_rw [dif_neg hn]
        by_cases h₀ : w i = w ⟨0, by omega⟩
        · rw [if_pos h₀]
          by_cases h₁ : i = ⟨0, by omega⟩
          · subst h₁
            simp
            rfl
          · have ⟨m,hm⟩ : ∃ m, i.1 = m + 1 := by
                apply exists_eq_succ_of_ne_zero
                contrapose h₁
                exact Fin.eq_mk_iff_val_eq.mpr h₁
            have : i.castSucc = ⟨m+1, by omega⟩ := Fin.eq_mk_iff_val_eq.mpr hm
            simp_rw [this]
            by_cases h : ∃ (h₁ : m + 1 < n), w i = w ⟨m + 1, h₁⟩
            · simp_rw [dif_pos h]
              aesop
            · simp_rw [dif_neg h]
              unfold least_not_in_range
              simp
              push Not at h
              by_cases h₂ : m + 1 < n
              · exact (h h₂ <| Fin.eq_mk_iff_val_eq.mpr hm ▸ rfl).elim
              · have : i.1 ≥ n := by omega
                have := i.2
                omega
        · rw [if_neg h₀]
          have : i.1 ≠ 0 := by
            intro hc
            have : i = ⟨0,by omega⟩ := Fin.eq_mk_iff_val_eq.mpr hc
            rw [this] at h₀
            apply h₀
            rfl
          have ⟨m,hm⟩ : ∃ m, i.1 = m + 1 := by
                apply exists_eq_succ_of_ne_zero
                contrapose this
                simp_all
          have : i.castSucc = ⟨m+1, by omega⟩ := Fin.eq_mk_iff_val_eq.mpr hm
          simp_rw [this]
          by_cases h₂ : ∃ (h₁ : m + 1 < n), w i = w ⟨m + 1, h₁⟩
          · rw [dif_pos h₂]
            apply Fin.eq_mk_iff_val_eq.mpr
            simp;tauto
          · rw [dif_neg h₂]
            push Not at h₂
            by_cases h₃ : m + 1 < n
            · have := h₂ h₃
              exfalso
              apply this
              congr
              exact Fin.eq_mk_iff_val_eq.mpr hm
            · have := i.2
              omega

/-- If `Perm_δ w` accepts a word then it does so along a path that advances at most one step at a time. -/
theorem perm_path_bound {A : Type*} {n : ℕ} (v w : Fin n → A) (p : Fin (n + 1) → Fin (n + 1))
  (h : accepts_word_path (Permδ w) v 0 (Fin.last n) p)
  : ∀ (s : Fin n),
  (p s.succ).1 ≤ ↑(p s.castSucc).1 + 1 := by
        intro i
        by_cases h₂ :  p i.castSucc = Fin.last n
        · rw [h₂]
          have := (p i.succ).2
          aesop
        · rw [h.2.2 i]
          apply le_trans <| Fin.add_def _ _ ▸ Perm_δ_bound w (v i) h₂
          have : (p i.castSucc).1 < n := by
              contrapose h₂
              simp_all only [not_lt]
              exact Fin.eq_of_val_eq <| le_antisymm (Fin.is_le (p i.castSucc)) h₂
          simp
          rw [mod_eq_of_lt <| Nat.add_lt_add_right this 1]

/-- `Perm_δ w` accepts a word of length `|w|` only along the path `id` that advances one step at a time. -/
theorem accepts_perm_path  {A : Type*} {n : ℕ} (v w : Fin n → A) (p : Fin (n+1) → Fin (n+1))
    (h : accepts_word_path (Permδ w) v 0 (Fin.last n) p) : p = id := by
    ext i
    by_cases hi : i = Fin.last n
    · simp
      rw [hi]
      rw [h.2.1]
    · have := @exact_racecar n p h.1 h.2.1 (by
        apply perm_path_bound <;> tauto
      ) (i.castPred hi)
      simp at this
      rw [this]
      simp

/-- If `Perm_δ w` accepts a word of length `|w|` then that word must be `w`. -/
theorem accepts_perm_word  {A : Type*} {n : ℕ} (v w : Fin n → A) (p : Fin (n+1) → Fin (n+1))
    (h : accepts_word_path (Permδ w) v 0 (Fin.last n) p) : w = v := by
  rw [accepts_perm_path v w p h] at h
  by_cases hn : n = 0
  · subst hn
    ext i
    have := i.2
    omega
  obtain ⟨m,hm⟩ := exists_eq_succ_of_ne_zero hn
  subst hm
  have case0 : w 0 = v 0 := by
    have := h.2.2 0
    unfold Permδ Perm_δ at this
    rw [dif_neg hn] at this
    simp at this
    symm
    by_contra H
    rw [if_neg H] at this
    conv at this =>
        right
        change 0
    simp at this
  have := @Fin.induction m (fun i => w i = v i) case0 (by
      intro i hi
      have := h.2.2 i.succ
      unfold Permδ Perm_δ at this
      simp at this
      have his : i.succ.castSucc = ⟨i.1.succ, by omega⟩ := by simp;rfl
      sorry
      -- simp_rw [his] at this
      -- symm
      -- by_contra H
      -- have hic : w i.succ = w ⟨i.1 + 1, by omega⟩ := by rfl
      -- simp_rw [← hic] at this
      -- simp_all
      -- have := @least_not_in_range_small m.succ i.1 (Perm_δ w (v i.succ)) ⟨i.1+1, by omega⟩ i.1 (by simp)
      --   (by omega) (by
      --       apply this.symm.trans
      --       rw [Fin.add_def]
      --       have : (i.1 + 1 + 1) % (m + 1 + 1) = i.1 + 1 + 1 := mod_eq_of_lt <| by omega
      --       exact Fin.eq_mk_iff_val_eq.mpr this.symm
      --   )
      -- omega
  )
  ext i
  exact this i

/-- If q+2 is the least not in the range then anything less
 is in the range. -/
theorem is_onto {n q r : ℕ} (h₉ : q + 1 < n) (hr : r < n)
    (h₁ := Order.lt_add_one_iff.mpr h₉)
    {p : Fin (n+1) → Fin (n+1)}
    (h : ⟨q + 2, h₁⟩ =
      least_not_in_range hr
        fun i ↦ p ⟨i.1, by omega⟩) (x : Fin (q+2)):
    ∃ y : Fin (r+1), p ⟨y.1, by omega⟩ = ⟨x.1, by omega⟩ := by
  by_contra H
  push Not at H
  have : (⟨q+2, h₁⟩ : Fin (n+1)) ≤ ⟨x.1, by omega⟩ := by
    rw [h]
    apply min'_le
    simp
    tauto
  have : q + 2 ≤ x.1 := this
  omega

theorem bound_of_least_not_in_range {n q r : ℕ} (h₉ : q + 1 < n) (hr : r < n)
    (h₁ := Order.lt_add_one_iff.mpr h₉)
    {p : Fin (n+1) → Fin (n+1)}
    (h : ⟨q + 2, h₁⟩ = least_not_in_range hr fun i ↦ p ⟨i.1, by omega⟩):
    q + 2 ≤ r + 1 := by
  have hnq : q + 2 ≤ n + 1 := by omega
  have onto: ∀ x : Fin (q+2), ∃ y : Fin (r+1),
    p ⟨y.1, by omega⟩ = ⟨x.1, by omega⟩ := by apply is_onto <;> tauto
  sorry
  -- let f (k : Fin (q+2)) := (@Fin.find (r+1)
  --   (fun y : Fin (r+1) => p ⟨y.1, by omega⟩ = ⟨k.1, by omega⟩) _
  --   ).get (Fin.isSome_find_iff.mpr <| onto k)
  -- have : Function.Injective f := fun u v _ => by
  --   have hu := @Fin.find_spec (r+1) (fun y : Fin (r+1) =>
  --       p ⟨y.1, by omega⟩ = ⟨u.1, by omega⟩) _
  --     (Option.get _ (Fin.isSome_find_iff.mpr (onto u))) (by aesop)
  --   have hv := @Fin.find_spec (r+1) (fun y : Fin (r+1) =>
  --     p ⟨y.1, by omega⟩ = ⟨v.1, by omega⟩) _
  --     (Option.get _ (Fin.isSome_find_iff.mpr (onto u))) (by aesop)
  --   exact (@Fin.castLE_inj (n+1) (q+2) hnq u v).mp <| hu.symm.trans hv
  -- rw [← Fintype.card_fin (r + 1), ← Fintype.card_fin (q + 2)]
  -- exact Fintype.card_le_of_injective _ this


/-- Injectivity of `Perm_δ`, "forward" case. -/
theorem injCase₁ {A : Type*} {n : ℕ} (w : Fin n → A) {q : ℕ} (h₉ : q + 1 < n)
    {r : ℕ} (hr : r.succ < n + 1)
    (h : Perm_δ w (w ⟨q + 1, h₉⟩) ⟨q.succ, by omega⟩
       = Perm_δ w (w ⟨q + 1, h₉⟩) ⟨r.succ, hr⟩) : q = r := by
  have hnq : q + 2 ≤ n + 1 := by omega
  have h₀ : ∃ (h₁ : q + 1 < n), w ⟨q + 1, h₉⟩ = w ⟨q + 1, h₁⟩ := by use h₉
  have hq : q.succ < n + 1 := by
    obtain ⟨u,v⟩ := h₀
    omega
  unfold Perm_δ at h
  rw [dif_pos h₀] at h
  simp at h
  by_cases h₁ : ∃ (h₁ : r + 1 < n), w ⟨q + 1, h₉⟩ = w ⟨r + 1, h₁⟩
  · rw [dif_pos h₁] at h
    aesop
  · rw [dif_neg h₁] at h
    push Not at h₁
    by_contra H
    have hbig: q+2 ≤ r+1 := by apply bound_of_least_not_in_range <;> tauto
    have hl : q < r := by omega
    by_cases hrn : r + 1 < n
    · have h₁ := h₁ hrn
        -- @the bigger one the current bit is not a, but they are part of the same run of a's
      have := mem_of_eq_min h
      simp at this
      apply this ⟨q+1, by omega⟩
      unfold Perm_δ
      simp
      rw [dif_pos h₉]
    · simp_all
      have : r = n - 1 := by omega
      subst this
      unfold least_not_in_range at h
      -- q+2 can't be the least not in the range because it's in the range!
      have := mem_of_eq_min h
      simp at this
      apply this ⟨q+1, by omega⟩
      unfold Perm_δ
      simp
      simp_rw [dif_pos h₉]




/-- Injectivity of `Perm_δ`, zero case. -/
theorem injCase₀ {A : Type*} {n : ℕ} (w : Fin n → A) (a : A) {q : ℕ} (hq : q.succ < n + 1) :
    Perm_δ w a 0 ≠ Perm_δ w a ⟨q.succ, hq⟩ := by
    intro h
    by_cases hn : n = 0
    · subst hn
      have : q = 0 := by omega
      subst this
      simp at hq
    · have hn₀ : 0 < n := zero_lt_of_ne_zero hn
      have hn₁ : 1 < n + 1 := Nat.lt_add_of_pos_left hn₀
      conv at h =>
          right
          unfold Perm_δ
      by_cases h₀ :  ∃ (h₁ : q + 1 < n), a = w ⟨q + 1, h₁⟩
      · symm at h
        unfold Perm_δ at h
        rw [dif_neg hn] at h
        simp at h
        rw [dif_pos h₀] at h
        conv at h =>
          right
          change (if a = w ⟨0, hn₀⟩ then ⟨1, hn₁⟩ else 0)
        by_cases h₁ : a = w ⟨0, hn₀⟩
        · rw [if_pos h₁] at h
          simp at h
        · simp_all only [↓reduceIte]
          obtain ⟨w_1, h⟩ := h₀
          simp_all only
          have : q + 2 = 0 := Fin.mk.inj_iff.mp h
          simp at this

      · rw [dif_neg h₀] at h
        have := mem_of_eq_min h
        simp only [mem_filter, mem_univ, true_and] at this
        exact this 0 rfl

theorem injCase_helper {A : Type u_1} {n : ℕ} (w : Fin n → A) (a : A) {q : ℕ} (hq : q.succ < n + 1)
    {r : ℕ}
    (hr : r.succ < n + 1) (h : Perm_δ w a ⟨q + 1, hq⟩ = Perm_δ w a ⟨r + 1, hr⟩)
    (hl : q < r) : ∃ (h₁ : r + 1 < n), a = w ⟨r + 1, h₁⟩ := by
  by_contra h₁
  conv at h =>
      right
      unfold Perm_δ
  simp_rw [dif_neg h₁] at h
  unfold least_not_in_range at h
  have := mem_of_eq_min h
  simp at this
  apply this ⟨q + 1, by omega⟩
  rfl

/-- Injectivity of `Perm_δ`, "backward" case. -/
theorem injCase {A : Type*} {n : ℕ} (w : Fin n → A) (a : A) {q : ℕ} (hq : q.succ < n + 1) {r : ℕ}
    (hr : r.succ < n + 1) (h : Perm_δ w a ⟨q.succ, hq⟩ = Perm_δ w a ⟨r.succ, hr⟩)
    (h₀ : ¬∃ (h₁ : q + 1 < n), a = w ⟨q + 1, h₁⟩) (h₁ : ¬∃ (h₁ : r + 1 < n), a = w ⟨r + 1, h₁⟩)
    : q = r := by
    by_contra H
    cases Nat.lt_or_gt_of_ne H with
    | inl hl => exact h₁ <| injCase_helper _ _ _ _ h hl
    | inr hl => exact h₀ <| injCase_helper _ _ _ _ h.symm hl

example (P Q : Prop) (h : ∃ _ : P, Q) : Q := (exists_prop.mp h).2

example (P Q : Prop) (h : ∃ _ : P, Q) : P := (exists_prop.mp h).1

lemma exists_prop_fun {P : Prop} {Q : P → Prop} (h : ∃ h₀ : P, Q h₀) : P := by
  obtain ⟨w, h⟩ := h
  simp_all only



/-- Injectivity of `Perm_δ`, which is its key property. -/
theorem Perm_δ_injective {A : Type*} {n : ℕ} (w : Fin n → A) (a : A) :
  Function.Injective (Perm_δ w a) := by
  intro x y h
  match x with
  | 0 =>
    match y with
    | 0 => rfl
    | Fin.mk (succ q) hq =>
      exfalso; apply injCase₀ <;> tauto
  | Fin.mk (succ q) hq => match y with
    | 0 =>
      exfalso; apply injCase₀ <;> tauto
    | Fin.mk (succ r) hr =>
        congr
        by_cases h₀ : ∃ (h₁ : q + 1 < n), a = w ⟨q + 1, h₁⟩
        · exact injCase₁ w (exists_prop_fun h₀) hr (by
            obtain ⟨u,v⟩ := h₀
            exact v ▸ h)
        · by_cases h₁ : ∃ (h₁ : r + 1 < n), a = w ⟨r + 1, h₁⟩
          · exact (injCase₁ w (exists_prop_fun h₁) hq (by
              obtain ⟨u,v⟩ := h₁
              exact (v ▸ h).symm)).symm
          · by_cases h₃ : q + 1 < n <;>
              (by_cases h₂ : r + 1 < n <;> (apply injCase <;> tauto))

/-- The permutation-automatic complexity of `w` admits a witness of size `q`. -/
def A_perm_witness_size {A : Type*} {n : ℕ} (w : Fin n → A) (q : ℕ): Prop :=
  ∃ Q : Type, ∃ _ : Fintype Q, card Q = q ∧
    ∃ δ : A → Q → Q,
    ∃ init final p,
    (∀ a, Function.Injective (δ a)) ∧
    let Δ : A → Q → Set (Q) := fun a q => {δ a q}
    accepts_word_path Δ w init final p
    ∧ ∀ v : Fin n → A, ∀ p' : Fin (n+1) → Q,
      accepts_word_path Δ v init final p' → p = p' ∧ w = v

/-- The permutation-automatic complexity of a family `𝓕` admits a witness of size `q`. -/
def A_perm_witness_size_family {A : Type*} {n : ℕ} (𝓕 : Set (Fin n → A)) (q : ℕ): Prop :=
  ∃ Q : Type, ∃ _ : Fintype Q, card Q = q ∧
    ∃ δ : A → Q → Q,
    ∃ init final p,
    (∀ a, Function.Injective (δ a)) ∧
    let Δ : A → Q → Set (Q) := fun a q => {δ a q}
    (∀ w ∈ 𝓕, accepts_word_path Δ w init final p)
    ∧ ∀ v : Fin n → A, ∀ p' : Fin (n+1) → Q,
      accepts_word_path Δ v init final p' → v ∈ 𝓕


/-- The permutation-automatic complexity of `w` is upper bounded by `|w|+1` [Kjos-Hanssen 2017]. -/
theorem kjos_upper_bound  {A : Type*} {n : ℕ} (w : Fin n → A) :
    A_perm_witness_size w (n+1) := by
  use Fin (n+1)
  use Fin.fintype (n + 1)
  constructor
  · exact Fintype.card_fin (n + 1)
  · use Perm_δ w, 0, Fin.last n, id
    constructor
    · exact Perm_δ_injective w
    · constructor
      · apply accepts_perm
      · intro v p' h
        have := @accepts_perm_path
        have hp' : p' = id := by
          apply this
          exact h
        constructor
        · symm; tauto
        · apply @accepts_perm_word A n v w p'
          tauto

/-- The extended transition function δ* plays well with concatenation. -/
lemma ast_take  {A : Type*} [Fintype A] {n : ℕ} (w : Fin n → A)
    (δ : A → Q → Q) : ∀ (a : A),
ast δ (Fin.snoc w a) init = δ a (ast δ w init) := by
    intro a
    cases n with
    | zero => simp; rfl
    | succ n =>
        unfold ast;congr
        · apply Fin.snoc_last
        · apply Fin.init_snoc


/-- A value of the extended transition function δ* is implied by the existence of a path. -/
lemma star_if_path  {A : Type*} [Fintype A]
    (δ : A → Q → Q) : ∀ {n : ℕ} (w : Fin n → A) (c d : Q),
    (∃ p, accepts_word_path (fun a q ↦ {δ a q}) w c d p) →
    ast δ w c = d := by
    intro n
    induction n with
    | zero => exact fun w c d ⟨p,hp⟩ => hp.1.symm.trans hp.2.1
    | succ n ih =>
        intro w c d ⟨p,hp⟩
        have := ih (Fin.init w) c (p (Fin.last n).castSucc) (by
            use Fin.init p
            constructor
            · rw [← hp.1]
              exact rfl
            · constructor
              · rfl
              · intro i
                simp
                have := hp.2.2 i.castSucc
                simp at this
                have : Fin.init p i.succ =  p i.castSucc.succ := by rfl
                have : δ (Fin.init w i) (Fin.init p i.castSucc) =
                    δ (w i.castSucc) (p i.castSucc.castSucc) := by rfl
                tauto
        )
        unfold ast
        rw [this]
        have := hp.2.2 (Fin.last n)
        simp at this
        rw [← this]
        unfold accepts_word_path at hp
        tauto

/-- A value of the extended transition function δ* is equivalent to the existence of a path. -/
lemma path_iff_star {A : Type*} [Fintype A] (δ : A → Q → Q) {n : ℕ} (w : Fin n → A) :
    (∃ p, accepts_word_path (fun a q ↦ {δ a q}) w init final p) ↔
    ast δ w init = final := by
    constructor
    · apply star_if_path
    · intro h
      use (fun k => ast δ (Fin.take k (Fin.is_le k) w) init)
      constructor
      · rfl
      · constructor
        · simp
          exact h
        · intro i
          simp
          have := @Fin.take_succ_eq_snoc n (fun _ => A) i.1 i.2 w
          rw [this]
          simp
          apply ast_take


/-- The permutation-automatic complexity of `w` is lower by `|w|+1` [Quas 2020]. -/
theorem quas_lower_bound {A : Type*} [Fintype A] (hA : Fintype.card A ≥ 2) {m n : ℕ} (w : Fin n → A)
    (hmn : m ≤ n):
    ¬ A_perm_witness_size w m := by
  unfold A_perm_witness_size
  push Not
  intro Q _ hQ δ init final p ha hΔ

  have hquas := @quas' Q A _ _ δ ha n init final (by
    have h₀ := @path_iff_star Q init final A _ δ n
    have h₁ : (fun w : Fin n → A ↦ ast δ w init = final)
        = (fun w => (∃ p, accepts_word_path (fun a q ↦ {δ a q}) w init final p)) := by
            ext
            rw [h₀]
    simp_rw [h₁]
    have : #{w}=1 := rfl
    simp_rw [← this]
    congr
    ext v
    constructor
    · intro h
      simp at h
      obtain ⟨p', hp'⟩ := h
      have := (hΔ.2 v p' hp').2
      simp
      rw [this]
    · intro h
      simp at h
      symm at h
      subst h
      simp
      use p
      exact hΔ.1
  ) hA
  omega

/-- The permutation-automatic complexity of `w` is well-defined. -/
theorem A_perm_bounded {A : Type*} {n : ℕ} (w : Fin n → A) :
  ∃ q, A_perm_witness_size w q := by
  use n+1
  exact kjos_upper_bound w

/-- The permutation-automatic complexity of `w`. -/
noncomputable def A_perm {A : Type*} : {n : ℕ} → (Fin n → A) → ℕ :=
  fun w => Nat.find (A_perm_bounded w)

/-- The permutation-automatic complexity of `w` is exactly `|w|+1`. -/
theorem A_perm_characterization {A : Type*} [Fintype A] (hA : Fintype.card A ≥ 2)
    {n : ℕ} (w : Fin n → A) : A_perm w = n+1 := by
  have : A_perm w ≤ n+1 := find_le <| kjos_upper_bound w
  have : ¬ A_perm w ≤ n := by
    intro hc
    simp [A_perm] at hc
    obtain ⟨m,hm⟩ := hc
    exact quas_lower_bound hA w hm.1 hm.2
  omega

example : A_perm ![(0 : Fin 2),1,1] = 4 := by
    apply A_perm_characterization
    simp
