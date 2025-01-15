import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.Algebra.Order.Floor
import Mathlib.Data.Nat.Log
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fin.Tuple.Take
import Acmoi.HydeTheorem
set_option maxHeartbeats 20000000
/-!

  # Kjos-Hanssen's part of the K-H Quas theorem


-/

open Finset Fintype Nat Classical



def leastnotinrange' {n q : ℕ} (h : q < n) (f : Fin (q) → Fin (n)) : Fin (n) := by
    exact min' (filter (fun k => ∀ l : Fin (q), f ⟨l.1,by omega⟩ ≠ k) univ) (by
    by_contra h₂
    simp at h₂
    have : ∀ k : Fin (n), k ∉  filter (fun k ↦ ∀ (l : Fin (q)), ¬ f ⟨l.1, by omega⟩ = k) univ := by
        intro k
        rw [h₂]
        simp
    simp at this
    have : Function.Surjective f := this
    have := Fintype.card_le_of_surjective f this
    simp at this
    omega
    )


def leastnotinrange {n q : ℕ} (h : q < n) (f : Fin (q+1) → Fin (n+1)) : Fin (n+1) := by
    exact min' (filter (fun k => ∀ l : Fin (q+1), f ⟨l.1,by omega⟩ ≠ k) univ) (by
    by_contra h₂
    simp at h₂
    have : ∀ k : Fin (n+1), k ∉  filter (fun k ↦ ∀ (l : Fin (q + 1)), ¬ f ⟨l.1, by omega⟩ = k) univ := by
        intro k
        rw [h₂]
        simp
    simp at this
    have : Function.Surjective f := this
    have := Fintype.card_le_of_surjective f this
    simp at this
    omega
    )

noncomputable def Perm_δ {A : Type} {n : ℕ} (w : Fin n → A) (a : A) (q : Fin (n+1)) :  (Fin (n+1)) := match q with
| 0 => by
  by_cases hn : n = 0
  · exact ⟨0, by omega⟩
  · by_cases h₀ : a = w ⟨0, by omega⟩
    · exact ⟨1, by omega⟩
    · exact ⟨0, by omega⟩
| Fin.mk (succ q) hq => by
    by_cases h₀ : ∃ (h₁ : q+1 < n), a = w ⟨q+1, h₁⟩
    · exact ⟨q+2, by
            obtain ⟨h₁,hh₁⟩ := h₀
            omega
        ⟩
    · have hqn : q < n := by omega
      exact leastnotinrange hqn (fun i => Perm_δ w a ⟨i.1, by omega⟩)

-- example {n : ℕ} (a b : Fin n) : (a + b).1 = a.1 + b.1 := by refine Fin.eq_mk_iff_val_eq.mp ?a✝

theorem memofeqmin {α : Type} [LinearOrder α] {s : Finset α} (H : s.Nonempty) {a : α} (h : a = min' s H) : a ∈ s := by
  have := @min'_mem α _ s H
  rw [← h] at this
  tauto

theorem hbig {n : ℕ} {q : ℕ} {δa : Fin (n+1) → Fin (n+1)}
  {l : Fin (n + 1)} {m : ℕ} (hm : ↑l = m + 1)
  (hq₂ : q + 2 < n + 1)
  (hc : (leastnotinrange (by omega) fun i : Fin (m + 1) ↦ δa ⟨i.1, by omega⟩) = ⟨q + 1, by omega⟩ + 1) :
  Fintype.card (Fin (q + 2)) ≤ Fintype.card (Fin (m + 1)) := by
            have : ∀ x : Fin (q+2), ∃ y : Fin (m+1),
                δa ⟨y.1, by omega⟩ = ⟨x.1, by omega⟩ := by
                intro x
                by_contra H
                push_neg at H
                unfold leastnotinrange at hc
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
                have : q + 2 ≤ x.1 := by exact this
                have : x.1 < q + 2 := x.2
                omega
            let f := fun k : Fin (q+2) => (@Fin.find (m+1)
                (fun y : Fin (m+1) =>
                    δa ⟨y.1, by omega⟩ = ⟨k.1, by omega⟩) _
                ).get (by
                apply Fin.isSome_find_iff.mpr
                exact this k)
            have := @Fintype.card_le_of_injective (Fin (q+2)) (Fin (m+1)) _ _
                f (by
                intro u v huv
                unfold f at huv

                have hu := @Fin.find_spec (m+1)
                    (fun y : Fin (m+1) =>
                    δa ⟨y.1, by omega⟩ = ⟨u.1, by omega⟩) _
                    (@Option.get (Fin (m + 1))
                    (Fin.find fun y ↦ δa ⟨↑y, by omega⟩ = ⟨↑u, by omega⟩) (by
                        exact Fin.isSome_find_iff.mpr (this u)
                    ) : Fin (m + 1)) (by aesop)
                have hv := @Fin.find_spec (m+1)
                    (fun y : Fin (m+1) =>
                    δa ⟨y.1, by omega⟩ = ⟨v.1, by omega⟩) _
                    (@Option.get (Fin (m + 1))
                    (Fin.find fun y ↦ δa ⟨↑y, by omega⟩ = ⟨↑u, by omega⟩) (by
                        exact Fin.isSome_find_iff.mpr (this u)
                    ) : Fin (m + 1)) (by aesop)
                simp at hu hv
                suffices (⟨u.1, by omega⟩ : Fin (n+1)) = ⟨v.1, by omega⟩ by aesop
                apply hu.symm.trans
                tauto)
            exact this

theorem Perm_δ_bound {A : Type} {n : ℕ} (w : Fin n → A) (a : A) (q : Fin (n+1))
    (hqn : q ≠ Fin.last n):
    (Perm_δ w a q) ≤ q + 1 := match q with
  | 0 => by
    by_cases hn : n = 0
    · subst hn;unfold Perm_δ;simp
    · by_cases h₀ : a = w ⟨0, by omega⟩
      · subst h₀;unfold Perm_δ;simp;rw [dif_neg hn]
        conv =>
            left
            change ⟨1,by omega⟩
        apply le_of_eq
        apply Fin.eq_mk_iff_val_eq.mpr
        symm
        refine one_mod_eq_one.mpr ?pos.hab.a
        omega
      · unfold Perm_δ
        rw [dif_neg hn]
        simp
        rw [if_neg h₀]
        conv =>
            left
            change 0
        exact Fin.zero_le 1
  | Fin.mk (succ q) hq => by
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
      unfold leastnotinrange
      apply min'_le
      simp
      intro l
      unfold Perm_δ
      by_cases hl : l = 0
      · subst hl
        simp
        by_cases hn : n = 0
        · omega
        · rw [dif_neg hn]
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
            apply congrArg (fun x => x.1) at hc
            simp at hc
            by_cases h : q + 1 + 1 < n + 1
            · have : (q + 1 + 1) % (n + 1) = q + 1 + 1 := by exact mod_eq_of_lt h
              rw [this] at hc
              omega
            · have : q = n - 1 := by omega
              subst this
              apply hqn
              have : (n-1).succ = n := by omega
              simp_rw [this]
              rfl
      · have hn : ¬ n = 0 := by omega
        rw [dif_neg hn]
        have : l.1 ≠ 0 := by
            intro hc
            apply hl
            exact Eq.symm (Fin.eq_of_val_eq (id (Eq.symm hc)))
        have : ∃ m, l.1 = m + 1 := by exact exists_eq_succ_of_ne_zero this
        obtain ⟨m,hm⟩ := this
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
                    simp_all only [ne_eq]
                    suffices q + 1 ≠ n by omega
                    contrapose hqn
                    simp_all
                    exact rfl
          rw [dif_neg h₁]
          intro hc
          -- if q+2 is the smallest not in range of a functin from m+1
          -- then m+1 ≥ q+2 AS BEFORE so q+1 ≤ m so...
          have hbig: Fintype.card (Fin (q+2)) ≤ Fintype.card (Fin (m+1)) := by
            apply hbig; tauto; exact ⟨l.1, by omega⟩; exact hm; exact hq₂;
          have hf₀: Fintype.card (Fin (m+1)) = m+1 := Fintype.card_fin (m + 1)
          have hf₁: Fintype.card (Fin (q+2)) = q+2 := Fintype.card_fin (q + 2)
          have : q + 2 ≤ m + 1 := by
                rw [← hf₀, ← hf₁]
                omega
          omega


noncomputable def Permδ {A : Type} {n : ℕ} (w : Fin n → A) (a : A) (q : Fin (n+1)) :  Set (Fin (n+1)) :=
    {Perm_δ w a q}


theorem accepts_perm  {A : Type} {n : ℕ} (w : Fin n → A) :
    accepts_word_path (Permδ w) w 0 (Fin.last n) id := by
  constructor
  · rfl
  · constructor
    · rfl
    · intro i
      unfold Permδ
      simp
      unfold Perm_δ
      simp
      by_cases hn : n = 0
      · subst hn
        have := i.2
        simp at this
      · simp_rw [dif_neg hn]
        by_cases h₀ : w i = w ⟨0, by omega⟩
        · rw [if_pos h₀]
          by_cases h₁ : i = ⟨0, by omega⟩
          · subst h₁
            simp
            rfl
          · have : ∃ m, i.1 = m + 1 := by
                apply exists_eq_succ_of_ne_zero
                contrapose h₁
                simp_all
                exact Fin.eq_mk_iff_val_eq.mpr h₁
            obtain ⟨m,hm⟩ := this
            have : i.castSucc = ⟨m+1, by omega⟩ := by aesop
            simp_rw [this]
            by_cases h : ∃ (h₁ : m + 1 < n), w i = w ⟨m + 1, h₁⟩
            · simp_rw [dif_pos h]
              aesop
            · simp_rw [dif_neg h]
              unfold leastnotinrange
              simp
              push_neg at h
              by_cases h₂ : m + 1 < n
              · exfalso
                apply h h₂
                congr
                exact Fin.eq_mk_iff_val_eq.mpr hm
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
          have : ∃ m, i.1 = m + 1 := by
                apply exists_eq_succ_of_ne_zero
                contrapose this
                simp_all
          obtain ⟨m,hm⟩ := this
          have : i.castSucc = ⟨m+1, by omega⟩ := by aesop
          simp_rw [this]
          by_cases h₂ : ∃ (h₁ : m + 1 < n), w i = w ⟨m + 1, h₁⟩
          · rw [dif_pos h₂]
            apply Fin.eq_mk_iff_val_eq.mpr
            simp;tauto
          · rw [dif_neg h₂]
            push_neg at h₂
            by_cases h₃ : m + 1 < n
            · have := h₂ h₃
              exfalso
              apply this
              congr
              exact Fin.eq_mk_iff_val_eq.mpr hm
            · have := i.2
              omega

/-- instead of all, this
-- how about just use `Perm_δ_bound` and the fact that you have
-- to get to Fin.last n in n steps.  -/
theorem perm_path_bound {A : Type} {n : ℕ} (v w : Fin n → A) (p : Fin (n + 1) → Fin (n + 1))
  (h : accepts_word_path (Permδ w) v 0 (Fin.last n) p)
  : ∀ (s : Fin n),
  (p s.succ).1 ≤ ↑(p s.castSucc).1 + 1 := by
        intro i
        by_cases h₂ :  p i.castSucc = Fin.last n
        · rw [h₂]
          have := (p i.succ).2
          aesop
        have h₁ := h.2.2 i
        unfold Permδ at h₁
        simp at h₁
        rw [h₁]
        have h₀ := @Perm_δ_bound A n w (v i) (p i.castSucc) h₂
        rw [Fin.add_def] at h₀
        have :  (Perm_δ w (v i) (p i.castSucc)).1
            ≤
            (⟨(↑(p i.castSucc) + (1:Fin (n+1))) % (n + 1), by
            apply mod_lt (↑(p i.castSucc) +  (1:Fin (n+1)))
            omega
            ⟩ : Fin (n+1)).1
            := h₀
        apply le_trans this
        simp
        have : (p i.castSucc).1 < n := by
            contrapose h₂
            simp_all
            have : (p i.castSucc).1 = n := by omega
            exact Fin.eq_of_val_eq this
        have : (p i.castSucc).1 + 1 < n + 1 := by omega
        have : ((p i.castSucc).1 + 1) % (n + 1) = (p i.castSucc).1 + 1 := mod_eq_of_lt this
        rw [this]

theorem accepts_perm_path  {A : Type} {n : ℕ} (v w : Fin n → A) (p : Fin (n+1) → Fin (n+1))
    (h : accepts_word_path (Permδ w) v 0 (Fin.last n) p) : p = id := by
    ext i
    by_cases hi : i = Fin.last n
    · simp
      rw [hi]
      rw [h.2.1]
    · have := @id_of_slow' n p h.1 h.2.1 (by
        apply perm_path_bound <;> tauto
      ) (i.castPred hi)
      simp at this
      rw [this]
      simp

theorem accepts_perm_word  {A : Type} {n : ℕ} (v w : Fin n → A) (p : Fin (n+1) → Fin (n+1))
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
      simp_rw [his] at this
      symm
      by_contra H
      have hic : w i.succ = w ⟨i.1 + 1, by omega⟩ := by rfl
      simp_rw [← hic] at this
      simp_all
      have := @hbig m.succ i.1 (Perm_δ w (v i.succ)) ⟨i.1+1, by omega⟩ i.1 (by simp)
        (by omega) (by
            apply this.symm.trans
            rw [Fin.add_def]
            have : i.1 + 1 + 1 < m + 1 + 1 := by omega
            have : (i.1 + 1 + 1) % (m + 1 + 1) = i.1 + 1 + 1 := mod_eq_of_lt this
            exact Fin.eq_mk_iff_val_eq.mpr this.symm
        )
      have hf₀: Fintype.card (Fin (i.1+1)) = i.1+1 := Fintype.card_fin (i.1 + 1)
      have hf₁: Fintype.card (Fin (i.1+2)) = i.1+2 := Fintype.card_fin (i.1 + 2)
      have : i.1 + 2 ≤ i.1 + 1 := by
        rw [← hf₀, ← hf₁]
        omega
      omega
  )
  ext i
  exact this i

theorem injCase₁ {A : Type} {n : ℕ} (w : Fin n → A) (a : A) (q : ℕ) (hq : q.succ < n + 1) (r : ℕ)
    (hr : r.succ < n + 1) (h : Perm_δ w a ⟨q.succ, hq⟩ = Perm_δ w a ⟨r.succ, hr⟩)
    (h₀ : ∃ (h₁ : q + 1 < n), a = w ⟨q + 1, h₁⟩) : q = r := by
          unfold Perm_δ at h
          rw [dif_pos h₀] at h
          simp at h
          by_cases h₁ : ∃ (h₁ : r + 1 < n), a = w ⟨r + 1, h₁⟩
          · rw [dif_pos h₁] at h
            aesop
          · rw [dif_neg h₁] at h
            push_neg at h₁
            by_contra H
            have hbig: Fintype.card (Fin (q+2)) ≤ Fintype.card (Fin (r+1)) := by
                have : ∀ x : Fin (q+2), ∃ y : Fin (r+1),
                    Perm_δ w a ⟨y.1, by omega⟩ = ⟨x.1, by omega⟩ := by
                    intro x
                    by_contra H
                    push_neg at H
                    unfold leastnotinrange at h
                    have : (⟨q+2, by
                        simp_all only [ne_eq]
                        obtain ⟨w_1, h⟩ := h₀
                        simp_all only
                        omega
                    ⟩ : Fin (n+1)) ≤ ⟨x.1, by omega⟩ := by
                        rw [h]
                        apply min'_le
                        simp
                        tauto
                    have : q + 2 ≤ x.1 := by exact this
                    have : x.1 < q + 2 := x.2
                    omega
                let f := fun k : Fin (q+2) => (@Fin.find (r+1)
                    (fun y : Fin (r+1) =>
                        Perm_δ w a ⟨y.1, by omega⟩ = ⟨k.1, by omega⟩) _
                    ).get (by
                    apply Fin.isSome_find_iff.mpr
                    exact this k)
                have := @Fintype.card_le_of_injective (Fin (q+2)) (Fin (r+1)) _ _
                    f (by
                    intro u v huv
                    unfold f at huv

                    have hu := @Fin.find_spec (r+1)
                        (fun y : Fin (r+1) =>
                        Perm_δ w a ⟨y.1, by omega⟩ = ⟨u.1, by omega⟩) _
                        (@Option.get (Fin (r + 1))
                        (Fin.find fun y ↦ Perm_δ w a ⟨↑y, by omega⟩ = ⟨↑u, by omega⟩) (by
                            exact Fin.isSome_find_iff.mpr (this u)
                        ) : Fin (r + 1)) (by aesop)
                    have hv := @Fin.find_spec (r+1)
                        (fun y : Fin (r+1) =>
                        Perm_δ w a ⟨y.1, by omega⟩ = ⟨v.1, by omega⟩) _
                        (@Option.get (Fin (r + 1))
                        (Fin.find fun y ↦ Perm_δ w a ⟨↑y, by omega⟩ = ⟨↑u, by omega⟩) (by
                            exact Fin.isSome_find_iff.mpr (this u)
                        ) : Fin (r + 1)) (by aesop)
                    simp at hu hv
                    suffices (⟨u.1, by omega⟩ : Fin (n+1)) = ⟨v.1, by omega⟩ by aesop
                    apply hu.symm.trans
                    tauto)
                exact this
            have hf₀: Fintype.card (Fin (r+1)) = r+1 := Fintype.card_fin (r + 1)
            have hf₁: Fintype.card (Fin (q+2)) = q+2 := Fintype.card_fin (q + 2)
            have : q + 2 ≤ r + 1 := by
                rw [← hf₀, ← hf₁]
                omega
            have hl : q < r := by
                omega
            by_cases hrn : r + 1 < n
            · have h₁ := h₁ hrn
                -- @the bigger one the current bit is not a, but they are part of the same run of a's
              have := memofeqmin _ h
              simp at this
              apply this ⟨q+1, by omega⟩
              unfold Perm_δ
              simp
              rw [dif_pos h₀]
            · simp_all
              have : r = n - 1 := by omega
              subst this
              unfold leastnotinrange at h
              -- q+2 can't be the least not in the range because it's in the range!
              have := memofeqmin _ h
              simp at this
              apply this ⟨q+1, by omega⟩
              unfold Perm_δ
              simp
              simp_rw [dif_pos h₀]


theorem injCase₀ {A : Type} {n : ℕ} (w : Fin n → A) (a : A) (q : ℕ) (hq : q.succ < n + 1)
    (h : Perm_δ w a 0 = Perm_δ w a ⟨q.succ, hq⟩) : False := by
    by_cases hn : n = 0
    · subst hn
      have : q = 0 := by omega
      subst this
      simp at hq

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
        change (if a = w ⟨0, by omega⟩ then ⟨1, by omega⟩ else 0)
      by_cases h₁ : a = w ⟨0, by omega⟩
      rw [if_pos h₁] at h
      simp at h
      simp_all only [↓reduceIte]
      obtain ⟨w_1, h⟩ := h₀
      simp_all only
      have : q + 2 = 0 := Fin.mk.inj_iff.mp h
      simp at this

    · rw [dif_neg h₀] at h
      simp at h
      unfold leastnotinrange at h
      have := memofeqmin _ h
      simp at this
      apply this 0
      rfl




theorem injCase {A : Type} {n : ℕ} (w : Fin n → A) (a : A) (q : ℕ) (hq : q.succ < n + 1) (r : ℕ)
    (hr : r.succ < n + 1) (h : Perm_δ w a ⟨q.succ, hq⟩ = Perm_δ w a ⟨r.succ, hr⟩)
    (h₀ : ¬∃ (h₁ : q + 1 < n), a = w ⟨q + 1, h₁⟩) (h₁ : ¬∃ (h₁ : r + 1 < n), a = w ⟨r + 1, h₁⟩)
    : q = r := by
    by_contra H
    simp at h
    have : q < r ∨ r < q := by omega
    cases this with
    | inl hl =>
        conv at h =>
            right
            unfold Perm_δ
        simp_rw [dif_neg h₁] at h
        unfold leastnotinrange at h
        have := memofeqmin _ h
        simp at this
        apply this ⟨q + 1, by omega⟩
        rfl
    | inr hl =>
        -- entirely symmetrical
        conv at h =>
            left
            unfold Perm_δ
        simp_rw [dif_neg h₀] at h
        unfold leastnotinrange at h
        have := memofeqmin _ h.symm
        simp at this
        apply this ⟨r + 1, by omega⟩
        rfl
    -- @both the current bit is not a, but they are part of the same run of a's

theorem Perm_δ_injective  {A : Type} {n : ℕ} (w : Fin n → A) (a : A) :
  Function.Injective (Perm_δ w a) := by
  intro x y h
  match x with
  | 0 =>
    match y with
    | 0 => rfl
    | Fin.mk (succ q) hq => exfalso; apply injCase₀ <;> tauto
  | Fin.mk (succ q) hq => match y with
    | 0 =>                  exfalso; apply injCase₀ <;> tauto
    | Fin.mk (succ r) hr =>
        suffices q = r by simp_rw [this]
        by_cases h₀ : ∃ (h₁ : q + 1 < n), a = w ⟨q + 1, h₁⟩
        · apply injCase₁ <;> tauto
        · by_cases h₁ : ∃ (h₁ : r + 1 < n), a = w ⟨r + 1, h₁⟩
          · exact (@injCase₁ A n w a r hr q hq h.symm h₁).symm
          · by_cases h₃ : q + 1 < n <;> (by_cases h₂ : r + 1 < n <;> (apply injCase <;> tauto))
