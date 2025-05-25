import Mathlib.NumberTheory.Padics.PadicNumbers
import Acmoi.HydePrelim
import Mathlib.Data.Set.Finite
/-!

  # Theorem 1.49 in ACMOI


-/

open Finset Fintype Nat Classical

def ringδ' {A : Type} {n : ℕ} (w : Fin n → A) : A → Fin (n+1) → Set (Fin (n+1)) := by
      intro a q
      by_cases H₀ : q.1 < n
      · by_cases H₁ : a = w ⟨q.1, H₀⟩
        · exact {⟨(q.1 + 1) % n, by
            by_cases H₂ : n > 0
            · exact Nat.lt_add_right 1 <| mod_lt (q.1 + 1) H₂
            · aesop
            ⟩} -- continue around the cycle
        · exact {Fin.last n} -- go to dead state
      · exact {Fin.last n} -- Fin.last n is a dead state


theorem deadRingδ₀ {A : Type} {m n : ℕ} (v : Fin m → A) (w : Fin n → A) (p : Fin (m+1) → (Fin (n+1)))
  {final : Fin (n+1)}
  (h : accepts_word_path (ringδ' w) v 0 final p)
  (t : Fin m)
  (ht : p t.castSucc = Fin.last n) :
  p t.succ = Fin.last n := by
    unfold accepts_word_path at h
    have := h.2.2 t
    unfold ringδ' at this
    simp at this
    simp_all

theorem deadRingδ₂ {A : Type} {m n : ℕ} (v : Fin m → A) (w : Fin n → A) (p : Fin (m+1) → (Fin (n+1)))
  {final : Fin (n+1)}
  (h : accepts_word_path (ringδ' w) v 0 final p)
  (t : Fin (m+1))
  (ht : p t = Fin.last n) (s : Fin (m+1)) (hs : t.1 ≤ s.1) :
    p s = Fin.last n := by
  have := @Fin.induction m (fun k => t.1 ≤ k.1 → p k = Fin.last n) (by
    simp;intro hh;rw [← ht];congr;symm;exact Fin.eq_of_val_eq hh
  ) (by
  simp
  intro i h₀ h₁
  by_cases H : t.1 ≤ i.1
  · have := h₀ (by omega)
    apply deadRingδ₀
    exact h
    exact this
  · have : t.1 = i.1 + 1 := by omega
    rw [← ht]
    congr
    symm at this
    exact Fin.eq_of_val_eq this
  )
  simp at this
  tauto


theorem deadRingδ₁ {A : Type} {m n : ℕ} (v : Fin m → A) (w : Fin n → A) (p : Fin (m+1) → (Fin (n+1)))
  {final : Fin (n+1)} {hfinal : final ≠ Fin.last n}
  (h : accepts_word_path (ringδ' w) v 0 final p)
  (t : Fin (m+1)) :
  p t ≠ Fin.last n := by
  intro hc
  have : p (Fin.last m) = Fin.last n := by
    apply deadRingδ₂
    exact h
    exact hc
    simp
    omega
  unfold accepts_word_path at h
  rw [h.2.1] at this
  tauto

lemma ringPath'helper {n : ℕ}
    (t : Fin (n + 1)) : t.1 % n < n + 1 := by
  by_cases H : n = 0
  · subst H
    simp
  · apply Nat.lt_add_right 1
    apply mod_lt ↑t
    omega

lemma ringPathhelper {m n : ℕ} (hn : n ≠ 0)
    (t : Fin (m + 1)) : t.1 % n < n + 1 := by
  by_cases H : m = 0
  · subst H
    simp
  · apply Nat.lt_add_right 1
    apply mod_lt ↑t
    omega

theorem liveRingδ₁  {A : Type} {m n : ℕ}
    (v : Fin m → A) (w : Fin n → A) (p : Fin (m+1) → (Fin (n+1)))
    {final : Fin (n+1)} {hfinal : final ≠ Fin.last n}
    (h : accepts_word_path (ringδ' w) v 0 final p)
    (t : Fin (m+1)) : p t = ⟨t.1 % n, by
      suffices t.1 % n < n by exact Nat.lt_add_right 1 this
      refine mod_lt ↑t ?a
      omega
    ⟩ := by
  have := @Fin.induction m (fun k  => p k = ⟨k.1 % n, by
      suffices k.1 % n < n by exact Nat.lt_add_right 1 this
      apply mod_lt k.1
      omega
    ⟩ ) (by
    simp;unfold accepts_word_path at h;tauto
  ) (by
    intro i h₀
    unfold accepts_word_path ringδ' at h
    have := h.2.2 i
    simp at this
    split_ifs at this
    · simp at this
      simp_rw [h₀] at this;rw [this];simp
    · simp at this
      have := @deadRingδ₁ A m n v w p _ (by tauto) (by tauto) i.succ
      tauto
    · simp at this
      have := @deadRingδ₁ A m n v w p _ (by tauto) (by tauto) i.succ
      tauto
  )
  apply this

-- keep this since it doesn't require n ≠ 0
theorem liveRingδ₁'  {A : Type} {n : ℕ}
  (w v : Fin n → A) (p : Fin (n+1) → (Fin (n+1)))
  {final : Fin (n+1)} {hfinal : final ≠ Fin.last n}
  (h : accepts_word_path (ringδ' w) v 0 final p)
  (t : Fin (n+1)) : t ≠ Fin.last n → p t = t := by
  by_cases hn : n = 0
  · subst hn
    intro h₀
    exfalso
    apply h₀
    have := t.2
    suffices t.1 = 0 by exact Fin.eq_of_val_eq this
    simp_all
  have := @Fin.induction n (fun k  => k ≠ Fin.last n → p k = k) (by
    simp;intro;unfold accepts_word_path at h;tauto
  ) (by
    intro i h₀ h₁
    have := h₀ (by
      have := i.2; have : i.1 ≠ n := Nat.ne_of_lt this;exact
      Ne.symm (Fin.ne_of_val_ne (id (Ne.symm this)));)
    have hdead := @deadRingδ₁ A n n v w p final (by tauto) (by tauto) i.succ
    unfold accepts_word_path at h
    have := h.2.2 ⟨i.1, by omega⟩
    unfold ringδ' at this
    simp at this
    split_ifs at this with g₀ g₁
    · simp_all
      suffices (i.1 + 1) % n = i.1 + 1 by exact Fin.eq_of_val_eq this
      apply mod_eq_of_lt
      have : ¬ i + 1 = n := by
        intro hc
        apply h₁
        exact Fin.eq_of_val_eq hc
      omega
    · simp_all
    · simp at this
      tauto
  )
  simp at this
  intro hl
  exact this t (by tauto)


/-- A simpler construction of ringPath, although the proof that
it makes sense is harder. -/
def ringPath' {n : ℕ} : Fin (n+1) → Fin (n+1) := fun t =>
    ⟨t.1 % n, ringPath'helper t
    ⟩


def ringPath {m n : ℕ} (hn : n ≠ 0) : Fin (m+1) → Fin (n+1) := fun t =>
    ⟨t.1 % n, @ringPathhelper m n hn t
    ⟩

theorem ringδ_unique_word {A : Type} {m n : ℕ} (hn : n ≠ 0) (hm : m ≠ 0)
    (v : Fin m → A) (w : Fin n → A)
    {final : Fin (n+1)} {hfinal : final ≠ Fin.last n}
    (h : accepts_word_path (ringδ' w) v 0 final (ringPath hn)) :
    ∀ i : Fin m, v i = w ⟨i.1 % n, mod_lt ↑i <| by omega⟩ := by
  intro t
  have ⟨b,hb⟩ : ∃ b, m = b+1 := by exact exists_eq_succ_of_ne_zero hm
  subst hb
  have := @Fin.induction b (fun k => v k = w ⟨k.1 % n, by
    apply mod_lt ↑k
    omega
  ⟩) (by
    simp
    unfold accepts_word_path ringδ' ringPath at h
    simp at h
    have := (h.2 0)
    simp at this
    split_ifs at this
    · tauto
    · simp at this
      have : 1 % n = n := Fin.mk.inj_iff.mp this
      exfalso
      revert this
      simp
      refine Nat.ne_of_lt ?neg.h
      exact mod_lt 1 (by tauto)
    · simp at this
      have : 1 % n = n := Fin.mk.inj_iff.mp this
      exfalso
      revert this
      simp
      apply Nat.ne_of_lt
      apply mod_lt 1
      exact zero_lt_of_ne_zero hn
    ) (by
      intro i hi
      have h₀ := h.2.2 ⟨i.1, by omega⟩
      unfold accepts_word_path ringδ' ringPath at h₀
      simp at h₀
      split_ifs at h₀ with g₀ g₁
      · have h₁ := h.2.2 ⟨i.1 + 1, by omega⟩
        unfold accepts_word_path ringδ' ringPath at h₁
        simp at h₁
        split_ifs at h₁ with g₂ g₃
        · simp at h₁
          exact g₃
        · simp at h₁
          have : (i.1 + 1 + 1) % n = n := Fin.mk.inj_iff.mp h₁
          have : (i.1 + 1 + 1) % n < n := mod_lt (↑i + 1 + 1) <| zero_lt_of_ne_zero hn
          omega
        · simp at h₁
          have : (i.1 + 1 + 1) % n = n := Fin.mk.inj_iff.mp h₁
          have : (i.1 + 1 + 1) % n < n := mod_lt (↑i + 1 + 1) <| zero_lt_of_ne_zero hn
          omega
      · simp at h₀
        have : (i.1 + 1) % n = n := Fin.mk.inj_iff.mp h₀
        have : (i.1 + 1) % n < n := mod_lt (↑i + 1) <| zero_lt_of_ne_zero hn
        omega
      · simp at h₀
        have : (i.1 + 1) % n = n := Fin.mk.inj_iff.mp h₀
        have : (i.1 + 1) % n < n := mod_lt (↑i + 1) <| zero_lt_of_ne_zero hn
        omega
    )
  apply this


theorem ringδ_unique_word' {A : Type} {n : ℕ}
    (w v : Fin n → A)
    {final : Fin (n+1)} {hfinal : final ≠ Fin.last n}
    (h : accepts_word_path (ringδ' w) v 0 final ringPath') : w = v := by
  by_cases hn : n = 0
  · subst hn
    ext i
    exfalso
    have := i.2
    omega
  unfold ringPath' at h
  have hdead := @deadRingδ₁ A n n v w ringPath' final hfinal h
  have ⟨m,hm⟩ : ∃ m, n = m+1 := by exact exists_eq_succ_of_ne_zero hn
  subst hm
  ext t
  have := @Fin.induction m (fun k => w k = v k) (by
    simp
    unfold accepts_word_path ringδ' at h
    have := h.2.2 0
    simp at this
    symm
    by_contra H
    rw [if_neg H] at this
    have hlt : 1 % (m+1) < m+1 := mod_lt 1 <| by omega
    have : 1 % (m+1) = m+1 := Fin.mk.inj_iff.mp this
    omega) (by
      simp
      intro i hi
      unfold accepts_word_path ringδ' at h
      simp at h
      have h' := h.2 i.succ
      simp at h'
      split_ifs at h' with g₀ g₁
      · rw [g₁]
        congr
        apply Fin.eq_mk_iff_val_eq.mpr
        simp
        symm
        apply mod_eq_of_lt
        omega
      · simp at h'
        have hlt : (i.1 + 1 + 1) % (m+1) < m+1 := mod_lt _ <| by omega
        have : (i.1 + 1 + 1) % (m+1) = m+1 := Fin.mk.inj_iff.mp h'
        omega
      · simp at h'
        have hlt : (i.1 + 1 + 1) % (m+1) < m+1 := mod_lt _ <| by omega
        have : (i.1 + 1 + 1) % (m+1) = m+1 := Fin.mk.inj_iff.mp h'
        omega
    )
  apply this

/-- A power of a word has low complexity. -/
theorem A_bound₀'pow {A : Type} {n e : ℕ} (hn : n ≠ 0) (he : e ≠ 0)
    (w : Fin n → A) : A_at_most (Fin.repeat e w) (n+1) := by
  use Fin (n+1), (Fin.fintype (n + 1))
  constructor
  · exact Fintype.card_fin (n + 1)
  · use ringδ' w, 0, 0, (fun t => ⟨t.1 % n, by apply ringPathhelper hn⟩)
    constructor
    · intro a q
      unfold ringδ'
      split_ifs <;> rfl
    · constructor
      · constructor
        · rfl
        · constructor
          · simp
          · simp
            intro i
            unfold ringδ'
            split_ifs with g₀ g₁
            · simp
            · simp; exfalso; apply g₁
              by_cases h : i.1 < n
              · simp_all
                apply g₁
                congr
              · congr
            · exfalso;apply g₀;refine mod_lt ↑i ?neg.a;omega
      · intro v p' h
        have hr : p' = ringPath hn := by
          unfold ringPath
          ext i
          have := @liveRingδ₁ A (e*n) n v w p' _ (by
            intro hc
            apply hn
            exact Fin.last_eq_zero_iff.mp hc.symm
          ) h i
          rw [this]
        constructor
        · symm;tauto
        · have := @ringδ_unique_word A (e*n) n hn (mul_ne_zero he hn) v w 0 (by
            intro hc;apply hn;
            exact Fin.last_eq_zero_iff.mp (id (Eq.symm hc))
          )
            (by rw [← hr];tauto)
          ext i
          rw [this i]
          -- Copied from above:
          unfold Fin.repeat
          simp
          congr




/-- A square has low complexity. -/
theorem A_bound₀'square {A : Type} {n : ℕ} (hn : n ≠ 0)
    (w : Fin n → A) : A_at_most (Fin.append w w) (n+1) := by
  have : Fin.append w w =
    fun i =>  Fin.repeat 2 w ⟨i.1,by have := i.2;omega⟩ := by
      ext i
      simp
      unfold Fin.append Fin.addCases
      simp
      split_ifs with h
      · congr
        refine Fin.eq_of_val_eq ?pos.e_a.a
        simp
        exact Eq.symm (mod_eq_of_lt (by tauto))
      congr
      unfold Fin.subNat Fin.modNat
      simp
      have : i.1 - n = i.1 % n := by
        simp at h
        have ⟨k,hk⟩ : ∃ k, i.1 = k + n := by exact Nat.exists_eq_add_of_le' h
        rw [hk]
        simp
        apply Eq.symm (mod_eq_of_lt (by
          have := i.2
          omega))
      simp_rw [← this]
  rw [this]
  have := @A_bound₀'pow A n 2 hn (by simp) w
  revert this
  apply Iff.mp
  apply Eq.to_iff
  congr
  omega
  simp
  refine (Fin.heq_fun_iff ?self.a.h.e_3.h).mpr ?self.a.h.e_3.a
  omega
  intro i
  simp


theorem A_bound₀' {A : Type} {n : ℕ}
    (w : Fin n → A) : A_at_most w (n+1) := by
  use Fin (n+1), (Fin.fintype (n + 1))
  constructor
  · exact Fintype.card_fin (n + 1)
  · use ringδ' w, 0, 0, ringPath'
    constructor
    · intro a q
      unfold ringδ'
      split_ifs <;> rfl
    · constructor
      · unfold accepts_word_path
        constructor
        · rfl
        · constructor
          · simp [ringPath']
          · intro i
            unfold ringPath'
            unfold ringδ'
            split_ifs with g₀ g₁
            · simp
            · simp at g₁
              exfalso
              apply g₁
              congr
              apply Fin.eq_of_val_eq
              simp
              symm
              apply mod_eq_of_lt i.2
            · exfalso
              by_cases hn : n = 0
              · subst hn
                have := i.2
                omega
              · apply g₀
                simp
                apply mod_lt ↑i
                omega
      · intro v p' h
        constructor
        · by_cases hn : n = 0
          · subst hn
            ext i
            calc _ = 0 := by exact Fin.val_eq_zero (ringPath' i)
            _ = _ := by exact Eq.symm (Fin.val_eq_zero (p' i))
          unfold ringPath'
          ext i
          simp
          unfold accepts_word_path ringδ' at h
          by_cases H : i = Fin.last n
          · rw [H]
            rw [h.2.1]
            simp
          · have : ¬ i.1 = n := by
              intro hc
              apply H <| Fin.eq_of_val_eq hc
            have h₀ := h.2.2 ⟨i.1, by
              omega
            ⟩
            simp at h₀
            split_ifs at h₀ with g₀ g₁
            · simp at h₀
              rw [@liveRingδ₁' A n w v p' 0 (by
                intro hc;apply hn;exact Fin.last_eq_zero_iff.mp (id (Eq.symm hc))
              ) (by tauto) i H]
              apply mod_eq_of_lt
              omega
            · simp at h₀
              have := @deadRingδ₁ A n n v w p' 0 (by
                intro hc
                apply hn
                exact Fin.last_eq_zero_iff.mp (id (Eq.symm hc))
              ) (by tauto) ⟨i.1+1,by omega⟩
              tauto
            · simp at h₀
              have := @deadRingδ₁ A n n v w p' 0 (by
                intro hc
                apply hn
                exact Fin.last_eq_zero_iff.mp (id (Eq.symm hc))
              ) (by tauto) ⟨i.1+1,by omega⟩
              tauto
        · by_cases hn : n = 0
          · subst hn
            ext i
            have := i.2
            omega
          exact @ringδ_unique_word' A n w v 0 (by
            intro hc;apply hn;exact
            Fin.last_eq_zero_iff.mp (id (Eq.symm hc))) (by
            have hp : ringPath' = p' := by
              unfold ringPath'
              ext i
              by_cases H : i = Fin.last n
              · rw [H, h.2.1]
                simp
              · rw [@liveRingδ₁' A n w v p' 0 (by
                  intro hc
                  apply H
                  have : n = 0 := Fin.last_eq_zero_iff.mp hc.symm
                  subst this
                  have := i.2

                  have : i.1 = 0 := by omega
                  exact Eq.symm (Fin.eq_of_val_eq (id (Eq.symm this)))
                ) (by tauto) i H]
                have : ¬ i.1 = n := by
                  intro hc
                  apply H
                  exact Fin.eq_of_val_eq hc
                simp
                refine mod_eq_of_lt ?neg.h
                omega

            rw [hp]
            tauto
          )





theorem A_bounded {A : Type} {n : ℕ} (w : Fin n → A) :
  ∃ q, A_at_most w q := by
  use n+1
  exact A_bound₀' w

theorem A_minus_bounded {A : Type} {n : ℕ} (w : Fin n → A) :
  ∃ q, A_minus_at_most w q := by
  use n+1
  apply A_minus_le_A
  exact A_bound₀' w





noncomputable def A {A : Type} : {n : ℕ} → (Fin n → A) → ℕ :=
  fun w => Nat.find (A_bounded w)

noncomputable def A_minus {A : Type} : {n : ℕ} → (Fin n → A) → ℕ :=
  fun w => Nat.find (A_minus_bounded w)

open Fin

def extend {A : Type} {n : ℕ} (hn : n ≠ 0) (w : Fin n → A) (m : ℕ) : Fin m → A :=
  fun i => w ⟨i.1 % n, by refine mod_lt ↑i ?a;omega;⟩

/-- Theorem 1.49 of ACMOI, in so many words.
Also essentially Lemma 9 in "Maximal automatic complexity and context-free
languages" although that was given for A_N.
-/
theorem A_bound₀'extend {A : Type} {n : ℕ} (hn : n ≠ 0) (w : Fin n → A)
    (m : ℕ)  (hm : m ≠ 0) : A_at_most (extend hn w m) (n+1) := by
  use Fin (n+1), (Fin.fintype (n + 1))
  let final : Fin (n+1) := ⟨m % n, by
      suffices m % n < n by omega
      apply mod_lt m
      omega
    ⟩
  constructor
  · exact Fintype.card_fin (n + 1)
  · use ringδ' w, 0, final, (fun t : Fin (m+1) => ⟨t.1 % n, by apply ringPathhelper hn⟩)
    constructor
    · intro a q
      unfold ringδ'
      split_ifs <;> rfl
    · constructor
      · constructor
        · rfl
        · constructor
          · simp
          · intro i
            unfold extend
            simp
            unfold ringδ'
            split_ifs with g₀ g₁
            · simp
            · simp; exfalso; apply g₁
              by_cases h : i.1 < n
              · simp_all
              · congr
            · exfalso;apply g₀;refine mod_lt ↑i ?neg.a;omega
      · intro v p' h
        have hr : p' = ringPath hn := by
          unfold ringPath
          ext i
          have := @liveRingδ₁ A m n v w p' final (by
            unfold final
            intro hc
            have : m % n = n := mk.inj_iff.mp hc
            have : m % n < n := by apply mod_lt m; omega
            omega
          ) h i
          rw [this]
        constructor
        · symm;tauto
        · --sorry
          have := @ringδ_unique_word A m n hn
            hm v w final (by
            unfold final
            intro hc
            have : m % n = n := mk.inj_iff.mp hc
            have : m % n < n := by apply mod_lt m; omega
            omega
            )
            (by rw [← hr];tauto)
          ext i
          rw [this i]
          unfold extend
          simp

example : A ![0,0,1,0,0,1,0,0,1] ≤ 4 := by
  have : Fin.repeat 3 ![0, 0, 1] = ![0,0,1,0,0,1,0,0,1] := by
    ext i; fin_cases i <;> decide
  rw [← this]
  unfold A
  simp
  use 4
  simp
  exact @A_bound₀'pow ℕ 3 3 (by simp) (by simp) ![0,0,1]

example : A ![0,0,1,0,0,1,0] ≤ 4 := by
  have : @extend ℕ 3 (by simp) ![0,0,1] 7 = ![0,0,1,0,0,1,0] := by
    ext i; fin_cases i <;> decide
  rw [← this]
  unfold A
  simp
  use 4
  simp
  exact @A_bound₀'extend ℕ 3 (by simp) ![0,0,1] 7 (by simp)

-- #print axioms A_N_bound
