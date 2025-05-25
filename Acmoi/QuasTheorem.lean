import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.Algebra.Order.Floor
import Mathlib.Data.Nat.Log
import Mathlib.InformationTheory.Hamming
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fin.Tuple.Take

/-!

  # Quas' Theorem

  We prove the italicized statement that we "must prove" in Theorem 4.42
  from *Automatic complexity: a computable measure of irregularity*

-/

open Finset Fintype

/-- ast for "asterisk": ast δ is what we in mathematics articles would
 call δ^*, the iteration of the transition function δ over a word in.  -/
def ast {Q A : Type*} [Fintype A] {n : ℕ}
    (δ : A → Q → Q) (w : Fin n → A) (init : Q) : Q := match n with
| 0 => init
| Nat.succ k => δ (w (Fin.last k)) (ast δ (Fin.init w) init)

def astN {Q A : Type*} [Fintype A] {n : ℕ}
    (δ : A → Q → Set Q) (w : Fin n → A) (init : Q) : Set Q := match n with
| 0 => {init}
| Nat.succ k => ⋃ q ∈ (astN δ (Fin.init w) init), δ (w (Fin.last k)) q

/-- This is an incorrect definition of accepting path. -/
def accepts {Q A : Type*} [Fintype A] {n : ℕ}
    (δ : A → Q → Set Q) (w : Fin n → A) (init : Q) (final : Q) (path : Fin (n+1) → Q) : Prop := by
  exact path 0 = init ∧ path (Fin.last n) = final
   ∧ ∀ i : Fin (n+1), path i ∈ astN δ (Fin.take i (by omega) w) init

def accepts' {Q A : Type*} [Fintype A] {n : ℕ}
    (δ : A → Q → Set Q) (w : Fin n → A) (init : Q) (final : Q) (path : Fin (n+1) → Q) : Prop := by
  exact path 0 = init ∧ path (Fin.last n) = final
   ∧ ∀ i : Fin (n), path (⟨i.1+1,by omega⟩) ∈ δ (w i) (path ⟨i.1,by omega⟩)


-- Let us try it with the 2-state Kayleigh graph for 011:
def myδ : Fin 2 → Fin 2 → Set (Fin 2) := (
  ![  -- state 0          state 1
    ![({1} : Set (Fin 2)), ∅    ], -- δ₀
    ![∅,                  {0,1} ] -- δ₁
  ]
)

example : accepts myδ ![0,1,1] 0 0 ![0,1,1,0] := by
  simp [accepts, myδ]
  constructor
  rfl
  intro i
  fin_cases i
  unfold astN
  simp
  unfold astN
  simp
  unfold astN
  simp
  unfold astN
  simp
  unfold astN
  simp
  unfold astN
  simp
  have : Fin.init ![(0 : Fin 2), 1, 1] = ![0, 1] := by
    ext x
    fin_cases x <;> rfl
  rw [this]
  simp
  have : Fin.init ![(0 : Fin 2), 1] = ![(0 : Fin 2)] := by
    ext x
    fin_cases x ; rfl
  rw [this]
  simp
  right
  simp
  unfold astN
  simp
  unfold astN
  simp
  unfold astN
  simp
  unfold astN
  simp
  use 1 -- just guessing!
  constructor
  · use 1
    constructor
    · have : Fin.take (3 : Fin 4) (by omega) ![(0 : Fin 2), 1, 1] = ![0,1,1] := rfl
      rw [this]
      simp
      have : Fin.init ![(0 : Fin 2), 1, 1] = ![(0 : Fin 2),1] := by
        ext x; fin_cases x <;> rfl
      rw [this]
      simp
      have : Fin.init ![(0 : Fin 2), 1] = ![(0 : Fin 2)] := by
        ext x; fin_cases x ; rfl
      rw [this]
      simp
    · have : Fin.take (3 : Fin 4) (by omega) ![(0 : Fin 2), 1, 1] = ![0,1,1] := rfl
      rw [this]
      simp
      have : Fin.init ![(0 : Fin 2), 1, 1] (Fin.last 1) = 1 := rfl
      rw [this]
      simp
  · have : ![(0 : Fin 2), 1, 1] (Fin.last 2) = 1 := rfl
    rw [this]
    simp


-- Now we can define general Kayleigh graph for odd-length words.
def kayleighδ {A : Type*} {k : ℕ} (hk : k ≥ 1)
  {w : Fin (2*k+1) → A} : A → Fin (k+1) → Set (Fin (k+1)) := by
  let n := 2*k + 1
  intro b q r -- is r reachable in one step from q reading b?
  -- n = 3, n/2 = 1
  let b₀ := w ⟨q, by omega⟩
  let b₁ := w ⟨k + 1 - q, by omega⟩
  by_cases H : q = k -- q = 1
  · -- last state
    let P₀ : Prop := (b = b₀ ∧ q.1 = r.1) ∨ (b = w ⟨q+1,by omega⟩ ∧ r.1 + 1 = q.1)
    exact P₀
  · -- last q = 0
    let P : Prop := (b = b₀ ∧ r.1 = q.1 + 1) ∨ (b = b₁ ∧ q.1 = r.1 + 1)
    exact P


example : @kayleighδ (Fin 2) 1 (by omega) ![0,1,1] 0 = myδ 0 := by
  ext q x
  simp [kayleighδ, myδ]
  fin_cases q
  fin_cases x
  simp

  intro hc
  change (⟨0,by omega⟩ : Fin 2).1 = 1 at hc
  simp at hc
  simp
  rfl
  simp
  intro hc
  change False at hc
  tauto

example : @kayleighδ (Fin 2) 1 (by omega) ![0,1,1] 1 = myδ 1 := by
  ext q x
  simp [kayleighδ, myδ]
  fin_cases q
  fin_cases x
  simp

  intro hc
  change False at hc
  tauto
  simp
  intro hc
  tauto
  simp
  constructor
  intro h
  simp at h
  change 1 = x.1 ∨ x.1 = 0 at h
  cases h with
  | inl h =>
    simp_all
    right
    symm
    exact Fin.eq_of_val_eq h
  | inr h =>
    simp_all
    left
    exact @Fin.eq_of_val_eq (1+1) x 0 h
  intro h
  cases h with
  | inl h =>
    right
    exact (@Fin.mk.inj_iff 2 x.1 0 x.2 (by omega)).mp h
  | inr h =>
    change 1 = x.1 ∨ x.1 = 0
    left
    symm
    apply Fin.mk.inj_iff.mp h

example : 0 ∈ astN myδ ![0,1,1] 0 := by
  unfold myδ astN
  unfold astN
  unfold astN
  unfold astN
  simp
  use 1 -- the penultimate state
  constructor
  · have : Fin.init ![(0 : Fin 2),1,1] = ![0,1] := by
      ext i; fin_cases i <;> rfl
    rw [this]
    simp
    have : Fin.init ![(0 : Fin 2), 1] = ![0] := by
      ext i; fin_cases i; rfl
    rw [this]
    simp
  · use 1 -- the state before that
    constructor
    · have : Fin.init ![(0 : Fin 2), 1, 1] = ![0,1] := by
        ext i; fin_cases i <;> rfl
      rw [this]
      simp
      have : ![(0 : Fin 2), 1] (Fin.last 1) = 1 := by
        simp [Fin.last]
      rw [this]
      simp
    · have : ![(0 : Fin 2), 1, 1] (Fin.last 2) = 1 := by
        simp [Fin.last]
      rw [this]
      simp
    -- the state before that again would have to be 0.

open Classical
noncomputable def 𝓡 {Q A : Type*} [Fintype A] [Fintype Q]
    {δ : A → Q → Q} : ℕ → Q → Finset Q :=
      fun m c => filter (fun q : Q => ∃ w : Fin m → A, q = ast δ w c) (univ : Finset Q)

noncomputable def r {Q A : Type*} [Fintype A] [Fintype Q]
    {δ : A → Q → Q} : ℕ → Q → ℕ :=
      fun m c => #(𝓡 (δ := δ) m c)

    -- `in_particular` is the last statement on page 93 of my book.
theorem in_particular  {Q A : Type*} [Fintype A] [Fintype Q]
    {δ : A → Q → Q} (c : Q) : 𝓡 (δ := δ) 0 c = {c} := by
      unfold 𝓡;simp
      ext q
      simp
      constructor
      · intro h
        unfold ast at h
        exact h
      · intro h
        subst h
        unfold ast
        simp

theorem case1 {Q A : Type*} [Fintype A] [Fintype Q]
    {δ : A → Q → Q} (c : Q)
       : 𝓡 (δ := δ) 1 c = ⋃ b, δ b '' 𝓡 (δ := δ) 0 c := by
          unfold 𝓡
          simp
          ext x
          simp
          constructor
          · intro ⟨w,hw⟩
            use w 0
            rw [hw]
            show δ (w 0) (ast δ ![] c) = ast δ w c
            have : ast δ ![] c = c := by rfl
            rw [this]
            unfold ast
            simp
            unfold ast
            simp
          · intro ⟨b,hb⟩
            rw [← hb]
            use ![b]
            symm
            show ast δ ![b] c = δ b (ast δ ![] c)
            unfold ast
            simp
            unfold ast
            simp

theorem claimByQuas {Q A : Type*} [Fintype A] [Fintype Q] {δ : A → Q → Q} (c : Q) :
    ∀ m, 𝓡 (δ := δ) (m+1) c = ⋃ b, δ b '' (𝓡 (δ := δ) m c) := by
  intro m
  induction m with
  | zero => simp;apply case1
  | succ n ih =>
    ext q
    constructor
    · intro h
      unfold 𝓡 at h
      simp at h
      obtain ⟨w,hw⟩ := h
      simp
      use w (Fin.last (n+1))
      rw [hw]
      use (ast δ (Fin.init w) c)
      constructor
      · unfold 𝓡
        simp
        use Fin.init w
      · symm
        rfl
    · intro h
      simp at h
      unfold 𝓡
      simp
      obtain ⟨b,hb⟩ := h
      obtain ⟨q₀,hq₀⟩ := hb
      unfold 𝓡 at hq₀
      simp at hq₀
      obtain ⟨w,hw⟩ := hq₀.1
      rw [← hq₀.2]
      rw [hw]
      use Fin.snoc w b
      have := @Fin.init_snoc (n+1) (fun _ => A) b w
      nth_rewrite 2 [← this]
      unfold ast
      simp
      congr

lemma compl_of_card_lt (α : Type*) [Fintype α]:
        ∀ X ⊆ (Finset.univ : Finset α),
        #X < #(Finset.univ : Finset α) →
        ∃ b', b' ∈ (Finset.univ : Finset α) \ X := by
        intro X hX₀ hX₁
        have : (Finset.univ : Finset α) \ X ≠ ∅ := by
          contrapose hX₁
          simp_all
        apply Nonempty.exists_mem
        exact nonempty_iff_ne_empty.mpr this

open Fin
lemma ast_append  {Q A : Type*} [Fintype Q] [Fintype A] [Nonempty A]
    (δ : A → Q → Q) {u v : ℕ} (U : Fin u → A) (V : Fin v → A) (c : Q) :
    ast δ (append U V) c = ast δ V (ast δ U c) := by
  induction v with
  | zero =>
      simp [ast, append_right_nil]
  | succ n ih =>
      rw [← snoc_init_self V, append_snoc U (init V) (V (last n))]
      simp [ast]
      suffices ast δ (append U (init V)) c
             = ast δ (init V) (ast δ U c) by aesop
      rw [ih (init V)]

lemma Fin.rtake {M m : ℕ} (hmM : m + 1 ≤ M) (w : Fin M → A):
    ∃ v : Fin (M - (m+1)) → A,
    (fun i : Fin (m + 1 + (M - (m + 1))) => w ⟨i.1, by omega⟩)
    = Fin.append (Fin.take (m+1) hmM w) v := by
  use fun j => w ⟨m + 1 + j.1, by omega⟩
  simp [append, take, addCases]
  unfold addCases take
  simp
  ext j
  by_cases H : j < m+1
  · simp_all
    congr
  · simp_all
    split_ifs
    rfl
/-- Claim 4.43 in `Automatic complexity`. -/
theorem claim443 {Q A : Type*} [Fintype Q] [Fintype A] [Nonempty A]
    {δ : A → Q → Q} (hinj : ∀ a, Function.Injective (δ a))
    {c : Q} {m : ℕ} (h : r (δ := δ) m c = r (δ := δ) m.succ c)
    {M : ℕ} (hM : M > m)
    {d : Q} (hd : d ∈ 𝓡 (δ := δ) M c) :
      #(filter (fun w => ast δ w c = d) (univ : Finset (Fin M → A))) ≥ card A := by
    let S := 𝓡 (δ := δ) m c
    have h₀ : #S = r (δ := δ) m c := by rfl
    have h₁ (b : A) : #(image (δ b) S) = #S :=
      card_image_iff.mpr <| fun _ _ _ _ hq => hinj _ hq
    have h₃ (b : A) : image (δ b) S ⊆ 𝓡 (δ := δ) (m+1) c := by
      intro q hq
      simp at hq
      obtain ⟨a,ha⟩ := hq
      simp [S, 𝓡] at *
      obtain ⟨v,hv⟩ := ha.1
      rw [← ha.2, hv]
      use snoc v b
      nth_rewrite 1 [← @init_snoc m (fun _ => A) b v]
      conv =>
        right
        unfold ast -- yay!
      simp
    have h₄ (b : A) : #(image (δ b) S) = #(𝓡 (δ := δ) (m+1) c) := by simp_all; rfl
    have h₅ (b : A) : (image (δ b) S) = (𝓡 (m+1) c) :=
      Finset.eq_of_subset_of_card_le (h₃ b) (le_of_eq <| (h₄ b).symm)
    have h₂ (b b' : A) : image (δ b) S = image (δ b') S := by simp [h₅ b, h₅ b']
    -- end of line 5 on page 94 in my book.
    by_contra H
    simp at H
    let bfun : (Finset.filter (fun (w : Fin M → A) ↦ ast δ w c = d) univ) → A :=
        fun w => Fin.take (m+1) hM w.1 (Fin.last _)
    obtain ⟨b',hb'⟩ : ∃ b', ∀ w, ∀ hw : w ∈ (Finset.filter (fun (w : Fin M → A) ↦ ast δ w c = d) univ),
      b' ≠ bfun ⟨w,hw⟩ := by
      obtain ⟨b',hb'⟩ := compl_of_card_lt A
        (Finset.filter (fun b' : A ↦ ∃ w, ∃ (hw : ast δ w c = d), bfun ⟨w,by simp;exact hw⟩ = b') univ)
          (subset_univ _)
          (by
            simp
            suffices #(filter (fun (w : Fin M → A) ↦ ast δ w c = d) univ)
              ≥ #(filter (fun b' ↦ ∃ w, ∃ (hw : ast δ w c = d), bfun ⟨w, by simp;exact hw⟩ = b') univ) by
                calc _ ≤ _ := this
                     _ < _ := H
            simp
            have : filter (fun b' ↦ ∃ w, ∃ (hw : ast δ w c = d), bfun ⟨w, (by simp;exact hw)⟩ = b') univ
              = image bfun univ := by ext b; simp
            rw [this]
            have : #(univ : Finset { x // x ∈ filter (fun (w : Fin M → A) ↦ ast δ w c = d) univ })
                                          = #(filter (fun (w : Fin M → A) ↦ ast δ w c = d) univ) := by
              aesop
            exact this ▸ card_image_le
            )
      use b'
      simp_all
      exact fun w hw hc => hb' w hw hc.symm
    have h₉ (w : Fin M → A) (hw : w ∈ (filter (fun (w : Fin M → A) ↦ ast δ w c = d) univ)) :
      ∃ u' : Fin (m+1) → A, u' (Fin.last m) = b' ∧
        ast δ u' c = ast δ (Fin.take (m+1) (by omega) w) c := by
      have h₇ : ast δ (Fin.take (m+1) (by omega) w) c ∈ image (δ (bfun ⟨w,hw⟩)) S := by
        simp [S, 𝓡]
        use ast δ (Fin.take m (by omega) w) c
        constructor
        · use Fin.take m (by omega) w
        · simp [bfun]; rfl
      have h₈ : ast δ (Fin.take (m+1) (by omega) w) c ∈ image (δ b') S :=
        h₂ (bfun ⟨w,hw⟩) b' ▸ h₇
      simp at h₈
      simp_all [S, 𝓡]
      obtain ⟨q,hq⟩ := h₈
      obtain ⟨v,hv⟩ := hq.1
      use Fin.snoc v b'
      constructor
      · simp
      · rw [← hq.2, hv]
        nth_rewrite 2 [← @Fin.init_snoc m (fun _ => A) b' v]
        conv =>
          left
          unfold ast -- yay!
        simp
    simp [𝓡] at hd
    obtain ⟨w,hw⟩ := hd
    have hmM: (m+1) + (M - (m+1)) = M := by omega
    obtain ⟨v,hv⟩ := rtake _ _
    obtain ⟨u',hu'⟩ := h₉ w (by simp; exact hw.symm)
    have taut₀ : ast δ (Fin.append u' v) c = d := by
      rw [ast_append, hw, hu'.2]
      have : ast δ w c = ast δ (fun i : Fin (m + 1 + (M - (m + 1))) => w ⟨i.1, by omega⟩) c := by
        congr
        · omega
        · exact (Fin.heq_fun_iff hmM.symm).mpr (congrFun rfl) -- scary!
      rw [this, hv]
      symm
      apply ast_append
    have taut₁ : ∀ w, ast δ w c = d → w ≠ (Fin.append u' v) := by
      intro w hw hc
      have hb'' := hb' (fun i => w ⟨i.1, by omega⟩) (by
        simp
        rw [← hw]
        congr
        · omega
        · exact (Fin.heq_fun_iff (id (Eq.symm hmM))).mpr (congrFun rfl)
      )
      subst hc
      apply hb''
      rw [← hu'.1]
      simp[bfun,last,append,addCases]
    exact taut₁ (append u' v) taut₀ rfl

lemma arith {n : ℕ} (r : ℕ → ℕ) (hr : ∀ j < n, r j < r (j+1)) : n + r 0 ≤ r n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h₀ := ih (by intro k hk;apply hr;omega)
    have h₁ := hr n (by omega)
    omega

lemma arith' {n : ℕ} (r : ℕ → ℕ) (h : r 0 ≥ 1) (hr : ∀ j < n, r j < r (j+1)) : n + 1 ≤ r n := by
  have := arith r hr
  omega


theorem quas_family {Q A : Type*} [Fintype Q] [Fintype A]
    {δ : A → Q → Q} (hinj : ∀ a, Function.Injective (δ a))
    {n : ℕ} {c d : Q}
    (h₀ : #(filter (fun w => ast δ w c = d) (univ : Finset (Fin n → A))) ≥ 1)
    (h₁ : #(filter (fun w => ast δ w c = d) (univ : Finset (Fin n → A))) < card A)
: card Q ≥ n + 1 := by
    have hA : card A ≥ 2 := by omega
    have hcA : card A ≠ 0 := by exact Nat.not_eq_zero_of_lt hA
    have huA : (univ : Finset A) ≠ ∅ := by
      intro hc
      apply hcA
      show #(univ : Finset A) = 0
      simp_all
    have : ∃ a : A, a ∈ univ := by
      by_contra hc
      push_neg at hc
      apply huA
      ext a
      simp
      exact hc a (by simp)
    have : Nonempty A := by
      obtain ⟨a,ha⟩ := this
      exact Nonempty.intro a
    let a : A := Classical.choose <| (exists_const A).mpr trivial
    -- Now start the proof proper.
    have h₁ : #(filter (fun w => ast δ w c = d) (univ : Finset (Fin n → A))) < card A := by omega
    have h₂ : ∀ j < n, r (δ := δ) j c < r (δ := δ) (j+1) c := by
      by_contra H
      push_neg at H
      obtain ⟨j,hj⟩ := H
      have unstated : r (δ := δ) j c ≤ r (δ := δ) (j + 1) c := by
        simp [r, 𝓡]
        apply card_le_card_of_injOn
        show ∀ q ∈ filter (fun q ↦ ∃ w, q = ast δ w c) univ,
          δ a q ∈ filter (fun q ↦ ∃ w, q = ast δ w c) univ
        · simp
          intro w
          use Fin.snoc w a
          simp [ast,snoc]
        -- since δ's are 1:1
        · intro q₀ hq₀ q₁ hq₁ hq
          exact hinj a (hinj a (congrArg (δ a) hq))
      have := @claim443 Q A _ _ _ δ hinj c j (le_antisymm unstated hj.2) n hj.1 d (by
        simp [𝓡]
        have := h₀
        have ⟨w,hw⟩ : (filter (fun w : Fin n → A ↦ ast δ w c = d) univ).Nonempty := by
          apply (@Finset.card_pos (Fin n → A) (filter (fun w : Fin n → A ↦ ast δ w c = d) univ)).mp
          omega
        use w
        simp_all
      )
      omega
    have := @arith' n (fun j => r (δ := δ) j c) (by
      simp [r, 𝓡]
      use c
      simp
      rfl
    ) h₂
    simp at this
    apply le_trans this
    simp [r, 𝓡]
    have : card Q = #(univ : Finset Q) := rfl
    rw [this]
    exact card_filter_le univ fun q ↦ ∃ w, q = ast δ w c

/-- Quas' Theorem. -/
theorem quas' {Q A : Type*} [Fintype Q] [Fintype A]
    {δ : A → Q → Q} (hinj : ∀ a, Function.Injective (δ a))
    {n : ℕ} {c d : Q} (h₀ : #(filter (fun w => ast δ w c = d) (univ : Finset (Fin n → A))) = 1)
    (hA : card A ≥ 2) : card Q ≥ n + 1 :=
  @quas_family Q A _ _ δ hinj n c d (by omega) (by omega)
