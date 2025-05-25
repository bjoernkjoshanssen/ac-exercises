import Mathlib.Data.Matrix.Basic

section general

theorem sub_succ_add_one {n b : ℕ} (hn: n ≥ b.succ) : n - Nat.succ (b) + 1 = n - b := by omega

def moveOne (i s : Fin 2 → ℕ) : (Nat.succ (Matrix.dotProduct i s)) = (i 0 * s 0 + 1 + i 1 * s 1) := by
  simp [Matrix.dotProduct]
  omega

def functional_eq_add_of_le  {m n : ℕ} (h : m ≤ n) : {k // n = m + k} :=
  ⟨n - m, (Nat.add_sub_of_le h).symm⟩

theorem unique_iff_of_bijective {α β : Type} {P : α → Prop} {Q : β → Prop}
    {f : {a : α // P a}  → {b : β // Q b}} (h : Function.Bijective f) :
    (∃! a, P a) ↔ (∃! b, Q b) := by
  constructor
  · intro ⟨a,ha⟩
    exists f ⟨a,ha.1⟩
    constructor
    · exact (f ⟨a,ha.1⟩).2
    · intro b hQb
      have ⟨a'pair,ha'pair⟩ := h.2 ⟨b,hQb⟩
      let a' := a'pair.1
      let heq := ha.2 a'pair a'pair.2
      have : a' = a'pair.1 := rfl
      rw [← this] at heq
      have hae: a'pair = ⟨a,ha.1⟩ := Subtype.coe_eq_of_eq_mk heq
      rw [hae] at ha'pair
      exact congr_arg (λ x ↦ x.1) ha'pair.symm
  · intro ⟨b,hb⟩
    have ⟨apair,ha⟩ := h.2 ⟨b,hb.1⟩
    exists apair
    constructor
    · exact apair.2
    · intro a' ha'
      let a'pair := (⟨a',ha'⟩ : { a // P a})
      have h₁: f a'pair = b     := hb.2 (f a'pair) (f a'pair).2
      have h₁': f a'pair = ⟨b,hb.1⟩ := Subtype.coe_eq_of_eq_mk h₁
      have h₃: f a'pair = f apair := Eq.trans h₁' ha.symm
      exact congr_arg (λ x ↦ x.1) (h.1 h₃)

  def find_spec_le {Z : ℕ → Prop} {u : ℕ} (hu: Z u) [DecidablePred Z] :
      {t₀ // Z t₀ ∧ ∀ v, Z v → t₀ ≤ v} :=
    ⟨Nat.find (Exists.intro u hu), by
      constructor
      exact Nat.find_spec _
      intro v hv
      exact Nat.find_le hv
    ⟩

  -- To get uniqueness we turn ∃ results into functional results:
  def get_equation'' {a n : ℕ} (han : (a) % n = 0): {k // a = n * k} := by
    have : n ∣ a := by exact Nat.dvd_of_mod_eq_zero han
    have : a / n * n = a := Nat.div_mul_cancel this
    rw [mul_comm] at this
    exact ⟨(a)/n,this.symm⟩

  def get_equation' {a b n : ℕ} (hab: a ≤ b) (han : (b) % n = a % n): {k // b = a + n * k} := by
    have : (b - a) % n = 0 := Nat.sub_mod_eq_zero_of_mod_eq han
    have pair : {k // b-a = n*k} := get_equation'' this
    have : b = a + n * pair.1 := calc
      _ = (b-a) + a := Nat.eq_add_of_sub_eq hab rfl
      _ = (n*pair.1) + a := congr_arg (λ x ↦ x + a) pair.2
      _ = _ := Nat.add_comm _ _
    exact ⟨pair.1, this⟩


  theorem get_equation {a b n : ℕ} (hab: a ≤ b) (han : (b) % n = a % n) :
      ∃ k, b = a + n * k := by
    have pair := get_equation' hab han; exact ⟨pair.1, pair.2⟩

  theorem zero_of_mod {a n : ℕ} (hn: 1 ≤ n) (ha: a % n  = 0 ) (han: a < n) : a = 0 := by
    have := (@Nat.mod_eq_iff_lt a n (by omega)).mpr han
    apply Eq.trans this.symm ha

end general
