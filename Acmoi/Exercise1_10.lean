import Mathlib.Data.Vector.Basic
import Mathlib.Data.List.Defs
import Mathlib.Data.Fintype.Vector

/-
In the following we prove A_N(0110)=3 and similar facts using dec_trivial.
-/

def slow {n:ℕ} {q:ℕ} (h : Mathlib.Vector (Fin q) n.succ): Prop :=
(h.get 0).1 = 0 ∧
∀ j : Fin q, ∃ i : Fin q, i.1 < j.1.succ ∧ (h.get j.1.succ).1 ≤ (h.get i.1).succ

instance {n b:ℕ}  (x : Mathlib.Vector (Fin b) n) (q:ℕ) (h : Mathlib.Vector (Fin q) n.succ):
Decidable (slow h) :=
decidable_of_iff (
(h.get 0).1 = 0 ∧
∀ j : Fin q, ∃ i : Fin q, i.1 < j.1.succ ∧ (h.get j.1.succ).1 ≤ (h.get i.1).succ
) (by rw [slow])


def is_witness {n b:ℕ} (x : Mathlib.Vector (Fin b) n) (q:ℕ) (h : Mathlib.Vector (Fin q) n.succ): Prop :=
-- (
--   (h.get 0).1 = 0 ∧
-- ∀ j : Fin q, ∃ i : Fin q, i.1 < j.1.succ ∧ (h.get j.1.succ).1 ≤ (h.get i.1).succ

-- ) ∧
  ∀ g : Mathlib.Vector (Fin q) n.succ,
    -- slow g →
    g.get 0 = h.get 0 →
    g.get n = h.get n →
    ∀ y : Mathlib.Vector (Fin b) n, (
      ∀ k : Fin n, ∃ l : Fin n,
        [h.get l.1, h.get l.1.succ] =
        [g.get k.1, g.get k.1.succ] ∧ x.get l = y.get k
    ) →
    g=h ∧ x=y


instance {n b:ℕ}  (x : Mathlib.Vector (Fin b) n) (q:ℕ) (h : Mathlib.Vector (Fin q) n.succ):
Decidable (is_witness x q h) :=
decidable_of_iff (
--   (
--     (h.get 0).1 = 0 ∧
-- ∀ j : Fin q, ∃ i : Fin q, i.1 < j.1.succ ∧ (h.get j.1.succ).1 ≤ (h.get i.1).succ

--   ) ∧
  ∀ g : Mathlib.Vector (Fin q) n.succ,
    -- slow g →

    g.get 0 = h.get 0 →
    g.get n = h.get n →
    ∀ y : Mathlib.Vector (Fin b) n, (
      ∀ k : Fin n, ∃ l : Fin n,
        [h.get l.1, h.get l.1.succ] =
        [g.get k.1, g.get k.1.succ] ∧ x.get l = y.get k
    ) →
    g=h ∧ x=y
) (by rw [is_witness])


def A_N_bounded_by
  {n b :ℕ}
  (x : Mathlib.Vector (Fin b) n)
  (q:ℕ) : Prop :=
∃ h : Mathlib.Vector (Fin q) n.succ, is_witness x q h

instance   {n b :ℕ}
  (x : Mathlib.Vector (Fin b) n)
  (q:ℕ) : Decidable (A_N_bounded_by x q) := decidable_of_iff (
∃ h : Mathlib.Vector (Fin q) n.succ, is_witness x q h
  ) (by rw [A_N_bounded_by])


def complexity_equals {n:ℕ} (x:Mathlib.Vector (Fin 2) n) (k:ℕ) : Prop :=
A_N_bounded_by x k ∧ ¬ A_N_bounded_by x (k-1)

instance {n:ℕ} (x:Mathlib.Vector (Fin 2) n) (k:ℕ) : Decidable (complexity_equals x k) :=
decidable_of_iff (
A_N_bounded_by x k ∧ ¬ A_N_bounded_by x (k-1)
) (by rw [complexity_equals])


#eval (∀ i ∈ [
  (complexity_equals (⟨[0,0,0,0], rfl⟩ : Mathlib.Vector (Fin 2) 4) 1 : Bool),
  (complexity_equals (⟨[0,0,0,1], rfl⟩ : Mathlib.Vector (Fin 2) 4) 2 : Bool),
  (complexity_equals (⟨[0,0,1,0], rfl⟩ : Mathlib.Vector (Fin 2) 4) 3 : Bool),
  (complexity_equals (⟨[0,0,1,1], rfl⟩ : Mathlib.Vector (Fin 2) 4) 3 : Bool),
  (complexity_equals (⟨[0,1,0,0], rfl⟩ : Mathlib.Vector (Fin 2) 4) 3 : Bool),
  (complexity_equals (⟨[0,1,0,1], rfl⟩ : Mathlib.Vector (Fin 2) 4) 2 : Bool),
  (complexity_equals (⟨[0,1,1,0], rfl⟩ : Mathlib.Vector (Fin 2) 4) 3 : Bool),
  (complexity_equals (⟨[0,1,1,1], rfl⟩ : Mathlib.Vector (Fin 2) 4) 2 : Bool)
], i = true : Bool)


#eval (∀ i ∈ [
  (complexity_equals (⟨[0,0,0,0,0], rfl⟩ : Mathlib.Vector (Fin 2) 5) 1 : Bool),
  (complexity_equals (⟨[0,0,0,0,1], rfl⟩ : Mathlib.Vector (Fin 2) 5) 2 : Bool),
  (complexity_equals (⟨[0,0,0,1,0], rfl⟩ : Mathlib.Vector (Fin 2) 5) 3 : Bool),
  (complexity_equals (⟨[0,0,0,1,1], rfl⟩ : Mathlib.Vector (Fin 2) 5) 3 : Bool),
  (complexity_equals (⟨[0,0,1,0,0], rfl⟩ : Mathlib.Vector (Fin 2) 5) 3 : Bool),
  (complexity_equals (⟨[0,0,1,0,1], rfl⟩ : Mathlib.Vector (Fin 2) 5) 3 : Bool),
  (complexity_equals (⟨[0,0,1,1,0], rfl⟩ : Mathlib.Vector (Fin 2) 5) 3 : Bool),
  (complexity_equals (⟨[0,0,1,1,1], rfl⟩ : Mathlib.Vector (Fin 2) 5) 3 : Bool),
  (complexity_equals (⟨[0,1,0,0,0], rfl⟩ : Mathlib.Vector (Fin 2) 5) 3 : Bool),
  (complexity_equals (⟨[0,1,0,0,1], rfl⟩ : Mathlib.Vector (Fin 2) 5) 3 : Bool),
  (complexity_equals (⟨[0,1,0,1,0], rfl⟩ : Mathlib.Vector (Fin 2) 5) 2 : Bool),
  (complexity_equals (⟨[0,1,0,1,1], rfl⟩ : Mathlib.Vector (Fin 2) 5) 3 : Bool),
  (complexity_equals (⟨[0,1,1,0,0], rfl⟩ : Mathlib.Vector (Fin 2) 5) 3 : Bool),
  (complexity_equals (⟨[0,1,1,0,1], rfl⟩ : Mathlib.Vector (Fin 2) 5) 3 : Bool),
  (complexity_equals (⟨[0,1,1,1,0], rfl⟩ : Mathlib.Vector (Fin 2) 5) 3 : Bool),
  (complexity_equals (⟨[0,1,1,1,1], rfl⟩ : Mathlib.Vector (Fin 2) 5) 2 : Bool)
], i = true : Bool)


-- #eval (∀ i ∈ [
--   (complexity_equals (⟨[0,0,0,0,0,0], rfl⟩ : Mathlib.Vector (Fin 2) 6) 1 : Bool),
--   (complexity_equals (⟨[0,0,0,0,0,1], rfl⟩ : Mathlib.Vector (Fin 2) 6) 2 : Bool),
--   (complexity_equals (⟨[0,0,0,0,1,0], rfl⟩ : Mathlib.Vector (Fin 2) 6) 3 : Bool),
--   (complexity_equals (⟨[0,0,0,0,1,1], rfl⟩ : Mathlib.Vector (Fin 2) 6) 3 : Bool),
--   (complexity_equals (⟨[0,0,0,1,0,0], rfl⟩ : Mathlib.Vector (Fin 2) 6) 4 : Bool),
--   (complexity_equals (⟨[0,0,0,1,0,1], rfl⟩ : Mathlib.Vector (Fin 2) 6) 4 : Bool),
--   (complexity_equals (⟨[0,0,0,1,1,0], rfl⟩ : Mathlib.Vector (Fin 2) 6) 4 : Bool),
--   (complexity_equals (⟨[0,0,0,1,1,1], rfl⟩ : Mathlib.Vector (Fin 2) 6) 4 : Bool),
--   (complexity_equals (⟨[0,0,1,0,0,0], rfl⟩ : Mathlib.Vector (Fin 2) 6) 4 : Bool),
--   (complexity_equals (⟨[0,0,1,0,0,1], rfl⟩ : Mathlib.Vector (Fin 2) 6) 3 : Bool),
--   (complexity_equals (⟨[0,0,1,0,1,0], rfl⟩ : Mathlib.Vector (Fin 2) 6) 3 : Bool),
--   (complexity_equals (⟨[0,0,1,0,1,1], rfl⟩ : Mathlib.Vector (Fin 2) 6) 4 : Bool),
--   (complexity_equals (⟨[0,0,1,1,0,0], rfl⟩ : Mathlib.Vector (Fin 2) 6) 3 : Bool), -- !
--   (complexity_equals (⟨[0,0,1,1,0,1], rfl⟩ : Mathlib.Vector (Fin 2) 6) 4 : Bool),
--   (complexity_equals (⟨[0,0,1,1,1,0], rfl⟩ : Mathlib.Vector (Fin 2) 6) 3 : Bool), -- !
--   (complexity_equals (⟨[0,0,1,1,1,1], rfl⟩ : Mathlib.Vector (Fin 2) 6) 3 : Bool),
--   (complexity_equals (⟨[0,1,0,0,0,0], rfl⟩ : Mathlib.Vector (Fin 2) 6) 3 : Bool),
--   (complexity_equals (⟨[0,1,0,0,0,1], rfl⟩ : Mathlib.Vector (Fin 2) 6) 4 : Bool),
--   (complexity_equals (⟨[0,1,0,0,1,0], rfl⟩ : Mathlib.Vector (Fin 2) 6) 3 : Bool),
--   (complexity_equals (⟨[0,1,0,0,1,1], rfl⟩ : Mathlib.Vector (Fin 2) 6) 4 : Bool),
--   (complexity_equals (⟨[0,1,0,1,0,0], rfl⟩ : Mathlib.Vector (Fin 2) 6) 3 : Bool),
--   (complexity_equals (⟨[0,1,0,1,0,1], rfl⟩ : Mathlib.Vector (Fin 2) 6) 2 : Bool),
--   (complexity_equals (⟨[0,1,0,1,1,0], rfl⟩ : Mathlib.Vector (Fin 2) 6) 4 : Bool),
--   (complexity_equals (⟨[0,1,0,1,1,1], rfl⟩ : Mathlib.Vector (Fin 2) 6) 4 : Bool),
--   (complexity_equals (⟨[0,1,1,0,0,0], rfl⟩ : Mathlib.Vector (Fin 2) 6) 4 : Bool),
--   (complexity_equals (⟨[0,1,1,0,0,1], rfl⟩ : Mathlib.Vector (Fin 2) 6) 4 : Bool),
--   (complexity_equals (⟨[0,1,1,0,1,0], rfl⟩ : Mathlib.Vector (Fin 2) 6) 4 : Bool),
--   (complexity_equals (⟨[0,1,1,0,1,1], rfl⟩ : Mathlib.Vector (Fin 2) 6) 3 : Bool),
--   (complexity_equals (⟨[0,1,1,1,0,0], rfl⟩ : Mathlib.Vector (Fin 2) 6) 3 : Bool), -- !
--   (complexity_equals (⟨[0,1,1,1,0,1], rfl⟩ : Mathlib.Vector (Fin 2) 6) 4 : Bool),
--   (complexity_equals (⟨[0,1,1,1,1,0], rfl⟩ : Mathlib.Vector (Fin 2) 6) 3 : Bool),
--   (complexity_equals (⟨[0,1,1,1,1,1], rfl⟩ : Mathlib.Vector (Fin 2) 6) 2 : Bool)
-- ], i = true : Bool)
