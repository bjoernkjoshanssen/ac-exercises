import number_theory.arithmetic_function
def μ : ℕ → ℤ := nat.arithmetic_function.moebius


lemma get_mu_zero (p n:ℕ) : ¬ is_unit p → p * p ∣ n → μ n = 0 := 
  λ hiu hdvd, 
  have  ¬ ( p * p ∣ n → is_unit p), from
    λ h , hiu (h hdvd),
  have  ∃ x:ℕ, ¬ ( x * x ∣ n → is_unit x), from exists.intro p this,
  have ¬  ∀ (x : ℕ), x * x ∣ n → is_unit x, from not_forall.mpr this,
  nat.arithmetic_function.moebius_eq_zero_of_not_squarefree this

lemma moebius_mul_prime (p q : ℕ) : nat.prime p → nat.prime q → nat.coprime p q →  μ (p * q) = 1 :=
  λ hp hq hpq,
  have hmp: μ p = -1, from nat.arithmetic_function.moebius_apply_prime hp,
  have hmq: μ q = -1, from nat.arithmetic_function.moebius_apply_prime hq,
  calc μ (p * q) = μ p * μ q : (nat.arithmetic_function.is_multiplicative_moebius).2 hpq
             ... = (-1) * μ q: by rw hmp
             ... = (-1) * (-1):by rw hmq
             ... = 1: rfl 


lemma mu1 : μ (1:ℕ) = (1:ℤ) := nat.arithmetic_function.moebius_apply_one
lemma mu2 : μ 2 = -1 := nat.arithmetic_function.moebius_apply_prime (by norm_num)
lemma mu3  : μ  3 = -1 := nat.arithmetic_function.moebius_apply_prime (by norm_num)
lemma mu5  : μ  5 = -1 := nat.arithmetic_function.moebius_apply_prime (by norm_num)
lemma mu7  : μ  7 = -1 := nat.arithmetic_function.moebius_apply_prime (by norm_num)
lemma mu17 : μ 17 = -1 := nat.arithmetic_function.moebius_apply_prime (by norm_num)
lemma mu11 : μ 11 = -1 := nat.arithmetic_function.moebius_apply_prime (by norm_num)
lemma mu13 : μ 13 = -1 := nat.arithmetic_function.moebius_apply_prime (by norm_num)

lemma mu4 : μ ( 4:ℕ) = (0:ℤ) := get_mu_zero 2  4 (of_to_bool_ff rfl) (by norm_num)
lemma mu8 : μ ( 8:ℕ) = (0:ℤ) := get_mu_zero 2  8 (of_to_bool_ff rfl) (by norm_num)
lemma mu16: μ ( 16:ℕ) = (0:ℤ) := get_mu_zero 2  16 (of_to_bool_ff rfl) (by norm_num)
lemma mu9 : μ ( 9:ℕ) = (0:ℤ) := get_mu_zero 3  9 (of_to_bool_ff rfl) (by norm_num)
lemma mu12: μ (12:ℕ) = (0:ℤ) := get_mu_zero 2 12 (of_to_bool_ff rfl) (by norm_num)

lemma mu6 : μ  6 = 1 :=   moebius_mul_prime 2 3 (by norm_num) (by norm_num) (by norm_num) 
lemma mu10: μ 10 = 1 :=   moebius_mul_prime 2 5 (by norm_num) (by norm_num) (by norm_num) 
lemma mu14: μ 14 = 1 :=   moebius_mul_prime 2 7 (by norm_num) (by norm_num) (by norm_num) 
lemma mu15 : μ 15 = 1 :=  moebius_mul_prime 3 5 (by norm_num) (by norm_num) (by norm_num) 


example :
  [μ 0,μ 1,μ 2,μ 3,μ 4,μ 5,μ 6,μ 7,μ 8,μ 9,μ 10,μ 11,μ 12,μ 13,μ 14, μ 15, μ 16]
= [  0,  1, -1, -1,  0, -1,  1, -1,  0,  0,   1,  -1,   0,  -1,   1,    1,    0]
  :=
  by {
    simp,
    exact (
      and.intro rfl (
        and.intro mu1 (
          and.intro mu2 (
            and.intro mu3 (
              and.intro mu4 (
                and.intro mu5 (
                  and.intro mu6 (
                    and.intro mu7 (
                      and.intro mu8 (
                        and.intro mu9 (
                          and.intro mu10 (
                            and.intro mu11 (
                              and.intro mu12 (
                                and.intro mu13 (
                                  and.intro mu14 (
                                    and.intro mu15 mu16)))
                            )
                          )
                        )
                      )
                    )
                  )
                )
              )
            )
          )
        )
      )
    )
  }
