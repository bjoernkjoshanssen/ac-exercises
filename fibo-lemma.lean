import data.nat.basic
import data.nat.fib
import data.nat.modeq
open nat

lemma lemma_1_92 (t p s : ℕ) (hp : 1 ≤ p) (h : fib (t+1) ≡ 0 [MOD p]):
2*s ≤ t → (fib (t+1+2*s) + fib(t+1-2*s) ≡ 0 [MOD p])
∧
fib (t + 2+2*s) ≡ fib (t  - 2*s) [MOD p] :=
nat.rec_on s (
  λ hs,
  and.intro
  ( -- Base case
    calc  fib (t+1) + fib (t+1)
        ≡ 0 +         fib (t+1) [MOD p]: nat.modeq.add_right (fib (t+1)) h
    ... = fib (t+1)                    : by ring_nf
    ... ≡ 0                     [MOD p]: h
  ) (
    calc fib (t+2) = fib t + fib (t+1)        : fib_add_two
               ... ≡ fib t + 0         [MOD p]: nat.modeq.add_left (fib t) h
               ... = fib t                    : by ring_nf
  )
) ( -- Inductive step
  λ s, λ h_ind, λ hs,
    have hah: 2+2*s ≤ t, from calc
              2+2*s = 2*succ s: by ring
                ... ≤ t: hs,
    have ha: 1+2*s ≤ t, from calc
             1+2*s ≤ 2+2*s: add_le_add_right one_le_two (2*s)
             ... ≤ t: hah,
    have hs': 2*s ≤ t, from
      calc  2*s ≤ 2*(s.succ): mul_le_mul_of_nonneg_left (le_succ s) (zero_le 2)
            ... ≤ t: hs,
    have htt: 2 ≤ t-2*s, from (le_tsub_iff_right hs').mpr hah,
    have hss: 1≤ t-2*s, from (le_tsub_iff_right hs').mpr ha,

    have fat2: fib (t + 1 + 2 * s + 2 ) ≡ fib (t + 1 + 2 * s) + fib (t + 1 + 2 * s+1) [MOD p], by rw fib_add_two,
    have fat4: fib (t - 2 * s - 1 + 2 ) ≡ fib (t - 2 * s - 1) + fib (t - 2 * s-1+1) [MOD p], by rw fib_add_two,
    have moar: t-2*s-1=t+1-2*succ s, from calc
              t-2*s-1 = t-2*s+1-2: by ring
                  ... = t-2*s-2+1: by rw (tsub_add_eq_add_tsub htt)
                  ... = t-2*(s+1)+1: by ring
                  ... = t+1-2*(s+1): by rw tsub_add_eq_add_tsub hs
                  ... = t+1-2*succ s: rfl,

    have help2: t + 1 - 2 * succ s = t - 2 * s - 1, from
        calc t + 1 - 2 * succ s
          = t + 1 - 2 * s - 2: rfl
        ...= t - 2 * s + 1 - 2: by rw (tsub_add_eq_add_tsub hs')
        ...= t - 2 * s - 1    : by ring,
    have help3: t - 2 * s - 1 + 2 = t + 1 - 2 * s, from calc
                t - 2 * s - 1 + 2
              = t - 2 * s + 2 - 1: by rw tsub_add_eq_add_tsub hss
          ...  = t - 2 * s + 1: by ring
          ...  = t + 1 - 2 * s: by rw tsub_add_eq_add_tsub hs',
    have H1:fib (t + 1 + 2 * succ s)                    + fib (t + 1 - 2 * succ s)≡ 0 [MOD p], from
      calc  fib (t + 1 + 2 * succ s)                    + fib (t + 1 - 2 * succ s)
          = fib (t + 1 + 2 * (s + 1))                    + fib (t + 1 - 2 * succ s): by ring
      ... = fib (t + 1 + 2 * s + 2)                    + fib (t + 1 - 2 * succ s): by ring_nf
      ... = fib (t + 1 + 2 * s) + fib (t + 1 + 2 * s+1) + fib (t + 1 - 2 * succ s) : by rw fib_add_two
      ... = fib (t + 2 + 2 * s) + (fib (t + 1 + 2 * s)  + fib (t + 1 - 2 * succ s)) : by ring_nf
      ... ≡ fib (t - 2 * s)     + (fib (t + 1 + 2 * s)  + fib (t + 1 - 2 * succ s)) [MOD p]: nat.modeq.add_right _ (h_ind hs').2

      ... = fib (t + 1 + 2 * s) + fib (t + 1 - 2 * succ s) + fib (t - 2 * s)           : by ring_nf
      ... = fib (t + 1 + 2 * s) + fib (t + 1 - 2 * succ s) + fib (t - 2 * s + 1 - 1)   : by ring_nf
      ... = fib (t + 1 + 2 * s) + fib (t + 1 - 2 * succ s) + fib (t - 2 * s - 1 + 1)   : by rw (tsub_add_eq_add_tsub hss).symm
      ... = fib (t + 1 + 2 * s) + (fib (t + 1 - 2 * succ s) + fib (t - 2 * s - 1 + 1)) : by ring_nf

      ... = fib (t + 1 + 2 * s) + (fib (t - 2 * s - 1)     + fib (t - 2 * s - 1 + 1))  :by {rw help2}
      ... ≡ fib (t + 1 + 2 * s) + fib (t - 2 * s - 1 + 2)                       [MOD p]:(nat.modeq.add_left _ fat4).symm
      ... = fib (t + 1 + 2 * s) + fib (t + 1 - 2 * s)                                  :by rw help3
      ... ≡ 0 [MOD p]: (h_ind hs').1,
  
    have H2: fib (t + 2 + 2 * succ s)≡ fib (t - 2 * succ s) [MOD p], from
      have fib (t+2+2*succ s)+fib (t-2*s-1) ≡ fib(t-2*succ s)+fib (t-2*s-1) [MOD p], from calc
      fib (t+2+2*succ s)+fib (t-2*s-1) = fib (t+2*succ s+2)+fib (t-2*s-1) : by ring_nf
      ... = fib (t+2*succ s)+fib(t+2*succ s+1)+fib (t-2*s-1)              : by rw fib_add_two
      ... = fib (t+2*(s+1))  +(fib (t-2*s-1)+fib(t+2*succ s+1)) : by ring
      ... = fib (t+2+2* s)  +(fib (t-2*s-1)+fib(t+2*succ s+1))  : by ring_nf
      ... ≡ fib (t-2* s)  +(fib (t-2*s-1)     +fib(t+2*succ s+1)) [MOD p]: nat.modeq.add_right _ (h_ind hs').2
      ... = fib (t-2* s)  +(fib (t+1-2*succ s)+fib(t+2*succ s+1)) : by rw moar
      ... = fib (t-2* s)  +(fib (t+1+2*succ s)+fib(t+1-2*succ s)) : by ring_nf
      ... ≡ fib (t-2* s)  + 0                                     [MOD p]: nat.modeq.add_left _ H1
      ... = fib (t-2* s+2-2)                   : by ring_nf
      ... = fib (t-2*s-2+2)                    : by rw (tsub_add_eq_add_tsub htt)
      ... = fib (t-2*s-2)    + fib (t-2*s-2+1) : by rw fib_add_two
      ... = fib (t-2*s-2)    + fib (t-2*s+1-2) : by rw tsub_add_eq_add_tsub htt
      ... = fib (t-2*s-2)    + fib (t-2*s-1)   : by ring
      ... = fib (t-(2*s+2))  + fib (t-2*s-1)   : rfl
      ... = fib (t-2*(s+1))  + fib (t-2*s-1)   : by ring_nf
      ... = fib (t-2*succ s) + fib (t-2*s-1)   : by ring,
      calc fib (t + 2 + 2 * succ s)
      ≡ fib (t - 2 * succ s) [MOD p]: modeq.add_right_cancel' (fib (t - 2 * s - 1)) this,
and.intro H1 H2  
)
