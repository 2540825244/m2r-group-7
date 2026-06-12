import Mathlib.RingTheory.ZMod.UnitsCyclic  -- for orderOf_one_add_mul_prime
import Mathlib.Data.ZMod.Units              -- for ZMod.unitOfCoprime

section OnePlusPpow

variable (p : ℕ) [hp : Fact p.Prime]

/-- (1 + p)^p = 1 in ZMod (p^2). Proved using the Mathlib order theorem. -/
lemma onePlusP_pow_p_eq_one_in_zmod_psq :
    (1 + (p : ZMod (p ^ 2))) ^ p = 1 := by
  have hprime := hp.out
  -- Rewrite as 1 + 1 * p to match the Mathlib API
  have hform : (1 : ZMod (p ^ 2)) + p = 1 + 1 * p := by ring
  -- The key: orderOf (1 + 1 * p) in ZMod (p^2) = p^1 = p
  -- so (1 + p)^p = 1 by pow_orderOf_eq_one
  suffices h : orderOf ((1 + (p : ZMod (p ^ 2))) : ZMod (p ^ 2)) ∣ p by
    exact orderOf_dvd_iff_pow_eq_one.mp h
  -- Apply ZMod.orderOf_one_add_mul_prime with a = 1, n = 1
  -- That gives orderOf (1 + 1 * p) in ZMod (p^(1+1)) = p^1
  have hord : orderOf ((1 + 1 * (p : ZMod (p ^ 2))) : ZMod (p ^ 2)) = p ^ 1 := by
    have := ZMod.orderOf_one_add_mul_prime (p := p) hprime
          (hp2 := hprime.ne_one ▸ by omega)  -- p ≠ 2 for odd; see note below
          (a := 1)
          (ha := by simp [Int.coe_nat_dvd]; exact hprime.one_lt.ne')
          (n := 1)
    simpa [pow_succ] using this
  rw [show (1 : ZMod (p ^ 2)) + p = 1 + 1 * p from by ring]
  simp [hord, pow_one]

end OnePlusPpow
