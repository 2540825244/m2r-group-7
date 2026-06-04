import Mathlib

/-- A kernel-computable characterisation of `n.factorization p = k`.
It is an `abbrev` built only from `Nat.Prime`, `∣`, `=`, `∧`, `∨`, `¬` — all of
which have `Decidable` instances the kernel can actually evaluate, unlike
`Nat.factorization` (which is well-founded recursive and never reduces). -/
abbrev FactSpec (n p k : ℕ) : Prop :=
  (p.Prime ∧ ((n ≠ 0 ∧ p ^ k ∣ n ∧ ¬ p ^ (k + 1) ∣ n) ∨ (n = 0 ∧ k = 0))) ∨
  (¬ p.Prime ∧ k = 0)

theorem factorization_eq_iff {n p k : ℕ} : n.factorization p = k ↔ FactSpec n p k := by
  unfold FactSpec
  by_cases hp : p.Prime
  · simp only [hp, true_and, not_true_eq_false, false_and, or_false]
    rcases eq_or_ne n 0 with rfl | hn
    · simp [eq_comm]
    · rw [or_iff_left (by simp [hn])]
      constructor
      · rintro rfl
        exact ⟨hn, Nat.ordProj_dvd n p, by
          rw [hp.pow_dvd_iff_le_factorization hn]; omega⟩
      · rintro ⟨-, h1, h2⟩
        refine le_antisymm ?_ ((hp.pow_dvd_iff_le_factorization hn).1 h1)
        by_contra hlt
        exact h2 ((hp.pow_dvd_iff_le_factorization hn).2 (Nat.lt_of_not_le hlt))
  · simp only [hp, false_and, not_false_eq_true, true_and, false_or,
      Nat.factorization_eq_zero_of_not_prime n hp, eq_comm]

/-- The custom `Decidable` instance routes `decide` through `FactSpec`
(which the kernel can reduce) instead of `Nat.factorization`. -/
instance (n p k : ℕ) : Decidable (n.factorization p = k) :=
  decidable_of_iff _ factorization_eq_iff.symm

-- Now plain `decide` works:
example : (7 - 1).factorization 2 = 1 := by decide
example : (96).factorization 2 = 5 := by decide
example : (96).factorization 3 = 1 := by decide
example : (97).factorization 2 = 0 := by decide
example : (100).factorization 5 = 2 := by decide
example : (0).factorization 7 = 0 := by decide
example : (84).factorization 7 = 1 := by decide
