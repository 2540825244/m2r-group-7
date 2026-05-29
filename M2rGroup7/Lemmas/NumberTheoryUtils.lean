import Mathlib

/-- Two distinct primes are coprime. -/
lemma Nat.Prime.coprime_of_ne {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    Nat.Coprime p q :=
  hp.coprime_iff_not_dvd.mpr fun hdvd =>
    hpq ((hq.eq_one_or_self_of_dvd p hdvd).resolve_left hp.one_lt.ne')

/-- For q an odd prime (q > 2), 2 divides q - 1. -/
lemma two_dvd_prime_sub_one {q : ℕ} [hq : Fact q.Prime] (h : q ≠ 2) : 2 ∣ q - 1 := by
  have hq_odd : Odd q := hq.out.odd_of_ne_two h
  obtain ⟨k, rfl⟩ := hq_odd; omega

/-- For q prime, q > 3: 1 ≤ min 2 ((q - 1).factorization 2). -/
lemma one_le_min_two_factorization_two {q : ℕ} [hq : Fact q.Prime] (h : q > 3) :
    1 ≤ min 2 ((q - 1).factorization 2) := by
  have h_qm1_ne : q - 1 ≠ 0 := by have := hq.out.one_lt; omega
  refine Nat.le_min.mpr ⟨one_le_two, ?_⟩
  rw [← Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two h_qm1_ne]
  simpa using two_dvd_prime_sub_one (by omega)

/-- For q prime, q ≡ 3 (mod 4): (q - 1).factorization 2 = 1. -/
lemma factorization_two_of_prime_three_mod_four {q : ℕ} [hq : Fact q.Prime]
    (h : q ≡ 3 [MOD 4]) : (q - 1).factorization 2 = 1 := by
  have h_qm1_ne : q - 1 ≠ 0 := by have := hq.out.one_lt; omega
  have h_ge : 1 ≤ (q - 1).factorization 2 := by
    rw [← Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two h_qm1_ne, pow_one]
    have : q % 4 = 3 := h; omega
  have h_not2 : ¬ (2 ≤ (q - 1).factorization 2) := by
    rw [← Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two h_qm1_ne]
    intro h4
    have hmod : q % 4 = 3 := h
    have hdvd : (4 : ℕ) ∣ q - 1 := by simpa using h4
    omega
  omega

/-- For q prime, q ≡ 1 (mod 4): 2 ≤ (q - 1).factorization 2. -/
lemma two_le_factorization_two_of_prime_one_mod_four {q : ℕ} [hq : Fact q.Prime]
    (h : q ≡ 1 [MOD 4]) : 2 ≤ (q - 1).factorization 2 := by
  have h_qm1_ne : q - 1 ≠ 0 := by have := hq.out.one_lt; omega
  rw [← Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two h_qm1_ne]
  have hmod : q % 4 = 1 := h
  have h4 : (4 : ℕ) ∣ q - 1 := by omega
  simpa [show (2:ℕ) ^ 2 = 4 by norm_num] using h4

/-- For q prime, q ≡ 1 (mod 4): 2 ≤ min 2 ((q - 1).factorization 2). -/
lemma two_le_min_two_factorization_two_of_one_mod_four {q : ℕ} [hq : Fact q.Prime]
    (h : q ≡ 1 [MOD 4]) : 2 ≤ min 2 ((q - 1).factorization 2) :=
  Nat.le_min.mpr ⟨le_refl _, two_le_factorization_two_of_prime_one_mod_four h⟩

/-- For q prime, q ≡ 3 (mod 4): gcd(4, q - 1) = 2. -/
lemma gcd_four_of_prime_three_mod_four {q : ℕ} [hq : Fact q.Prime]
    (h : q ≡ 3 [MOD 4]) : Nat.gcd 4 (q - 1) = 2 := by
  have hmod : q % 4 = 3 := h
  have h2_dvd_gcd : 2 ∣ Nat.gcd 4 (q - 1) :=
    Nat.dvd_gcd (by norm_num) (by omega)
  have h_gcd_dvd_4 : Nat.gcd 4 (q - 1) ∣ 4 := Nat.gcd_dvd_left _ _
  have h_gcd_dvd_qm1 : Nat.gcd 4 (q - 1) ∣ q - 1 := Nat.gcd_dvd_right _ _
  have h_not_4_dvd : ¬ (4 ∣ q - 1) := by
    intro h_dvd; rw [Nat.dvd_iff_mod_eq_zero] at h_dvd; omega
  have h_pos : 0 < Nat.gcd 4 (q - 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
  have h_le : Nat.gcd 4 (q - 1) ≤ 4 := Nat.le_of_dvd (by norm_num) h_gcd_dvd_4
  interval_cases Nat.gcd 4 (q - 1)
  · exact absurd h2_dvd_gcd (by decide)
  · rfl
  · exact absurd h_gcd_dvd_4 (by decide)
  · exact absurd h_gcd_dvd_qm1 h_not_4_dvd
