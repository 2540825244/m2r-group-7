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

/-- For q odd prime (q ≠ 2): 1 ≤ min 2 ((q - 1).factorization 2). -/
lemma one_le_min_two_factorization_two {q : ℕ} [hq : Fact q.Prime] (h : q ≠ 2) :
    1 ≤ min 2 ((q - 1).factorization 2) := by
  have h_qm1_ne : q - 1 ≠ 0 := by have := hq.out.one_lt; omega
  refine Nat.le_min.mpr ⟨one_le_two, ?_⟩
  rw [← Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two h_qm1_ne]
  simpa using two_dvd_prime_sub_one h

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

/-- For distinct primes p q, the factorization of p * q at p is exactly 1. -/
lemma factorization_prime_mul_prime_left {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) : (p * q).factorization p = 1 :=
  Nat.factorization_eq_one_of_squarefree
    (Nat.squarefree_mul_iff.mpr ⟨hp.coprime_of_ne hq hpq, hp.squarefree, hq.squarefree⟩)
    hp (dvd_mul_right p q)

/-- For q prime, q ≡ 3 (mod 4): gcd(4, q - 1) = 2. -/
lemma gcd_four_of_prime_three_mod_four {q : ℕ} [Fact q.Prime]
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

/-- For distinct primes p < q < r, the smallest prime factor of p * q * r is p. -/
lemma minFac_mul_of_prime_triple {p q r : ℕ}
    [h_p : Fact p.Prime] [h_q : Fact q.Prime] [h_r : Fact r.Prime]
    (hpq : p < q) (hqr : q < r) : Nat.minFac (p * q * r) = p := by
  have hf_prime : (p * q * r).minFac.Prime := Nat.minFac_prime (by
    have : 1 < p * q * r :=
      calc 1 < p := h_p.out.one_lt
           _ ≤ p * (q * r) := Nat.le_mul_of_pos_right _ (Nat.mul_pos h_q.out.pos h_r.out.pos)
           _ = p * q * r := by ring
    omega)
  have hf_le_p : (p * q * r).minFac ≤ p :=
    Nat.minFac_le_of_dvd h_p.out.two_le (dvd_mul_of_dvd_left (dvd_mul_right p q) r)
  have hf_dvd_p : (p * q * r).minFac ∣ p := by
    have hf1 := hf_prime.one_lt
    rcases hf_prime.dvd_mul.mp (Nat.minFac_dvd (p * q * r)) with h | hr'
    · rcases hf_prime.dvd_mul.mp h with hp' | hq'
      · exact hp'
      · rcases h_q.out.eq_one_or_self_of_dvd _ hq' with h1 | h2 <;> omega
    · rcases h_r.out.eq_one_or_self_of_dvd _ hr' with h1 | h2 <;> omega
  exact le_antisymm hf_le_p
    ((h_p.out.eq_one_or_self_of_dvd _ hf_dvd_p).resolve_left hf_prime.one_lt.ne' |>.symm.le)
