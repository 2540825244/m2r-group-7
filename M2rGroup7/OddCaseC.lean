import Mathlib
import «M2rGroup7».OddCaseA
import «M2rGroup7».OddCaseB
import «M2rGroup7».SmallGroupsLibrary

set_option maxHeartbeats 3200000

open scoped commutatorElement

/-!
# Case C (odd prime): Both generators have order p² → C_{p²} ⋊ C_p

For odd primes p, when both generators a and b of a non-abelian group G
of order p³ have order p², we can substitute b' = b * a^(p²-m) (where
b^p = a^(m*p)) to obtain an element of order p that doesn't commute with a,
reducing to Case B2.

The key tool is the commutator power formula for class-2 groups:
  (b * a^k)^n = ⁅a,b⁆^(k * n*(n-1)/2) * b^n * a^(k*n)
which for odd p simplifies to (b * a^k)^p = b^p * a^(k*p).
-/

variable {G : Type*} [Group G] {p : ℕ} [hp : Fact p.Prime]

section CommutatorFormula

/-
General commutator power formula for class-2 groups:
    (b * a^k)^n = ⁅a,b⁆^(k * (n*(n-1)/2)) * b^n * a^(k*n)
    when ⁅a,b⁆ is central.

    Proof by induction on n, using `comm_rearrange_one` for the key step
    a^m * b = ⁅a,b⁆^m * b * a^m.
-/
lemma pow_mul_central_comm (a b : G) (k n : ℕ)
    (hz : ∀ g : G, g * ⁅a, b⁆ = ⁅a, b⁆ * g) :
    (b * a ^ k) ^ n = ⁅a, b⁆ ^ (k * (n * (n - 1) / 2)) * b ^ n * a ^ (k * n) := by
  induction' n with n ih <;> simp_all +decide [ pow_succ, mul_assoc ];
  have h_comm : a ^ (k * n) * b = ⁅a, b⁆ ^ (k * n) * b * a ^ (k * n) := by
    convert comm_rearrange_one a b ( k * n ) hz using 1;
  simp_all +decide [ ← mul_assoc, Nat.succ_mul, Nat.add_mul_div_left ];
  rw [ show ( n * n + n ) / 2 = n * ( n - 1 ) / 2 + n by
        cases n <;> simp +decide [ Nat.mul_succ, Nat.add_mul_div_left ] ; ring;
        omega ] ; simp +decide [ pow_add, mul_assoc ] ;
  simp +decide [ ← mul_assoc, ← pow_add, mul_add, add_mul, h_comm ];
  simp +decide [ pow_add, mul_assoc, hz ];
  exact Nat.recOn ( k * n ) ( by simp +decide ) fun n ihn => by rw [ pow_succ', ← mul_assoc, hz, mul_assoc, ihn, ← mul_assoc ] ;

/-
For odd p with ⁅a,b⁆ of order p: (b * a^k)^p = b^p * a^(k*p).
    This follows from the general formula since p divides p*(p-1)/2
    when p is odd, making the commutator term vanish.
-/
lemma pow_p_mul_odd (a b : G) (k : ℕ) (hp_odd : p ≠ 2)
    (hz : ∀ g : G, g * ⁅a, b⁆ = ⁅a, b⁆ * g)
    (hord_comm : orderOf ⁅a, b⁆ = p) :
    (b * a ^ k) ^ p = b ^ p * a ^ (k * p) := by
  convert pow_mul_central_comm a b k p hz using 1;
  -- Since $p$ is odd, $k * (p * (p - 1) / 2)$ is divisible by $p$.
  have h_div : p ∣ k * (p * (p - 1) / 2) := by
    exact dvd_mul_of_dvd_right ( Nat.dvd_div_of_mul_dvd ( by exact ⟨ ( p - 1 ) / 2, by nlinarith [ Nat.div_mul_cancel ( show 2 ∣ p - 1 from even_iff_two_dvd.mp ( hp.1.even_sub_one hp_odd ) ) ] ⟩ ) ) _;
  obtain ⟨ m, hm ⟩ := h_div; simp +decide [ hm, pow_mul, hord_comm.symm ] ;
  simp +decide [ ← pow_mul, hord_comm, hm ];
  rw [ pow_mul, ← hord_comm, pow_orderOf_eq_one, one_pow ]

end CommutatorFormula

section Substitution

/-
b^p ∈ ⟨a⟩ when orderOf a = p² and |G| = p³.
    Since ⟨a⟩ has index p, the quotient G/⟨a⟩ has order p,
    so every element's p-th power maps to 1 in the quotient.
-/
lemma bp_mem_zpowers (a b : G) (ha : orderOf a = p ^ 2) (hcard : Nat.card G = p ^ 3) :
    b ^ p ∈ Subgroup.zpowers a := by
  have h_index : (Subgroup.zpowers a).index = p := by
    convert zpowers_index_eq_p a ha hcard;
  have h_quotient : ∀ (H : Subgroup G) [H.Normal], H.index = p → ∀ g : G, g ^ p ∈ H := by
    intro H hH h_index g
    have h_quotient : ∀ (g : G ⧸ H), g ^ p = 1 := by
      have h_quotient : Nat.card (G ⧸ H) = p := by
        convert h_index using 1;
      exact fun g => by rw [ ← h_quotient, ← orderOf_dvd_iff_pow_eq_one ] ; exact orderOf_dvd_natCard g;
    simpa [ ← QuotientGroup.eq_one_iff ] using h_quotient ( QuotientGroup.mk g );
  convert h_quotient ( Subgroup.zpowers a ) _ b;
  · convert zpowers_normal_of_order_p_sq a ha hcard;
  · exact h_index

/-
There exists m < p such that b^p = a^(m*p), when both a and b have order p²,
    don't commute, and |G| = p³.

    Since b^p ∈ ⟨a⟩ and orderOf(b^p) = p, and ⟨a⟩ is cyclic of order p²,
    b^p must lie in the unique subgroup of order p in ⟨a⟩, which is ⟨a^p⟩.
    So b^p = (a^p)^m = a^(m*p) for some m.
-/
lemma exists_bp_eq_amp (a b : G) (ha : orderOf a = p ^ 2) (hb : orderOf b = p ^ 2)
    (hab : a * b ≠ b * a) (hcard : Nat.card G = p ^ 3) :
    ∃ m : ℕ, m < p ∧ b ^ p = a ^ (m * p) := by
  obtain ⟨m, hm⟩ : ∃ m : ℕ, b ^ p = a ^ m ∧ m < p ^ 2 := by
    have h_order : b ^ p ∈ Subgroup.zpowers a := by
      exact?;
    obtain ⟨ m, hm ⟩ := h_order;
    refine' ⟨ Int.toNat ( m % ( p ^ 2 ) ), _, _ ⟩ <;> simp_all +decide [ ← zpow_natCast, Int.emod_nonneg, Int.emod_lt_of_pos ];
    · rw [ max_eq_left ( Int.emod_nonneg _ ( by norm_cast; exact pow_ne_zero 2 hp.1.ne_zero ) ) ] ; rw [ ← hm ] ; rw [ ← zpow_mod_orderOf ] ; simp +decide [ ha ] ;
    · linarith [ Int.emod_lt_of_pos m ( by nlinarith [ hp.1.pos ] : 0 < ( p : ℤ ) ^ 2 ), Int.toNat_of_nonneg ( Int.emod_nonneg m ( by nlinarith [ hp.1.pos ] : ( p : ℤ ) ^ 2 ≠ 0 ) ) ];
  have h_order : orderOf (a ^ m) = p := by
    rw [ ← hm.1, orderOf_pow' ] <;> simp_all +decide [ hp.1.ne_zero, pow_succ' ];
  rw [ orderOf_pow' ] at h_order <;> simp_all +decide [ Nat.pow_succ' ];
  · -- From the equation p * p / gcd(p * p, m) = p, we can deduce that gcd(p * p, m) = p.
    have h_gcd : Nat.gcd (p * p) m = p := by
      nlinarith [ Nat.div_mul_cancel ( Nat.gcd_dvd_left ( p * p ) m ), Nat.div_mul_cancel ( Nat.gcd_dvd_right ( p * p ) m ), hp.1.two_le ];
    exact ⟨ m / p, Nat.div_lt_of_lt_mul <| by linarith, by rw [ Nat.div_mul_cancel <| show p ∣ m from h_gcd ▸ Nat.gcd_dvd_right _ _ ] ⟩;
  · aesop

end Substitution

section MainTheorem

/-
Case C (odd prime): Both generators have order p² → C_{p²} ⋊ C_p.

    We substitute b' = b * a^(p²-m) where b^p = a^(m*p), and show:
    - b'^p = b^p * a^((p²-m)*p) = a^(mp) * a^(p³-mp) = a^(p³) = 1
    - orderOf b' = p (since b'^p = 1, b' ≠ 1)
    - a * b' ≠ b' * a (since a * b ≠ b * a)
    Then apply Case B2.
-/
theorem case_C_odd_isom (hp_odd : p ≠ 2)
    (a b : G) (ha : orderOf a = p ^ 2) (hb : orderOf b = p ^ 2)
    (hab : a * b ≠ b * a) (hcard : Nat.card G = p ^ 3) :
    Nonempty (G ≃* CyclicGroup (p ^ 2) ⋊[cpSqAction p] CyclicGroup p) := by
  obtain ⟨m, hm₁, hm₂⟩ : ∃ m : ℕ, m < p ∧ b ^ p = a ^ (m * p) := by
    exact?;
  obtain ⟨b', hb'⟩ : ∃ b' : G, b' ^ p = 1 ∧ a * b' ≠ b' * a ∧ orderOf b' = p := by
    refine' ⟨ b * a ^ ( p ^ 2 - m ), _, _, _ ⟩;
    · rw [ pow_p_mul_odd ];
      · rw [ hm₂, ← pow_add, ← add_mul, Nat.add_sub_of_le ( by nlinarith ) ];
        rw [ ← orderOf_dvd_iff_pow_eq_one ] ; simp +decide [ ha ];
      · exact hp_odd;
      · exact fun g => commutator_central p a b g hcard ⟨ a, b, hab ⟩;
      · exact commutator_order p a b hcard ⟨ a, b, hab ⟩ hab;
    · by_contra h_contra
      have h_comm : a * b = b * a := by
        have h_comm : a * b * a ^ (p ^ 2 - m) = b * a ^ (p ^ 2 - m) * a := by
          rw [ ← h_contra, mul_assoc ];
        have h_comm : a * b * a ^ (p ^ 2 - m) * a⁻¹ ^ (p ^ 2 - m) = b * a ^ (p ^ 2 - m) * a * a⁻¹ ^ (p ^ 2 - m) := by
          rw [h_comm];
        convert h_comm using 1 <;> group
      contradiction;
    · have hb'_order : orderOf (b * a ^ (p ^ 2 - m)) ∣ p := by
        have hb'_order : (b * a ^ (p ^ 2 - m)) ^ p = 1 := by
          convert pow_p_mul_odd a b ( p ^ 2 - m ) hp_odd _ _ using 1;
          · simp +decide [ hm₂, pow_mul', ha.symm ];
            rw [ ← pow_add, add_tsub_cancel_of_le ( show m ≤ orderOf a from by nlinarith ) ];
            rw [ ← pow_mul, mul_comm, pow_mul, pow_orderOf_eq_one, one_pow ];
          · exact fun g => commutator_central p a b g hcard ⟨ a, b, hab ⟩;
          · apply commutator_order p a b hcard ⟨a, b, hab⟩ hab;
        exact orderOf_dvd_iff_pow_eq_one.mpr hb'_order;
      rw [ Nat.dvd_prime hp.1 ] at hb'_order;
      cases' hb'_order with h h <;> simp_all +decide [ pow_succ', mul_assoc ];
      simp_all +decide [ mul_eq_one_iff_eq_inv ];
      exact False.elim ( hab ( by group ) );
  apply case_B2_odd_isom hp_odd a b' ha hb'.2.2 hb'.2.1 hcard

end MainTheorem
