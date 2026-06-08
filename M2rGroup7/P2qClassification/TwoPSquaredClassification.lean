import Mathlib
import «M2rGroup7».Lemmas.SylowUtils
import «M2rGroup7».Lemmas.LinearAlgebraUtils
import «M2rGroup7».Lemmas.GroupTheoryLemmas
import «M2rGroup7».Lemmas.ClassificationUtils
import «M2rGroup7».Lemmas.HomomorphismUtils
import «M2rGroup7».Lemmas.NumberTheoryUtils
import «M2rGroup7».P2qClassification.CycPGroupClassification

/-- Canonical nontrivial action `C_2 →* Aut(C_{p^2})`, image of order 2. -/
def canonicalC2OnCp2Action {p : ℕ} [h_p_prime : Fact p.Prime] (h_p_ne_2 : p ≠ 2) :
    CyclicGroup 2 →* MulAut (CyclicGroup (p ^ 2)) :=
  haveI := h_p_prime
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  haveI : NeZero (p ^ 2) := ⟨pow_ne_zero 2 h_p_prime.out.ne_zero⟩
  haveI : NeZero (2 : ℕ) := ⟨by norm_num⟩
  haveI : NeZero ((2:ℕ) ^ 1) := ⟨pow_ne_zero 1 (by norm_num)⟩
  transportCpCqHom (pow_one 2) (rfl : p ^ 2 = p ^ 2)
    (canonicalAction 2 p 2 1 (Ne.symm h_p_ne_2) h_p_ne_2 (by norm_num)
       1 (by
          have h := (Nat.le_min.mp (one_le_min_two_factorization_two h_p_ne_2)).2
          exact Nat.le_min.mpr ⟨le_refl 1, h⟩))

theorem classification_2p2 {p : ℕ} [h_p_prime : Fact p.Prime] [Group G]
    (h_ge_3 : p ≥ 3) (h : Nat.card G = p ^ 2 * 2)
    : Nonempty (G ≃* CyclicGroup (2 * p ^ 2))
      ∨ Nonempty (G ≃* CyclicGroup p × CyclicGroup p × CyclicGroup 2)
      ∨ Nonempty (G ≃* SemidirectProduct (CyclicGroup (p ^ 2)) (CyclicGroup 2) (canonicalC2OnCp2Action (by omega)))
 := by
  haveI : Finite G := by
    apply Nat.finite_of_card_ne_zero; rw [h]
    have p_ne : p ≠ 0 := Nat.Prime.ne_zero h_p_prime.elim
    simp; tauto
  let n_p := Nat.card (Sylow p G)
  let n_2 := Nat.card (Sylow 2 G)

  have n_p_or_n_2_one : n_p = 1 ∨ n_2 = 1 := p2q_group_has_normal_sylow_subgroup G (by omega) h
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  rcases n_p_or_n_2_one with h_np_1 | h_n2_1
  · -- n_p = 1: Sylow p-subgroup P (order p ^ 2) is normal, complement K has order 2
    let P : Sylow p G := default
    haveI : Subsingleton (Sylow p G) := (Nat.card_eq_one_iff_unique.mp h_np_1).1
    have h_card_form : Nat.card G = p ^ 2 * 2 ^ 1 := by aesop
    have h_p_p2 : Nat.card ↥(P : Subgroup G) = p ^ 2 := sylow_card_eq (by aesop) h_card_form P
    have h_p_idx_q : ∀ P : Sylow p G, (↑P : Subgroup G).index = 2 := fun P => by
      simpa using sylow_index_eq (by aesop) h_card_form P
    obtain ⟨K, hK⟩ := Subgroup.exists_right_complement'_of_coprime (N := (↑P : Subgroup G)) (by
      rw [h_p_p2, h_p_idx_q]
      exact (Nat.coprime_pow_left_iff (by norm_num) p 2).mpr
        (h_p_prime.out.coprime_of_ne Nat.prime_two (by omega)))
    have h_iso_g_p_k := SemidirectProduct.mulEquivSubgroup hK
    let φ : ↥K →* MulAut ↥(↑P : Subgroup G) :=
      (↑P : Subgroup G).normalizerMonoidHom.comp
        (Subgroup.inclusion (by simp [Subgroup.normalizer_eq_top]))
    have hK_card : Nat.card ↥K = 2 := by
      have h1 : Nat.card G = Nat.card ↥(↑P : Subgroup G) * Nat.card ↥K := by
        have heq := Nat.card_congr h_iso_g_p_k.toEquiv
        rw [SemidirectProduct.card] at heq; exact heq.symm
      rw [h_p_p2, h] at h1; aesop
    have eK : ↥K ≃* CyclicGroup 2 := Classical.choice (prime_classification_of_group (n := 2) hK_card)
    rcases (p_squared_classification (p := p) h_p_p2) with h_c_p2 | h_cp_cp
    · -- P ≅ C_(p ^ 2): Aut(P) ≅ C_p(p-1)
      sorry
    · -- P ≅ C_p × C_p: Aut(P) ≅ GL_2(p)
      have : Nonempty (MulAut (CyclicGroup p × CyclicGroup p) ≃* GL (Fin 2) (ZMod p)) := aut_of_CpCp p
      sorry
  · sorry
