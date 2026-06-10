import Mathlib
import «M2rGroup7».Lemmas.NumberTheoryUtils

variable (G : Type*) [Group G]

/-- In a finite group of order p^a * q^b (p, q distinct primes),
    every Sylow p-subgroup has order p^a. -/
lemma sylow_card_eq {p q : ℕ} {a b : ℕ}
    [hp : Fact p.Prime] [hq : Fact q.Prime] (hpq : p ≠ q)
    {G : Type*} [Group G] [Finite G]
    (h : Nat.card G = p ^ a * q ^ b) (P : Sylow p G) :
    Nat.card ↥(P : Subgroup G) = p ^ a := by
  rw [Sylow.card_eq_multiplicity, h]
  have hcop : Nat.Coprime (p ^ a) (q ^ b) :=
    ((hp.out.coprime_of_ne hq.out hpq).pow_left a).pow_right b
  rw [Nat.factorization_mul_of_coprime hcop, Finsupp.add_apply,
      Nat.factorization_pow_self hp.out]
  have hqb : (q ^ b).factorization p = 0 := by
    rw [Nat.factorization_pow, Finsupp.smul_apply, hq.out.factorization,
        Finsupp.single_apply, if_neg (Ne.symm hpq)]
    simp
  rw [hqb, add_zero]

/-- In a finite group of order p^a * q^b (p, q distinct primes),
    every Sylow p-subgroup has index q^b. -/
lemma sylow_index_eq {p q : ℕ} {a b : ℕ}
    [hp : Fact p.Prime] [hq : Fact q.Prime] (hpq : p ≠ q)
    {G : Type*} [Group G] [Finite G]
    (h : Nat.card G = p ^ a * q ^ b) (P : Sylow p G) :
    (P : Subgroup G).index = q ^ b := by
  have hcard := Subgroup.index_mul_card (P : Subgroup G)
  rw [sylow_card_eq hpq h P, h] at hcard
  exact Nat.eq_of_mul_eq_mul_right (pow_pos hp.out.pos a) (hcard.trans (mul_comm _ _))

/-- Two distinct Sylow p-subgroups, each of prime order p, intersect trivially. -/
lemma sylow_prime_order_disjoint {p : ℕ} [hp : Fact p.Prime]
    {G : Type*} [Group G] [Finite G]
    (h_sylow_card : ∀ P : Sylow p G, Nat.card ↥(P : Subgroup G) = p)
    {P₁ P₂ : Sylow p G} (hne : P₁ ≠ P₂) :
    Disjoint (P₁ : Subgroup G) P₂ := by
  rw [disjoint_iff]
  have hdvd : Nat.card ↥((P₁ : Subgroup G) ⊓ P₂) ∣ p :=
    calc Nat.card ↥((P₁ : Subgroup G) ⊓ P₂)
        ∣ Nat.card ↥(P₁ : Subgroup G) := Subgroup.card_dvd_of_le inf_le_left
      _ = p := h_sylow_card P₁
  rcases hp.out.eq_one_or_self_of_dvd _ hdvd with h1 | heqp
  · exact Subgroup.card_eq_one.mp h1
  · exfalso; apply hne; apply Sylow.ext
    have hce1 : Nat.card ↥((P₁ : Subgroup G) ⊓ P₂) = Nat.card ↥(P₁ : Subgroup G) :=
      heqp.trans (h_sylow_card P₁).symm
    have hce2 : Nat.card ↥((P₁ : Subgroup G) ⊓ P₂) = Nat.card ↥(P₂ : Subgroup G) :=
      heqp.trans (h_sylow_card P₂).symm
    have h_sgOf_card : ∀ (H K : Subgroup G), H ≤ K →
        Nat.card ↥(H.subgroupOf K) = Nat.card ↥H := fun H K hle => by
      calc Nat.card ↥(H.subgroupOf K)
          = Nat.card ↥((H.subgroupOf K).map K.subtype) :=
              (Subgroup.card_map_of_injective Subtype.coe_injective).symm
        _ = Nat.card ↥H := by rw [Subgroup.map_subgroupOf_eq_of_le hle]
    have map_top_subtype : ∀ K : Subgroup G,
        Subgroup.map K.subtype (⊤ : Subgroup ↥K) = K := fun K => by
      ext x; simp only [Subgroup.mem_map, Subgroup.mem_top, true_and]
      exact ⟨fun ⟨y, hy⟩ => hy ▸ y.prop, fun hx => ⟨⟨x, hx⟩, rfl⟩⟩
    have heq1 : (P₁ : Subgroup G) ⊓ P₂ = P₁ := by
      haveI : Finite ↥((P₁ ⊓ P₂ : Subgroup G).subgroupOf P₁) := inferInstance
      have htop := (Subgroup.card_eq_iff_eq_top _).mp
        ((h_sgOf_card _ P₁ inf_le_left).trans hce1)
      have hmb := Subgroup.map_subgroupOf_eq_of_le (inf_le_left (a := (P₁ : Subgroup G)) (b := P₂))
      rw [htop] at hmb; exact (map_top_subtype P₁ ▸ hmb).symm
    have heq2 : (P₁ : Subgroup G) ⊓ P₂ = P₂ := by
      haveI : Finite ↥((P₁ ⊓ P₂ : Subgroup G).subgroupOf P₂) := inferInstance
      have htop := (Subgroup.card_eq_iff_eq_top _).mp
        ((h_sgOf_card _ P₂ inf_le_right).trans hce2)
      have hmb := Subgroup.map_subgroupOf_eq_of_le (inf_le_right (a := (P₁ : Subgroup G)) (b := P₂))
      rw [htop] at hmb; exact (map_top_subtype P₂ ▸ hmb).symm
    exact heq1.symm.trans heq2

/-- The union of all Sylow p-subgroups, when each has prime order p, has
    cardinality 1 + n_p * (p - 1) where n_p = Nat.card (Sylow p G). -/
lemma sylow_prime_union_card {p : ℕ} [hp : Fact p.Prime]
    {G : Type*} [Group G] [Finite G]
    (h_sylow_card : ∀ P : Sylow p G, Nat.card ↥(P : Subgroup G) = p) :
    Nat.card (⋃ P : Sylow p G, (P : Subgroup G) : Set G) =
      1 + Nat.card (Sylow p G) * (p - 1) := by
  haveI hFinG : Fintype G := Fintype.ofFinite G
  haveI hDecEq : DecidableEq G := Classical.decEq G
  let toFset : Sylow p G → Finset G := fun P =>
    letI : Fintype ↥(P : Subgroup G) := Fintype.ofFinite _
    ((P : Subgroup G) : Set G).toFinset
  have mem_toFset : ∀ (P : Sylow p G) (x : G), x ∈ toFset P ↔ x ∈ (P : Subgroup G) := fun P x => by
    letI : Fintype ↥(P : Subgroup G) := Fintype.ofFinite _
    simp [toFset, Set.mem_toFinset, SetLike.mem_coe]
  have toFset_card : ∀ P : Sylow p G, (toFset P).card = p := fun P => by
    letI : Fintype ↥(P : Subgroup G) := Fintype.ofFinite _
    have : (toFset P).card = Nat.card ↥(P : Subgroup G) := by simp [toFset, Set.toFinset_card]
    rw [this, h_sylow_card]
  have hbU_set : (Finset.univ.biUnion toFset : Set G) =
      ⋃ P : Sylow p G, (P : Subgroup G) := by
    ext x; simp [mem_toFset, Set.mem_iUnion, SetLike.mem_coe]
  have h_ne_pdisj : Set.PairwiseDisjoint ↑(Finset.univ : Finset (Sylow p G))
      (fun P => toFset P \ {(1 : G)}) := by
    intro P₁ _ P₂ _ hne
    simp only [Function.onFun, Finset.disjoint_left]
    rintro x hx1 hx2
    simp only [Finset.mem_sdiff, mem_toFset, Finset.mem_singleton] at hx1 hx2
    exact hx1.2 (Subgroup.mem_bot.mp ((disjoint_iff.mp
      (sylow_prime_order_disjoint h_sylow_card hne)) ▸
      Subgroup.mem_inf.mpr ⟨hx1.1, hx2.1⟩))
  have h_ne_card : (Finset.univ.biUnion (fun P => toFset P \ {(1 : G)})).card =
      Nat.card (Sylow p G) * (p - 1) := by
    rw [Finset.card_biUnion h_ne_pdisj]
    have h_each : ∀ P : Sylow p G, (toFset P \ {(1 : G)}).card = p - 1 := fun P => by
      have hmem : (1 : G) ∈ toFset P := (mem_toFset _ _).mpr (P : Subgroup G).one_mem
      rw [Finset.card_sdiff, Finset.inter_comm, Finset.inter_singleton_of_mem hmem,
          Finset.card_singleton, toFset_card]
    simp only [h_each, Finset.sum_const, Finset.card_univ, smul_eq_mul, ← Nat.card_eq_fintype_card]
  have hU_split : Finset.univ.biUnion toFset =
      {(1 : G)} ∪ Finset.univ.biUnion (fun P => toFset P \ {(1 : G)}) := by
    ext x
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_union,
                Finset.mem_singleton, Finset.mem_sdiff, mem_toFset]
    constructor
    · rintro ⟨P, hxP⟩
      rcases eq_or_ne x 1 with rfl | hx1
      · left; rfl
      · right; exact ⟨P, hxP, hx1⟩
    · rintro (rfl | ⟨P, hxP, _⟩)
      · obtain ⟨P⟩ : Nonempty (Sylow p G) := inferInstance
        exact ⟨P, (P : Subgroup G).one_mem⟩
      · exact ⟨P, hxP⟩
  have hU_disj : Disjoint {(1 : G)} (Finset.univ.biUnion (fun P => toFset P \ {(1 : G)})) := by
    simp only [Finset.disjoint_left, Finset.mem_singleton, Finset.mem_biUnion, Finset.mem_univ,
                true_and, Finset.mem_sdiff, mem_toFset]
    rintro _ rfl ⟨_, _, h1⟩; exact h1 rfl
  have hFcard : (Finset.univ.biUnion toFset).card = 1 + Nat.card (Sylow p G) * (p - 1) := by
    rw [hU_split, Finset.card_union_of_disjoint hU_disj, Finset.card_singleton, h_ne_card]
  rw [show (⋃ P : Sylow p G, (P : Subgroup G) : Set G) =
      ↑(Finset.univ.biUnion toFset) from hbU_set.symm]
  exact (Nat.card_eq_finsetCard _).trans hFcard

/-- When each Sylow p-subgroup has prime order p, the number of elements of order p
    in G is n_p * (p - 1). -/
lemma sylow_elements_order_p_card {p : ℕ} [hp : Fact p.Prime]
    {G : Type*} [Group G] [Finite G]
    (h_sylow_card : ∀ P : Sylow p G, Nat.card ↥(P : Subgroup G) = p) :
    Nat.card {x : G | orderOf x = p} = Nat.card (Sylow p G) * (p - 1) := by
  have hset_eq : ({x : G | orderOf x = p} : Set G) =
      (⋃ P : Sylow p G, (P : Subgroup G) : Set G) \ {(1 : G)} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_diff, Set.mem_iUnion, SetLike.mem_coe,
                Set.mem_singleton_iff]
    constructor
    · intro hox
      constructor
      · have hzp : IsPGroup p ↥(Subgroup.zpowers x) :=
          IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hox, pow_one])
        obtain ⟨Q, hQ⟩ := IsPGroup.exists_le_sylow hzp
        exact ⟨Q, hQ (Subgroup.mem_zpowers x)⟩
      · intro h1; rw [h1, orderOf_one] at hox; linarith [hp.out.one_lt]
    · rintro ⟨⟨P, hxP⟩, hx1⟩
      have hdvd : orderOf x ∣ p :=
        (h_sylow_card P) ▸ Subgroup.orderOf_dvd_natCard (P : Subgroup G) hxP
      rcases hp.out.eq_one_or_self_of_dvd _ hdvd with h1' | hpeq
      · exact absurd (orderOf_eq_one_iff.mp h1') hx1
      · exact hpeq
  have h1_mem : (1 : G) ∈ (⋃ P : Sylow p G, (P : Subgroup G) : Set G) := by
    simp only [Set.mem_iUnion, SetLike.mem_coe]
    obtain ⟨P⟩ : Nonempty (Sylow p G) := inferInstance
    exact ⟨P, (P : Subgroup G).one_mem⟩
  have hcard_eq : Nat.card {x : G | orderOf x = p} =
      Nat.card (⋃ P : Sylow p G, (P : Subgroup G) : Set G) - 1 :=
    (Nat.card_congr (Equiv.setCongr hset_eq)).trans
      (Set.ncard_diff_singleton_of_mem h1_mem)
  rw [hcard_eq, sylow_prime_union_card h_sylow_card]
  omega

/-- Every group G of order p^2 q has either a normal Sylow p-group or normal Sylow q-group -/
lemma p2q_group_has_normal_sylow_subgroup {p : ℕ} {q : ℕ}
    [h_p_prime : Fact p.Prime] [h_q_prime : Fact q.Prime]
    (h_p_ne_q : p ≠ q) (h : Nat.card G = p ^ 2 * q)
    : Nat.card (Sylow p G) = 1 ∨ Nat.card (Sylow q G) = 1 := by
  let n_p := Nat.card (Sylow p G)
  let n_q := Nat.card (Sylow q G)
  -- G is finite
  haveI : Finite G := by
    apply Nat.finite_of_card_ne_zero
    rw [h]
    have p_ne : p ≠ 0 := Nat.Prime.ne_zero h_p_prime.elim
    have q_ne : q ≠ 0 := Nat.Prime.ne_zero h_q_prime.elim
    simp; tauto
  let P : Sylow p G := default
  -- Order of Sylow p-group is p^2
  have h_p_p2 : Nat.card ↥(P : Subgroup G) = p ^ 2 :=
    sylow_card_eq h_p_ne_q (show Nat.card G = p ^ 2 * q ^ 1 by aesop) P
  -- Index of Sylow p-group is q
  have h_p_idx_q : (↑P : Subgroup G).index = q := by
    simpa using sylow_index_eq h_p_ne_q (show Nat.card G = p ^ 2 * q ^ 1 by aesop) P
  -- n_p divides q
  have h_n_p_div_q : n_p ∣ q := by
    have h_sylow_dvd_p_index := Sylow.card_dvd_index P
    rw [h_p_idx_q] at h_sylow_dvd_p_index
    exact h_sylow_dvd_p_index
  -- n_p is 1 (mod p)
  have h_n_p_one_mod_p : n_p ≡ 1 [MOD p] := by
    change Nat.card (Sylow p G) ≡ 1 [MOD p]
    exact card_sylow_modEq_one p G
  -- Claim 1: n_p = 1 or n_q = 1
  have n_p_or_n_q_one : n_p = 1 ∨ n_q = 1 := by
    rcases lt_trichotomy p q with h_lt | h_eq | h_gt
    · -- case h_lt : p < q
      -- Step 1: n_q can be either 1, p, p^2
      let Q : Sylow q G := default
      -- Order of Sylow q-group is q
      have h_q_q : Nat.card ↥(Q : Subgroup G) = q := by
        have := sylow_card_eq (Ne.symm h_p_ne_q)
          (show Nat.card G = q ^ 1 * p ^ 2 by rw [pow_one, h]; ring) Q
        simpa using this
      -- Index of Sylow q-group is p^2
      have h_q_idx_p2 : (↑Q : Subgroup G).index = p ^ 2 := by
        simpa using sylow_index_eq (Ne.symm h_p_ne_q)
          (show Nat.card G = q ^ 1 * p ^ 2 by rw [pow_one, h]; ring) Q
      -- n_q divides p^2
      have h_n_p_div_q : n_q ∣ p^2 := by
        have h_sylow_dvd_p_index := Sylow.card_dvd_index Q
        rw [h_q_idx_p2] at h_sylow_dvd_p_index
        exact h_sylow_dvd_p_index
      -- n_q is 1, p, or p^2
      have h_n_q_cases : n_q = 1 ∨ n_q = p ∨ n_q = p^2 := by
        obtain ⟨k, hk, hkn⟩ := (Nat.dvd_prime_pow h_p_prime.out).mp h_n_p_div_q
        interval_cases k
        · left;  simpa using hkn
        · right; left;  simpa using hkn
        · right; right; simpa using hkn
      -- Step 2: n_q ≠ p as then q | p−1 contradicting p < q
      -- n_q is 1 (mod q)
      have h_n_p_one_mod_p : n_q ≡ 1 [MOD q] := by
        change Nat.card (Sylow q G) ≡ 1 [MOD q]
        exact card_sylow_modEq_one q G
      -- n_q ≠ p
      have h_n_q_neq_p : n_q ≠ p := by
        intro n_q_eq_p
        rw [n_q_eq_p] at h_n_p_one_mod_p
        unfold Nat.ModEq at h_n_p_one_mod_p
        rw [Nat.mod_eq_of_lt h_lt, Nat.mod_eq_of_lt h_q_prime.out.one_lt] at h_n_p_one_mod_p
        linarith [h_p_prime.out.one_lt]
      -- Step 3: If n_q ≠ 1, then n_q = p^2
      rcases h_n_q_cases with h_nq1 | h_nqp | h_nqp2
      · -- n_q = 1, done
        right; exact h_nq1
      · -- n_q = p, impossible
        exact absurd h_nqp h_n_q_neq_p
      · -- n_q = p^2
        -- Step 4: p^2 Sylow q-subgroups are trivially intersecting, hence contribute
        --         p²(q−1) elements of order q
        -- Step 5: Remaining p² elements form one Sylow p-subgroup, so n_p = 1
        -- =========================================================
        -- BEGIN PROOF OF STEPS 4 & 5 (counting argument, n_p = 1)
        -- =========================================================
        left
        haveI hFinG : Fintype G := Fintype.ofFinite G
        haveI hDecEq : DecidableEq G := Classical.decEq G
        -- Helper: build a Finset G from a Subgroup G
        let toFset : ∀ H : Subgroup G, Finset G := fun H =>
          letI : Fintype ↥H := Fintype.ofFinite _
          (H : Set G).toFinset
        have mem_toFset : ∀ (H : Subgroup G) (x : G), x ∈ toFset H ↔ x ∈ H := fun H x => by
          letI : Fintype ↥H := Fintype.ofFinite _
          change x ∈ (H : Set G).toFinset ↔ x ∈ H
          simp [Set.mem_toFinset, SetLike.mem_coe]
        have toFset_card : ∀ H : Subgroup G, (toFset H).card = Nat.card ↥H := fun H => by
          letI : Fintype ↥H := Fintype.ofFinite _
          aesop
        -- All Sylow q-subgroups have order q
        have h_sylow_q_card : ∀ Q' : Sylow q G, Nat.card ↥(Q' : Subgroup G) = q := fun Q' => by
          have := sylow_card_eq (Ne.symm h_p_ne_q)
            (show Nat.card G = q ^ 1 * p ^ 2 by rw [pow_one, h]; ring) Q'
          simpa using this
        -- Any Sylow p-subgroup has order p^2
        have h_p_p2_gen : ∀ P' : Sylow p G, Nat.card ↥(P' : Subgroup G) = p ^ 2 := fun P' =>
          sylow_card_eq h_p_ne_q (show Nat.card G = p ^ 2 * q ^ 1 by aesop) P'
        -- A Sylow p-subgroup and a Sylow q-subgroup always intersect trivially (different primes)
        have h_PQdisj : ∀ (P' : Sylow p G) (Q' : Sylow q G), Disjoint (P' : Subgroup G) Q' :=
          fun P' Q' => IsPGroup.disjoint_of_ne p q h_p_ne_q _ _ P'.isPGroup' Q'.isPGroup'
        -- Non-identity elements of any Sylow p-subgroup are absent from every Sylow q-subgroup
        have h_P_avoid_Q : ∀ (P' : Sylow p G) x, x ∈ (P' : Subgroup G) → x ≠ 1 →
            ∀ Q' : Sylow q G, x ∉ (Q' : Subgroup G) := fun P' x hxP hx1 Q' hxQ =>
          hx1 (Subgroup.mem_bot.mp ((disjoint_iff.mp (h_PQdisj P' Q'))
            ▸ Subgroup.mem_inf.mpr ⟨hxP, hxQ⟩))
        -- U = union of all Sylow q-subgroups (as a Finset)
        let U : Finset G := Finset.univ.biUnion (fun Q' : Sylow q G => toFset Q')
        -- |U| = 1 + n_q * (q - 1) via sylow_prime_union_card
        have hUcard : U.card = 1 + n_q * (q - 1) := by
          have hset : (↑U : Set G) = ⋃ Q' : Sylow q G, (Q' : Subgroup G) := by
            ext x; simp [U, mem_toFset, Set.mem_iUnion, SetLike.mem_coe]
          calc U.card
              = Nat.card ↥U := (Nat.card_eq_finsetCard U).symm
            _ = Nat.card (⋃ Q' : Sylow q G, (Q' : Subgroup G) : Set G) :=
                Nat.card_congr (Equiv.setCongr hset)
            _ = 1 + n_q * (q - 1) := sylow_prime_union_card h_sylow_q_card
        -- |univ \ U| = p^2 - 1  (the "remaining" elements)
        have hTcard : (Finset.univ \ U).card = p ^ 2 - 1 := by
          have hsum : (Finset.univ \ U).card + U.card = Fintype.card G := by
            have h1 := @Finset.card_sdiff_add_card_inter G _ Finset.univ U
            simp only [Finset.univ_inter] at h1
            linarith [Finset.card_univ (α := G)]
          have hU' : U.card = 1 + p ^ 2 * (q - 1) := h_nqp2 ▸ hUcard
          rw [← Nat.card_eq_fintype_card, h, hU'] at hsum
          have hp1 : 1 ≤ p ^ 2 := Nat.one_le_pow _ _ h_p_prime.out.pos
          rcases q with _ | k
          · exact absurd h_q_prime.out.pos (by omega)
          · simp only [Nat.succ_sub_one] at hsum
            have hring : p ^ 2 * (k + 1) = p ^ 2 * k + p ^ 2 := by ring
            omega
        -- Non-identity elements of any Sylow p-subgroup lie outside U
        have hPin_T : ∀ P' : Sylow p G, toFset P' \ {(1 : G)} ⊆ Finset.univ \ U := fun P' x => by
          simp only [Finset.mem_sdiff, mem_toFset, Finset.mem_singleton, Finset.mem_univ,
                      true_and, U, Finset.mem_biUnion]
          rintro ⟨hxP, hx1⟩ ⟨Q', hxQ⟩
          exact h_P_avoid_Q P' x hxP hx1 Q' hxQ
        -- Each Sylow p-subgroup contributes exactly p^2 - 1 non-identity elements
        have hPcard : ∀ P' : Sylow p G, (toFset P' \ {(1 : G)}).card = p ^ 2 - 1 := fun P' => by
          have hmem : (1 : G) ∈ toFset P' := (mem_toFset _ _).mpr (P' : Subgroup G).one_mem
          rw [Finset.card_sdiff, Finset.inter_comm, Finset.inter_singleton_of_mem hmem,
              Finset.card_singleton, toFset_card, h_p_p2_gen]
        -- The non-identity part of every Sylow p-subgroup equals univ \ U exactly
        have hPeqT : ∀ P' : Sylow p G, toFset P' \ {(1 : G)} = Finset.univ \ U :=
          fun P' => (Finset.subset_iff_eq_of_card_le
            (le_of_eq (hTcard.trans (hPcard P').symm))).mp (hPin_T P')
        -- Hence all Sylow p-subgroups coincide → Subsingleton → n_p = 1
        haveI hSubsing : Subsingleton (Sylow p G) := by
          refine ⟨fun P₁ P₂ => ?_⟩
          apply Sylow.ext; apply Subgroup.ext; intro x
          rcases eq_or_ne x 1 with rfl | hx1
          · simp
          · have h_neq : toFset P₁ \ {(1 : G)} = toFset P₂ \ {(1 : G)} :=
              (hPeqT P₁).trans (hPeqT P₂).symm
            have key := Finset.ext_iff.mp h_neq x
            simp only [Finset.mem_sdiff, mem_toFset, Finset.mem_singleton, hx1,
                        not_false_eq_true, and_true] at key
            exact key
        exact Nat.card_eq_one_iff_unique.mpr ⟨hSubsing, ⟨P⟩⟩
        -- =========================================================
        -- END PROOF OF STEPS 4 & 5
        -- =========================================================
    · -- case h_eq : p = q  (impossible since p ≠ q)
      trivial
    · -- case h_gt : q < p

      -- Step 1: Only divisor of q that's ≡ 1 (mod p) is 1. So n_p = 1.
      left
      rcases h_q_prime.out.eq_one_or_self_of_dvd n_p h_n_p_div_q with h | h
      · exact h
      · exfalso
        have hmod := h_n_p_one_mod_p
        rw [h] at hmod
        unfold Nat.ModEq at hmod
        rw [Nat.mod_eq_of_lt h_gt, Nat.mod_eq_of_lt h_p_prime.out.one_lt] at hmod
        linarith [h_q_prime.out.one_lt]
  tauto

/-- Every group `G` of order `p * q` for primes `p < q` has a unique (hence normal)
    Sylow `q`-subgroup. -/
lemma pq_group_has_normal_sylow_q_subgroup {p q : ℕ}
    [hp : Fact p.Prime] [hq : Fact q.Prime]
    (hlt : p < q) (h : Nat.card G = p * q) :
    Nat.card (Sylow q G) = 1 := by
  haveI : Finite G := by
    apply Nat.finite_of_card_ne_zero
    rw [h]
    exact Nat.mul_ne_zero hp.out.ne_zero hq.out.ne_zero
  have hpq : p ≠ q := Nat.ne_of_lt hlt
  let Q : Sylow q G := default
  have h_card_form : Nat.card G = q ^ 1 * p ^ 1 := by rw [pow_one, pow_one, h, mul_comm]
  have hQ_idx : (Q : Subgroup G).index = p := by
    simpa using sylow_index_eq (Ne.symm hpq) h_card_form Q
  have h_nq_dvd : Nat.card (Sylow q G) ∣ p := by
    have := Sylow.card_dvd_index Q
    rwa [hQ_idx] at this
  have h_nq_mod : Nat.card (Sylow q G) ≡ 1 [MOD q] := card_sylow_modEq_one q G
  rcases (Nat.dvd_prime hp.out).mp h_nq_dvd with h1 | hp_eq
  · exact h1
  · exfalso
    rw [hp_eq] at h_nq_mod
    unfold Nat.ModEq at h_nq_mod
    rw [Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt hq.out.one_lt] at h_nq_mod
    have := hp.out.one_lt
    omega

/-- Every group G of order pqr with p < q < r has either a normal Sylow q-group or normal Sylow r-group -/
lemma pqr_group_has_normal_sylow_qr_subgroup {p : ℕ} {q : ℕ} {r : ℕ}
    [h_p_prime : Fact p.Prime] [h_q_prime : Fact q.Prime] [h_r_prime : Fact r.Prime]
    (h_p_le_q : p < q) (h_q_le_r : q < r) (h : Nat.card G = p * q * r)
    : Nat.card (Sylow q G) = 1 ∨ Nat.card (Sylow r G) = 1 := by
  haveI hfin : Finite G := Nat.finite_of_card_ne_zero (h ▸
    Nat.mul_ne_zero (Nat.mul_ne_zero h_p_prime.out.ne_zero h_q_prime.out.ne_zero)
      h_r_prime.out.ne_zero)
  have h_p_ne_q : p ≠ q := Nat.ne_of_lt h_p_le_q
  have h_q_ne_r : q ≠ r := Nat.ne_of_lt h_q_le_r
  have h_p_ne_r : p ≠ r := Nat.ne_of_lt (Nat.lt_trans h_p_le_q h_q_le_r)
  have hp2 : 2 ≤ p := h_p_prime.out.two_le
  have hq2 : 2 ≤ q := h_q_prime.out.two_le
  have hr2 : 2 ≤ r := h_r_prime.out.two_le
  have hp_pos := h_p_prime.out.pos
  have hq_pos := h_q_prime.out.pos
  have hr_pos := h_r_prime.out.pos
  have h_p_lt_r : p < r := Nat.lt_trans h_p_le_q h_q_le_r
  -- Sylow card facts via factorization
  have hQ_card : ∀ Q : Sylow q G, Nat.card (Q : Subgroup G) = q := fun Q => by
    rw [Sylow.card_eq_multiplicity, h,
        Nat.factorization_mul (Nat.mul_ne_zero h_p_prime.out.ne_zero h_q_prime.out.ne_zero)
                               h_r_prime.out.ne_zero,
        Nat.factorization_mul h_p_prime.out.ne_zero h_q_prime.out.ne_zero,
        h_p_prime.out.factorization, h_q_prime.out.factorization, h_r_prime.out.factorization]
    simp [Finsupp.add_apply, h_p_ne_q, Ne.symm h_q_ne_r]
  have hR_card : ∀ R : Sylow r G, Nat.card (R : Subgroup G) = r := fun R => by
    rw [Sylow.card_eq_multiplicity, h,
        Nat.factorization_mul (Nat.mul_ne_zero h_p_prime.out.ne_zero h_q_prime.out.ne_zero)
                               h_r_prime.out.ne_zero,
        Nat.factorization_mul h_p_prime.out.ne_zero h_q_prime.out.ne_zero,
        h_p_prime.out.factorization, h_q_prime.out.factorization, h_r_prime.out.factorization]
    simp [Finsupp.add_apply, h_q_ne_r, h_p_ne_r]
  -- Indices
  have hQ_idx : ∀ Q : Sylow q G, (Q : Subgroup G).index = p * r := fun Q => by
    have hcard := Subgroup.index_mul_card (Q : Subgroup G)
    rw [hQ_card Q, h] at hcard
    exact Nat.eq_of_mul_eq_mul_right hq_pos (hcard.trans (by ring))
  have hR_idx : ∀ R : Sylow r G, (R : Subgroup G).index = p * q := fun R => by
    have hcard := Subgroup.index_mul_card (R : Subgroup G)
    rw [hR_card R, h] at hcard
    exact Nat.eq_of_mul_eq_mul_right hr_pos hcard
  obtain ⟨Q₀⟩ : Nonempty (Sylow q G) := inferInstance
  obtain ⟨R₀⟩ : Nonempty (Sylow r G) := inferInstance
  have h_n_r_div : Nat.card (Sylow r G) ∣ p * q := by
    have := Sylow.card_dvd_index R₀
    rwa [hR_idx R₀] at this
  have h_n_q_div : Nat.card (Sylow q G) ∣ p * r := by
    have := Sylow.card_dvd_index Q₀
    rwa [hQ_idx Q₀] at this
  have h_n_r_mod : Nat.card (Sylow r G) ≡ 1 [MOD r] := card_sylow_modEq_one r G
  have h_n_q_mod : Nat.card (Sylow q G) ≡ 1 [MOD q] := card_sylow_modEq_one q G
  -- Show n_r = 1 or n_r = p*q
  have h_n_r_cases : Nat.card (Sylow r G) = 1 ∨ Nat.card (Sylow r G) = p * q := by
    set n_r := Nat.card (Sylow r G) with h_n_r_def
    obtain ⟨a, b, ha_dvd, hb_dvd, hab⟩ := Nat.dvd_mul.mp h_n_r_div
    rcases (Nat.dvd_prime h_p_prime.out).mp ha_dvd with ha1 | hap
    · rcases (Nat.dvd_prime h_q_prime.out).mp hb_dvd with hb1 | hbq
      · left; rw [← hab, ha1, hb1, mul_one]
      · exfalso
        have hnr_eq : n_r = q := by rw [← hab, ha1, hbq, one_mul]
        rw [hnr_eq] at h_n_r_mod
        have hmod : q % r = 1 % r := h_n_r_mod
        rw [Nat.mod_eq_of_lt h_q_le_r, Nat.mod_eq_of_lt hr2] at hmod
        omega
    · rcases (Nat.dvd_prime h_q_prime.out).mp hb_dvd with hb1 | hbq
      · exfalso
        have hnr_eq : n_r = p := by rw [← hab, hap, hb1, mul_one]
        rw [hnr_eq] at h_n_r_mod
        have hmod : p % r = 1 % r := h_n_r_mod
        rw [Nat.mod_eq_of_lt h_p_lt_r, Nat.mod_eq_of_lt hr2] at hmod
        omega
      · right; rw [← hab, hap, hbq]
  rcases h_n_r_cases with h_nr1 | h_nr_pq
  · right; exact h_nr1
  · -- n_r = p*q. Need to show n_q = 1, else derive contradiction.
    have h_n_q_cases : Nat.card (Sylow q G) = 1 ∨ r ≤ Nat.card (Sylow q G) := by
      set n_q := Nat.card (Sylow q G) with h_n_q_def
      obtain ⟨a, b, ha_dvd, hb_dvd, hab⟩ := Nat.dvd_mul.mp h_n_q_div
      rcases (Nat.dvd_prime h_p_prime.out).mp ha_dvd with ha1 | hap
      · rcases (Nat.dvd_prime h_r_prime.out).mp hb_dvd with hb1 | hbr
        · left; rw [← hab, ha1, hb1, mul_one]
        · right; rw [← hab, ha1, hbr, one_mul]
      · rcases (Nat.dvd_prime h_r_prime.out).mp hb_dvd with hb1 | hbr
        · exfalso
          have hnq_eq : n_q = p := by rw [← hab, hap, hb1, mul_one]
          rw [hnq_eq] at h_n_q_mod
          have hmod : p % q = 1 % q := h_n_q_mod
          rw [Nat.mod_eq_of_lt h_p_le_q, Nat.mod_eq_of_lt hq2] at hmod
          omega
        · right
          rw [← hab, hap, hbr]
          exact Nat.le_mul_of_pos_left _ hp_pos
    rcases h_n_q_cases with h_nq1 | h_nq_ge_r
    · left; exact h_nq1
    · exfalso
      -- Count elements of order r and order q
      have h_count_r : Nat.card {x : G | orderOf x = r} = p * q * (r - 1) := by
        rw [sylow_elements_order_p_card hR_card, h_nr_pq]
      have h_count_q : Nat.card {x : G | orderOf x = q} =
          Nat.card (Sylow q G) * (q - 1) := sylow_elements_order_p_card hQ_card
      haveI hFinG : Fintype G := Fintype.ofFinite G
      haveI hDecEq : DecidableEq G := Classical.decEq G
      let S_r : Finset G := ({x | orderOf x = r} : Set G).toFinset
      let S_q : Finset G := ({x | orderOf x = q} : Set G).toFinset
      have hSr_card : S_r.card = p * q * (r - 1) := by
        have heq : S_r.card = Nat.card {x : G | orderOf x = r} := by
          change ({x : G | orderOf x = r} : Set G).toFinset.card = _
          rw [Set.toFinset_card, Nat.card_eq_fintype_card]
        rw [heq, h_count_r]
      have hSq_card : S_q.card = Nat.card (Sylow q G) * (q - 1) := by
        have heq : S_q.card = Nat.card {x : G | orderOf x = q} := by
          change ({x : G | orderOf x = q} : Set G).toFinset.card = _
          rw [Set.toFinset_card, Nat.card_eq_fintype_card]
        rw [heq, h_count_q]
      have h1_notin_Sr : (1 : G) ∉ S_r := by
        simp only [S_r, Set.mem_toFinset, Set.mem_setOf_eq, orderOf_one]
        omega
      have h1_notin_Sq : (1 : G) ∉ S_q := by
        simp only [S_q, Set.mem_toFinset, Set.mem_setOf_eq, orderOf_one]
        omega
      have hSrq_disj : Disjoint S_r S_q := by
        rw [Finset.disjoint_left]
        intro x hxr hxq
        simp only [S_r, Set.mem_toFinset, Set.mem_setOf_eq] at hxr
        simp only [S_q, Set.mem_toFinset, Set.mem_setOf_eq] at hxq
        rw [hxr] at hxq
        exact h_q_ne_r.symm hxq
      have h1_S_disj : Disjoint ({(1 : G)} : Finset G) (S_r ∪ S_q) := by
        rw [Finset.disjoint_left]
        intro x hx hxun
        rw [Finset.mem_singleton] at hx
        subst hx
        rcases Finset.mem_union.mp hxun with h | h
        · exact h1_notin_Sr h
        · exact h1_notin_Sq h
      have h_union_card : (({(1 : G)} : Finset G) ∪ (S_r ∪ S_q)).card =
          1 + S_r.card + S_q.card := by
        rw [Finset.card_union_of_disjoint h1_S_disj,
            Finset.card_union_of_disjoint hSrq_disj, Finset.card_singleton]
        ring
      have h_le : (({(1 : G)} : Finset G) ∪ (S_r ∪ S_q)).card ≤ Fintype.card G :=
        Finset.card_le_card (Finset.subset_univ _)
      rw [h_union_card, hSr_card, hSq_card,
          ← Nat.card_eq_fintype_card, h] at h_le
      -- 1 + p*q*(r-1) + n_q*(q-1) ≤ p*q*r and r ≤ n_q so:
      have h_aux : 1 + p * q * (r - 1) + r * (q - 1) ≤ p * q * r := by
        calc 1 + p * q * (r - 1) + r * (q - 1)
            ≤ 1 + p * q * (r - 1) + Nat.card (Sylow q G) * (q - 1) := by
                  have := Nat.mul_le_mul_right (q - 1) h_nq_ge_r
                  omega
          _ ≤ p * q * r := h_le
      -- Rewrite using Nat.mul_sub_one
      have h_pq_expand : p * q * (r - 1) = p * q * r - p * q := Nat.mul_sub_one (p * q) r
      have h_r_expand : r * (q - 1) = r * q - r := Nat.mul_sub_one r q
      have h_pq_le_pqr : p * q ≤ p * q * r := Nat.le_mul_of_pos_right _ hr_pos
      -- Key claim: (q - 1) * r ≥ p * q
      have h_key : (q - 1) * r ≥ p * q := by
        calc (q - 1) * r ≥ (q - 1) * q := Nat.mul_le_mul_left _ (le_of_lt h_q_le_r)
          _ ≥ p * q := Nat.mul_le_mul_right _ (by omega)
      have h_key2 : q * r - r ≥ p * q := by
        have := h_key
        rw [Nat.sub_one_mul] at this
        exact this
      rw [h_pq_expand, h_r_expand] at h_aux
      have hcomm : r * q = q * r := mul_comm r q
      rw [hcomm] at h_aux
      set A := p * q with hA
      set B := q * r with hB
      set D := p * q * r with hD
      have hr_le_B : r ≤ B := by rw [hB]; exact Nat.le_mul_of_pos_left _ hq_pos
      have hA_le_D : A ≤ D := by rw [hA, hD]; exact h_pq_le_pqr
      have h_B_minus_r_ge_A : B - r ≥ A := by rw [hB]; exact h_key2
      omega
