import Mathlib
import «M2rGroup7».Lemmas.NumberTheoryUtils

/-!
# Conjugacy classes of order `q` subgroups in `GL₂(𝔽_p)`

Let `p`, `q` be distinct primes with `q > 2`. This file proves that the
number of conjugacy classes of subgroups of order `q` in `GL₂(𝔽_p)` equals
$$ \tfrac{q+3}{2}\,\Delta_{p-1}^{q} \;+\; \Delta_{p+1}^{q}, $$
where `Δ_m^n = 1` if `n ∣ m` and `0` otherwise.

(The user's phrasing "matrices `A` of order `q`" follows the blueprint
convention of counting cyclic subgroups `⟨A⟩` of order `q`.)

The proof follows the blueprint source `conjugacy-classes-of-order-q-over-gl2-f-p-source.tex`:

* Since `q` is an odd prime, `q` cannot divide both `p - 1` and `p + 1`
  (it would divide their difference `2`).
* **Case 1** (`q ∣ p + 1`): no eigenvalues in `𝔽_p`, so any order-`q` subgroup
  embeds into a Singer cycle `S ≅ C_{p²-1}`; `S` has a unique subgroup of order
  `q`, giving exactly `1` conjugacy class.
* **Case 2** (`q ∣ p - 1`): every order-`q` subgroup is diagonalisable. The
  conjugacy classes correspond to orbits of `ℓ ↦ ℓ⁻¹` on `𝔽_q ∪ {∞}`, which
  total `(q + 3) / 2`.
* **Case 3** (`q ∤ p² - 1`): no element of order `q` exists in `GL₂(𝔽_p)`, so
  the count is `0`.

The two case-specific structural computations are proved at this stage as
placeholder lemmas (`sorry`); the dichotomy and the main combination are
finished here.
-/

namespace M2rGroup7.Lemmas

open scoped Pointwise

/-! ### Divisibility indicator -/

/-- `deltaDiv a b = 1` if `a ∣ b`, otherwise `0`. This is `Δ_b^a` in the
blueprint notation. -/
noncomputable def deltaDiv (a b : ℕ) : ℕ := if a ∣ b then 1 else 0

@[simp] lemma deltaDiv_eq_one_iff {a b : ℕ} : deltaDiv a b = 1 ↔ a ∣ b := by
  unfold deltaDiv; split_ifs with h <;> simp [h]

@[simp] lemma deltaDiv_eq_zero_iff {a b : ℕ} : deltaDiv a b = 0 ↔ ¬ a ∣ b := by
  unfold deltaDiv; split_ifs with h <;> simp [h]

lemma deltaDiv_of_dvd {a b : ℕ} (h : a ∣ b) : deltaDiv a b = 1 :=
  deltaDiv_eq_one_iff.mpr h

lemma deltaDiv_of_not_dvd {a b : ℕ} (h : ¬ a ∣ b) : deltaDiv a b = 0 :=
  deltaDiv_eq_zero_iff.mpr h

/-! ### Conjugacy on subgroups -/

/-- Two subgroups `H₁`, `H₂` of a group `G` are conjugate if there is `g ∈ G`
with `g H₁ g⁻¹ = H₂`. -/
def Subgroup.IsConj {G : Type*} [Group G] (H₁ H₂ : Subgroup G) : Prop :=
  ∃ g : G, H₁.map (MulEquiv.toMonoidHom (MulAut.conj g)) = H₂

namespace Subgroup.IsConj

variable {G : Type*} [Group G]

lemma refl (H : Subgroup G) : Subgroup.IsConj H H := by
  refine ⟨1, ?_⟩
  ext x
  simp [Subgroup.mem_map]

lemma symm {H₁ H₂ : Subgroup G} (h : Subgroup.IsConj H₁ H₂) :
    Subgroup.IsConj H₂ H₁ := by
  obtain ⟨g, hg⟩ := h
  refine ⟨g⁻¹, ?_⟩
  rw [← hg, Subgroup.map_map]
  convert Subgroup.map_id H₁
  ext x
  simp [MulAut.conj_apply, mul_assoc]

lemma trans {H₁ H₂ H₃ : Subgroup G} (h₁ : Subgroup.IsConj H₁ H₂)
    (h₂ : Subgroup.IsConj H₂ H₃) : Subgroup.IsConj H₁ H₃ := by
  obtain ⟨g, hg⟩ := h₁
  obtain ⟨g', hg'⟩ := h₂
  refine ⟨g' * g, ?_⟩
  rw [← hg', ← hg, Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

end Subgroup.IsConj

/-- The setoid of subgroups of `G` under conjugacy. -/
def Subgroup.conjSetoid (G : Type*) [Group G] : Setoid (Subgroup G) where
  r := Subgroup.IsConj
  iseqv :=
    { refl := Subgroup.IsConj.refl
      symm := Subgroup.IsConj.symm
      trans := Subgroup.IsConj.trans }

/-- The number of conjugacy classes of subgroups of order `q` in `G`. -/
noncomputable def numConjClassesOfSubgroupsOfOrder (G : Type*) [Group G] (q : ℕ) : ℕ :=
  Nat.card (Quotient
    ((Subgroup.conjSetoid G).comap
      (fun H : {H : Subgroup G // Nat.card H = q} => H.val)))

/-! ### Dichotomy: an odd prime `q` cannot divide both `p - 1` and `p + 1` -/

/-- If `q > 2` is prime and divides both `p - 1` and `p + 1`, contradiction. -/
lemma not_dvd_both_sub_one_add_one {p q : ℕ} (hp : 1 ≤ p)
    (hq2 : 2 < q) :
    ¬ (q ∣ (p - 1) ∧ q ∣ (p + 1)) := by
  rintro ⟨h1, h2⟩
  -- q divides (p + 1) - (p - 1) = 2
  have hdvd : q ∣ 2 := by
    have hsub : (p + 1) - (p - 1) = 2 := by omega
    rw [← hsub]
    exact Nat.dvd_sub h2 h1
  have hle : q ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
  omega

/-! ### Case-specific structural lemmas (admitted) -/

/-- **Case 1** (`q ∣ p + 1`). When `q` is an odd prime distinct from `p` and
`q ∣ p + 1`, every order-`q` subgroup of `GL₂(𝔽_p)` is conjugate to the unique
order-`q` subgroup of the Singer cycle `S ≅ C_{p²-1}`. Hence the number of
conjugacy classes of such subgroups equals `1`.

Proof sketch (blueprint, Case 1):
  * `q ∤ p - 1` so `𝔽_p` contains no primitive `q`-th roots of unity, hence no
    reducible (diagonalisable) order-`q` subgroup exists.
  * `q ∣ p² - 1` so `𝔽_{p²}` contains primitive `q`-th roots of unity, and
    `𝔽_{p²}^×` embeds in `GL₂(𝔽_p)` as a Singer cycle `S ≅ C_{p²-1}`.
  * `S` is cyclic and `q ∣ |S|`, so `S` has a unique subgroup of order `q`.
  * Any irreducible order-`q` subgroup is conjugate into `S`. Inside the
    Singer normalizer `N = C_2 ⋉ S`, the unique order-`q` subgroup of `S`
    is the only one (since `q` is odd, the order-`2` factor cannot supply a
    new copy). Hence there is exactly `1` conjugacy class. -/
theorem numConjClassesOfSubgroupsOfOrder_GL2_of_q_dvd_p_add_one
    {p q : ℕ} [hp : Fact p.Prime] (hq : q.Prime) (hq2 : 2 < q) (hpq : p ≠ q)
    (h_dvd : q ∣ p + 1) :
    numConjClassesOfSubgroupsOfOrder (GL (Fin 2) (ZMod p)) q = 1 := by
  sorry

/-- **Case 2** (`q ∣ p - 1`). When `q` is an odd prime distinct from `p` and
`q ∣ p - 1`, every order-`q` subgroup of `GL₂(𝔽_p)` is conjugate to a diagonal
order-`q` subgroup. The conjugation action permutes the diagonal subgroups via
`ℓ ↦ ℓ⁻¹` on the slope parameter `ℓ ∈ 𝔽_q ∪ {∞}`. Counting orbits gives
`1 + 1 + 1 + (q - 3) / 2 = (q + 3) / 2` conjugacy classes.

Proof sketch (blueprint, Case 2):
  * Every order-`q` subgroup `U` of `GL₂(𝔽_p)` is reducible (since `𝔽_p`
    contains a primitive `q`-th root of unity `a`), hence conjugate into the
    diagonal subgroup `D ≅ C_{p-1} × C_{p-1}`.
  * The order-`q` subgroups of `D` are parametrized by `ℓ ∈ 𝔽_q ∪ {∞}` via
    `U_ℓ = ⟨diag(a, a^ℓ)⟩` (with the convention `U_∞ = ⟨diag(1, a)⟩`).
  * `N_{GL_2}(D) = C_2 ⋉ D`, where the `C_2` swaps the diagonal entries; this
    sends `U_ℓ ↦ U_{ℓ⁻¹}` on the parameter space.
  * Orbits of `ℓ ↦ ℓ⁻¹` on `𝔽_q ∪ {∞}`:
    - `{0, ∞}` (1 orbit);
    - `{1}` (1 orbit);
    - `{-1}` (1 orbit);
    - the remaining `q - 3` elements pair up into `(q - 3) / 2` orbits.
    Total: `3 + (q - 3) / 2 = (q + 3) / 2`. -/
theorem numConjClassesOfSubgroupsOfOrder_GL2_of_q_dvd_p_sub_one
    {p q : ℕ} [hp : Fact p.Prime] (hq : q.Prime) (hq2 : 2 < q) (hpq : p ≠ q)
    (h_dvd : q ∣ p - 1) :
    numConjClassesOfSubgroupsOfOrder (GL (Fin 2) (ZMod p)) q = (q + 3) / 2 := by
  sorry

/-- **Case 3** (`q ∤ p² - 1`). If `q` divides neither `p - 1` nor `p + 1` then
`q` is coprime to `|GL₂(𝔽_p)| = p (p - 1)² (p + 1)`, hence by Lagrange (or
Cauchy) there is no element, and therefore no subgroup, of order `q`. The
number of conjugacy classes is `0`. -/
theorem numConjClassesOfSubgroupsOfOrder_GL2_of_q_not_dvd
    {p q : ℕ} [hp : Fact p.Prime] (hq : q.Prime) (hq2 : 2 < q) (hpq : p ≠ q)
    (h1 : ¬ q ∣ p - 1) (h2 : ¬ q ∣ p + 1) :
    numConjClassesOfSubgroupsOfOrder (GL (Fin 2) (ZMod p)) q = 0 := by
  sorry

/-! ### Main theorem -/

/-- **Main theorem.** Let `p`, `q` be distinct primes with `q > 2`. The number
of conjugacy classes of subgroups of order `q` (equivalently, cyclic subgroups
generated by matrices of order `q`) in `GL₂(𝔽_p)` equals
$$ \tfrac{q+3}{2}\,\Delta_{p-1}^{q} \;+\; \Delta_{p+1}^{q}, $$
where `Δ_b^a = 1` if `a ∣ b` and `0` otherwise. -/
theorem numConjClassesOfSubgroupsOfOrder_GL2
    {p q : ℕ} [hp : Fact p.Prime] (hq : q.Prime) (hq2 : 2 < q) (hpq : p ≠ q) :
    numConjClassesOfSubgroupsOfOrder (GL (Fin 2) (ZMod p)) q
      = (q + 3) / 2 * deltaDiv q (p - 1) + deltaDiv q (p + 1) := by
  -- `q` cannot divide both `p - 1` and `p + 1`.
  have hpos : 1 ≤ p := hp.out.one_lt.le
  by_cases h1 : q ∣ p - 1
  · -- Case 1: q ∣ p - 1, so q ∤ p + 1.
    have h2 : ¬ q ∣ p + 1 := fun h2' =>
      not_dvd_both_sub_one_add_one hpos hq2 ⟨h1, h2'⟩
    rw [numConjClassesOfSubgroupsOfOrder_GL2_of_q_dvd_p_sub_one hq hq2 hpq h1,
        deltaDiv_of_dvd h1, deltaDiv_of_not_dvd h2]
    ring
  · by_cases h2 : q ∣ p + 1
    · -- Case 2: q ∣ p + 1, so q ∤ p - 1 (by assumption).
      rw [numConjClassesOfSubgroupsOfOrder_GL2_of_q_dvd_p_add_one hq hq2 hpq h2,
          deltaDiv_of_not_dvd h1, deltaDiv_of_dvd h2]
      ring
    · -- Case 3: q divides neither.
      rw [numConjClassesOfSubgroupsOfOrder_GL2_of_q_not_dvd hq hq2 hpq h1 h2,
          deltaDiv_of_not_dvd h1, deltaDiv_of_not_dvd h2]
      ring

end M2rGroup7.Lemmas
