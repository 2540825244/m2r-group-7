import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Semisimple
import Mathlib.LinearAlgebra.Eigenspace.Semisimple
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Data.ZMod.Basic
import «M2rGroup7».PqCase

set_option linter.style.nativeDecide false

/-!
## Classification of order-2 elements of GL₂(𝔽_p), p odd prime

Proof outline:
  Let M = A.val. Since A has order 2, M² = I and M ≠ I.
  The minimal polynomial of M divides X² - 1 = (X - 1)(X + 1),
  which is squarefree since p ≠ 2 (so 1 ≠ -1 in 𝔽_p).
  Hence M is semisimple, and since both eigenvalues ±1 lie in 𝔽_p,
  M is diagonalizable over 𝔽_p. The diagonal form has entries in {1,-1}.
  Excluding M = I (order 1), the similarity classes are:
  · diag(1,-1) = diag(-1,1)  (one class, since the two are conjugate via the permutation matrix)
  · diag(-1,-1) = -I          (the central element)
-/

section GL2OrderTwo

variable {p : ℕ} [hp : Fact p.Prime]

private lemma diag_self_mul_aux (v : Fin 2 → ZMod p) (hv : ∀ i, v i * v i = 1) :
    Matrix.diagonal v * Matrix.diagonal v = 1 := by
  rw [Matrix.diagonal_mul_diagonal]
  ext i j
  simp only [Matrix.diagonal_apply, Matrix.one_apply]
  split_ifs with h
  · exact hv i
  · simp

/-- The element diag(1, -1) of GL₂(𝔽_p).
    Defined only for odd p (p ≠ 2) since we need 1 ≠ -1 to ensure it has order 2
    (for the statement; the matrix itself is always well-defined). -/
noncomputable def gl2Diag1NegOne (_hp2 : p ≠ 2) : GL (Fin 2) (ZMod p) :=
  let v : Fin 2 → ZMod p := ![(1 : ZMod p), -1]
  have hv : ∀ i : Fin 2, v i * v i = 1 := by intro i; fin_cases i <;> simp [v]
  ⟨Matrix.diagonal v, Matrix.diagonal v, diag_self_mul_aux v hv, diag_self_mul_aux v hv⟩

/-- The element diag(-1, -1) = -I of GL₂(𝔽_p). -/
noncomputable def gl2DiagNeg1Neg1 : GL (Fin 2) (ZMod p) := -1

@[simp] lemma gl2Diag1NegOne_val (hp2 : p ≠ 2) :
    (gl2Diag1NegOne hp2 : GL (Fin 2) (ZMod p)).val =
      Matrix.diagonal ![(1 : ZMod p), -1] := rfl

@[simp] lemma gl2DiagNeg1Neg1_val :
    (gl2DiagNeg1Neg1 : GL (Fin 2) (ZMod p)).val =
      -(1 : Matrix (Fin 2) (Fin 2) (ZMod p)) := rfl

/-- Helper: if `P` is a `2×2` matrix with nonzero determinant and
    `A.val * P = P * diag(1,-1)`, then `A` is conjugate to `gl2Diag1NegOne hp2`. -/
private lemma isConj_of_conj_matrix (hp2 : p ≠ 2) (A : GL (Fin 2) (ZMod p))
    (P : Matrix (Fin 2) (Fin 2) (ZMod p)) (hPdet : P.det ≠ 0)
    (hconj : A.val * P = P * Matrix.diagonal ![(1 : ZMod p), -1]) :
    IsConj A (gl2Diag1NegOne hp2) := by
  rw [isConj_iff]
  refine ⟨(Matrix.GeneralLinearGroup.mkOfDetNeZero P hPdet)⁻¹, ?_⟩
  apply Units.ext
  have hP_val : (Matrix.GeneralLinearGroup.mkOfDetNeZero P hPdet : GL (Fin 2) (ZMod p)).val = P :=
    rfl
  have hPinv_val :
      ((Matrix.GeneralLinearGroup.mkOfDetNeZero P hPdet : GL (Fin 2) (ZMod p))⁻¹).val = P⁻¹ := by
    rw [Matrix.coe_units_inv, hP_val]
  simp only [Units.val_mul, inv_inv, gl2Diag1NegOne_val, hPinv_val, hP_val]
  rw [mul_assoc, hconj, ← mul_assoc,
      Matrix.nonsing_inv_mul P (isUnit_iff_ne_zero.mpr hPdet), one_mul]

-- `simp [Matrix.mul_apply]` after `fin_cases` needs flexible simp since `Matrix.cons_val_zero`
-- does not fire on the `⟨n, h⟩`-form Fin indices that `fin_cases` produces.
set_option linter.flexible false in
/-- Any element A of GL₂(𝔽_p) of order 2 (p an odd prime) is conjugate in GL₂(𝔽_p) to
    either diag(1, -1) or diag(-1, -1). -/
theorem gl2_order_two_classification (hp2 : p ≠ 2) (A : GL (Fin 2) (ZMod p))
    (hA : orderOf A = 2) :
    IsConj A (gl2Diag1NegOne hp2) ∨ IsConj A (gl2DiagNeg1Neg1 : GL (Fin 2) (ZMod p)) := by
  -- A² = 1 in GL
  have hA_sq : A ^ 2 = 1 := by
    have h := pow_orderOf_eq_one A; rw [hA] at h; exact h
  -- A ≠ 1
  have hA_ne1 : A ≠ 1 := by intro h; simp [h, orderOf_one] at hA
  -- Underlying matrix M = A.val satisfies M * M = I
  have hM_sq : A.val * A.val = 1 := by
    have h : (A ^ 2 : GL (Fin 2) (ZMod p)).val = (1 : GL (Fin 2) (ZMod p)).val :=
      congr_arg Units.val hA_sq
    rw [Units.val_pow_eq_pow_val, Units.val_one] at h
    rwa [sq] at h
  -- Case on A = -1 (i.e. A = diag(-1,-1)) or not
  by_cases hAneg : A = -1
  · -- A = -I: conjugate to itself via 1
    right
    subst hAneg
    -- gl2DiagNeg1Neg1 is defined as -1; show IsConj (-1) (-1) with c = 1
    change IsConj (-1 : GL (Fin 2) (ZMod p)) (-1 : GL (Fin 2) (ZMod p))
    exact ⟨1, by unfold SemiconjBy; simp [Units.val_one, mul_one]⟩
  · -- A ≠ -I: A is conjugate to diag(1,-1).
    -- Write M = A.val as !![a, b; c, d] and derive the four entry equations from M*M = I.
    -- Build a conjugating matrix P by cases on whether c = 0.
    left
    set M := A.val with hM_def
    have hM_eq : M = !![M 0 0, M 0 1; M 1 0, M 1 1] := Matrix.eta_fin_two M
    set a := M 0 0
    set b := M 0 1
    set c := M 1 0
    set d := M 1 1
    have hsq : !![a, b; c, d] * !![a, b; c, d] = (1 : Matrix (Fin 2) (Fin 2) (ZMod p)) := by
      rw [← hM_eq]; exact hM_sq
    rw [Matrix.mul_fin_two] at hsq
    have h00 : a * a + b * c = 1 := by
      have := congrArg (fun N : Matrix (Fin 2) (Fin 2) (ZMod p) => N 0 0) hsq
      simp only [Matrix.one_apply, Fin.isValue] at this; exact this
    have h01 : a * b + b * d = 0 := by
      have := congrArg (fun N : Matrix (Fin 2) (Fin 2) (ZMod p) => N 0 1) hsq
      simp only [Matrix.one_apply, Fin.isValue] at this; exact this
    have h10 : c * a + d * c = 0 := by
      have := congrArg (fun N : Matrix (Fin 2) (Fin 2) (ZMod p) => N 1 0) hsq
      simp only [Matrix.one_apply, Fin.isValue] at this; exact this
    have h11 : c * b + d * d = 1 := by
      have := congrArg (fun N : Matrix (Fin 2) (Fin 2) (ZMod p) => N 1 1) hsq
      simp only [Matrix.one_apply, Fin.isValue] at this; exact this
    have hM_ne_one : M ≠ 1 := by
      intro h; apply hA_ne1; ext1; rw [Units.val_one]; exact h
    have hM_ne_negone : M ≠ -1 := by
      intro h; apply hAneg; ext1; rw [Units.val_neg, Units.val_one]; exact h
    have h_two_ne_zero : (2 : ZMod p) ≠ 0 := by
      have hp_prime := hp.out
      have h2cast : (2 : ZMod p) = ((2 : ℕ) : ZMod p) := by norm_cast
      rw [h2cast, Ne, ZMod.natCast_eq_zero_iff]
      intro hdvd
      have := (Nat.prime_dvd_prime_iff_eq hp_prime Nat.prime_two).mp hdvd
      exact hp2 this
    by_cases hc0 : c = 0
    · -- c = 0: a² = d² = 1, and either a = -d (giving the diagonalizable case)
      -- or a = d = ±1 (leading to M = ±I, contradicting hM_ne_one / hM_ne_negone).
      have ha_sq : a * a = 1 := by rw [hc0] at h00; simpa using h00
      have hd_sq : d * d = 1 := by rw [hc0] at h11; simpa using h11
      have hbad : b * (a + d) = 0 := by linear_combination h01
      have ha_cases : a = 1 ∨ a = -1 := by
        have : (a - 1) * (a + 1) = 0 := by linear_combination ha_sq
        rcases mul_eq_zero.mp this with h | h
        · left; linear_combination h
        · right; linear_combination h
      have hd_cases : d = 1 ∨ d = -1 := by
        have : (d - 1) * (d + 1) = 0 := by linear_combination hd_sq
        rcases mul_eq_zero.mp this with h | h
        · left; linear_combination h
        · right; linear_combination h
      rcases ha_cases with ha | ha
      · rcases hd_cases with hd | hd
        · exfalso
          have hb0 : b = 0 := by
            have h2b : b * 2 = 0 := by rw [ha, hd] at hbad; linear_combination hbad
            rcases mul_eq_zero.mp h2b with h | h
            · exact h
            · exact absurd h h_two_ne_zero
          apply hM_ne_one
          rw [hM_eq, ha, hb0, hc0, hd]
          ext i j; fin_cases i <;> fin_cases j <;> simp
        · apply isConj_of_conj_matrix hp2 A !![(1 : ZMod p), b; 0, -2]
          · rw [Matrix.det_fin_two_of]
            intro h
            apply h_two_ne_zero
            linear_combination -h
          · change M * _ = _
            rw [hM_eq, ha, hc0, hd]
            ext i j; fin_cases i <;> fin_cases j <;>
              simp [Matrix.mul_apply, Fin.sum_univ_succ]; ring
      · rcases hd_cases with hd | hd
        · apply isConj_of_conj_matrix hp2 A !![b, (-2 : ZMod p); 2, 0]
          · rw [Matrix.det_fin_two_of]
            intro h4
            have h2sq : (2 : ZMod p) * 2 = 0 := by linear_combination h4
            rcases mul_eq_zero.mp h2sq with h | h
            · exact h_two_ne_zero h
            · exact h_two_ne_zero h
          · change M * _ = _
            rw [hM_eq, ha, hc0, hd]
            ext i j; fin_cases i <;> fin_cases j <;>
              simp [Matrix.mul_apply, Fin.sum_univ_succ]; ring
        · exfalso
          have hb0 : b = 0 := by
            have h2b : b * (-2) = 0 := by rw [ha, hd] at hbad; linear_combination hbad
            rcases mul_eq_zero.mp h2b with h | h
            · exact h
            · exfalso; apply h_two_ne_zero; linear_combination -h
          apply hM_ne_negone
          rw [hM_eq, ha, hb0, hc0, hd]
          ext i j; fin_cases i <;> fin_cases j <;> simp
    · -- c ≠ 0: h10 forces a + d = 0, and we take P = !![a+1, a-1; c, c] (det = 2c ≠ 0).
      have had : a + d = 0 := by
        have hcad : c * (a + d) = 0 := by linear_combination h10
        rcases mul_eq_zero.mp hcad with h | h
        · exact absurd h hc0
        · exact h
      have hd_eq : d = -a := by linear_combination had
      have hbc : b * c = 1 - a * a := by linear_combination h00
      apply isConj_of_conj_matrix hp2 A !![a + 1, a - 1; c, c]
      · rw [Matrix.det_fin_two_of]
        intro hdet
        have h2c : (2 : ZMod p) * c = 0 := by linear_combination hdet
        rcases mul_eq_zero.mp h2c with h | h
        · exact h_two_ne_zero h
        · exact hc0 h
      · change M * _ = _
        rw [hM_eq, hd_eq]
        have hbc' : c * b = 1 - a * a := by linear_combination hbc
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [Matrix.mul_apply, Fin.sum_univ_succ] <;>
          first
            | linear_combination hbc
            | linear_combination hbc'
            | ring

end GL2OrderTwo

/-- GL₂(𝔽₂) ≅ S₃ (DihedralGroup 3) -/
noncomputable def GL2F2_isoS3 : GL (Fin 2) (ZMod 2) ≃* DihedralGroup 3 :=
  Classical.choice (by
    have hcard : Nat.card (GL (Fin 2) (ZMod 2)) = 6 := by
      rw [Nat.card_eq_fintype_card]; native_decide
    rcases order6_classification hcard with h | h
    · -- CyclicGroup 6 is abelian, but GL₂(𝔽₂) is not
      obtain ⟨e⟩ := h
      have hcomm : ∀ a b : GL (Fin 2) (ZMod 2), a * b = b * a :=
        fun a b => e.injective (by
          rw [map_mul e, map_mul e]
          exact @mul_comm (Multiplicative (ZMod 6)) inferInstance (e a) (e b))
      exact absurd hcomm (by native_decide)
    · exact h)

/-- The automorphism group of C_p × C_p is isomorphic to GL(2, 𝔽_p).
    Proof sketch:
      MulAut(C_p × C_p)
        ≃*  AddAut(ZMod p × ZMod p)
              [strip Multiplicative: MulAutMultiplicative + MulEquiv.prodMultiplicative]
        ≃*  (ZMod p × ZMod p) ≃ₗ[ZMod p] (ZMod p × ZMod p)
              [AddMonoidHom.toZModLinearMapEquiv: every additive aut of a ZMod p-module is linear]
        ≃*  GL (Fin 2) (ZMod p)
              [Matrix.GeneralLinearGroup.toLin' with standard basis] -/
lemma aut_of_CpCp (p : ℕ) [hp : Fact p.Prime] :
    Nonempty (MulAut (CyclicGroup p × CyclicGroup p) ≃* GL (Fin 2) (ZMod p)) := by
  -- Step 1: strip the Multiplicative wrapper
  -- CyclicGroup p = Multiplicative (ZMod p), so C_p × C_p ≃* Multiplicative (ZMod p × ZMod p)
  -- Then MulAutMultiplicative gives MulAut (Multiplicative G) ≃* AddAut G
  have step1 : MulAut (CyclicGroup p × CyclicGroup p) ≃* AddAut (ZMod p × ZMod p) :=
    (MulAut.congr (MulEquiv.prodMultiplicative (ZMod p) (ZMod p)).symm).trans
      (MulAutMultiplicative (ZMod p × ZMod p))
  -- Step 2: every additive automorphism of a ZMod p-module is automatically ZMod p-linear
  -- (AddMonoidHom.toZModLinearMap shows additive homs between ZMod p-modules are linear)
  have step2 : AddAut (ZMod p × ZMod p) ≃*
      ((ZMod p × ZMod p) ≃ₗ[ZMod p] (ZMod p × ZMod p)) :=
    { toFun := fun f => f.toLinearEquiv
        (fun r x => (AddMonoidHom.toZModLinearMap p f.toAddMonoidHom).map_smul r x)
      invFun := fun g => g.toAddEquiv
      left_inv := fun f => by
        apply AddEquiv.ext
        intro x
        rfl
      right_inv := fun g => by
        apply LinearEquiv.ext
        intro x
        rfl
      map_mul' := fun f g => by
        apply LinearEquiv.ext
        intro x
        rfl
      }
  -- Step 3: LinearEquiv group ≃* GL(Fin 2, ZMod p)
  -- via generalLinearEquiv, then finTwoArrow to match (Fin 2 → ZMod p), then toLin
  have step3 : ((ZMod p × ZMod p) ≃ₗ[ZMod p] (ZMod p × ZMod p)) ≃* GL (Fin 2) (ZMod p) :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod p) (ZMod p × ZMod p)).symm
      |>.trans (LinearMap.GeneralLinearGroup.congrLinearEquiv
        (LinearEquiv.finTwoArrow (ZMod p) (ZMod p)).symm)
      |>.trans Matrix.GeneralLinearGroup.toLin.symm
  exact ⟨step1.trans (step2.trans step3)⟩
