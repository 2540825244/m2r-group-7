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
  · -- A ≠ -I: A is conjugate to diag(1,-1)
    left
    -- Strategy: since M² = I, M ≠ I, M ≠ -I, the minimal polynomial of M divides
    -- (X-1)(X+1), which is squarefree (p odd). Both eigenvalues
    -- ±1 lie in 𝔽_p, so M is diagonalizable over 𝔽_p with eigenvalues {1, -1}.
    -- Concretely: since M ≠ -I, the matrix M + I ≠ 0, so pick a nonzero column v₊
    -- of M + I; it satisfies M * v₊ = v₊ (a 1-eigenvector, since (M-I)(M+I) = M²-I = 0).
    -- Similarly, since M ≠ I, pick a nonzero column v₋ of M - I satisfying M * v₋ = -v₋.
    -- Since 1 ≠ -1 (p ≠ 2), v₊ and v₋ are linearly independent.
    -- The matrix P = [v₊ | v₋] ∈ GL₂(𝔽_p) conjugates A to diag(1,-1).
    sorry

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
