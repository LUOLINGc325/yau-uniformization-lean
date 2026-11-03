import Yau.Proofs.C02PullbackMatrixQuadratic

/-! Intrinsic quadratic estimates imply the exact Hermitian matrix order
used by the original uniform-chart contract, in every finite dimension. -/

noncomputable section
open scoped Manifold Matrix ComplexOrder
namespace Yau.Blueprint.C02Proof
variable {n : ℕ} {M : ComplexManifold n}

theorem real_scalar_identity_quadratic (c : ℝ) (u : ComplexVector n) :
    (star (WithLp.ofLp u) ⬝ᵥ (((c : ℂ) • (1 : Herm n)) *ᵥ WithLp.ofLp u)).re =
      c * ‖u‖ ^ 2 := by
  rw [Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul]
  change ((c : ℂ) * (star (WithLp.ofLp u) ⬝ᵥ WithLp.ofLp u)).re = _
  rw [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct,
    inner_self_eq_norm_sq_to_K]
  change ((c : ℂ) * ((‖u‖ : ℂ) ^ 2)).re = _
  rw [← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]

theorem pullbackMat_bounds_of_quadratic
    (h : HermitianField M) (Φ : ComplexVector n → M.Carrier) (z : ComplexVector n)
    (c C : ℝ)
    (hLower : ∀ u : ComplexVector n, c * ‖u‖ ^ 2 ≤ hermitianNormSq (h (Φ z))
      (mfderiv 𝓘(ℂ, ComplexVector n) (ComplexModel n) Φ z u))
    (hUpper : ∀ u : ComplexVector n, hermitianNormSq (h (Φ z))
      (mfderiv 𝓘(ℂ, ComplexVector n) (ComplexModel n) Φ z u) ≤ C * ‖u‖ ^ 2) :
    HermLE ((c : ℂ) • (1 : Herm n)) (pullbackMat h Φ z) ∧
      HermLE (pullbackMat h Φ z) ((C : ℂ) • (1 : Herm n)) := by
  have hH := pullbackMat_isHermitian h Φ z
  have hI (a : ℝ) : (((a : ℂ) • (1 : Herm n))).IsHermitian :=
    Matrix.isHermitian_one.smul (by simp [IsSelfAdjoint])
  constructor
  · have hHerm := hH.sub (hI c)
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hHerm
    intro v
    apply Complex.nonneg_iff.mpr
    refine ⟨?_, (hHerm.im_star_dotProduct_mulVec_self v).symm⟩
    have hh := hLower (WithLp.toLp 2 v)
    change c * ‖WithLp.toLp 2 v‖ ^ 2 ≤ ((h (Φ z)).toFun _ _).re at hh
    rw [← pullbackMat_quadratic, ← real_scalar_identity_quadratic c] at hh
    simpa only [Matrix.sub_mulVec, dotProduct_sub, Complex.sub_re,
      WithLp.ofLp_toLp] using sub_nonneg.mpr hh
  · have hHerm := (hI C).sub hH
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hHerm
    intro v
    apply Complex.nonneg_iff.mpr
    refine ⟨?_, (hHerm.im_star_dotProduct_mulVec_self v).symm⟩
    have hh := hUpper (WithLp.toLp 2 v)
    change ((h (Φ z)).toFun _ _).re ≤ C * ‖WithLp.toLp 2 v‖ ^ 2 at hh
    rw [← pullbackMat_quadratic, ← real_scalar_identity_quadratic C] at hh
    simpa only [Matrix.sub_mulVec, dotProduct_sub, Complex.sub_re,
      WithLp.ofLp_toLp] using sub_nonneg.mpr hh

end Yau.Blueprint.C02Proof
