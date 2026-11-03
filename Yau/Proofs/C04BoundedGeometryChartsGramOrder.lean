import Yau.Proofs.C04BoundedGeometryChartsPairing
import Yau.Blueprint.Stages

/-! Hermitian matrix order follows from bounds on the actual Hermitian quadratic form. -/
noncomputable section
open scoped Topology Matrix ComplexOrder InnerProductSpace
namespace Yau.Proofs.C04ChartsAux
open Yau Yau.Blueprint Yau.LeafProofs.L12Aux
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

section Gram
variable {n : ℕ} {V : Type*} [AddCommGroup V] [TopologicalSpace V] [Module ℂ V]

def hermitianGram (h : HermitianInnerProduct V) (D : ComplexVector n →L[ℂ] V) : Herm n :=
  fun a b => h.toFun (D (stdVec a)) (D (stdVec b))

theorem hermitianGram_isHermitian (h : HermitianInnerProduct V) (D : ComplexVector n →L[ℂ] V) :
    (hermitianGram h D).IsHermitian := by
  ext a b
  exact (h.conjugate_symmetric _ _).symm

theorem hermitianGram_quadratic (h : HermitianInnerProduct V) (D : ComplexVector n →L[ℂ] V)
    (x : Fin n → ℂ) :
    star x ⬝ᵥ (hermitianGram h D *ᵥ x) =
      h.toFun (D (WithLp.toLp 2 x)) (D (WithLp.toLp 2 x)) := by
  have hsum : D (WithLp.toLp 2 x) = ∑ i, x i • D (stdVec i) := by
    have hh := congrArg D (sum_stdVec (WithLp.toLp 2 x))
    simpa only [map_sum, map_smul, PiLp.toLp_apply] using hh.symm
  rw [hsum, hermitian_sum_left]
  simp_rw [hermitian_sum_right, HermitianInnerProduct.map_smul_left,
    HermitianInnerProduct.map_smul_right]
  simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum, hermitianGram]

theorem identity_quadratic (x : Fin n → ℂ) :
    star x ⬝ᵥ ((1 : Herm n) *ᵥ x) = ⟪WithLp.toLp 2 x, WithLp.toLp 2 x⟫_ℂ := by
  simp only [Matrix.one_mulVec, dotProduct, Pi.star_apply, PiLp.inner_apply,
    PiLp.toLp_apply, RCLike.inner_apply]
  apply Finset.sum_congr rfl
  intro i _
  exact mul_comm _ _

theorem hermitianGram_order_of_quadratic (h : HermitianInnerProduct V)
    (D : ComplexVector n →L[ℂ] V) (c C : ℝ)
    (hbound : ∀ v, c * ‖v‖^2 ≤ (h.toFun (D v) (D v)).re ∧
      (h.toFun (D v) (D v)).re ≤ C * ‖v‖^2) :
    HermLE ((c : ℂ) • (1 : Herm n)) (hermitianGram h D) ∧
      HermLE (hermitianGram h D) ((C : ℂ) • (1 : Herm n)) := by
  have hherm := hermitianGram_isHermitian h D
  have hscalar (a : ℝ) : ((a : ℂ) • (1 : Herm n)).IsHermitian :=
    Matrix.isHermitian_one.smul (by simp [IsSelfAdjoint])
  constructor
  · apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
    refine ⟨hherm.sub (hscalar c), ?_⟩
    intro x
    have hrx : (⟪(WithLp.toLp 2 x : ComplexVector n), WithLp.toLp 2 x⟫_ℂ).re =
        ‖(WithLp.toLp 2 x : ComplexVector n)‖^2 := (norm_sq_eq_re_inner (𝕜 := ℂ) _).symm
    have hix : (⟪(WithLp.toLp 2 x : ComplexVector n), WithLp.toLp 2 x⟫_ℂ).im = 0 :=
      inner_self_im (𝕜 := ℂ) _
    rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, dotProduct_smul,
      hermitianGram_quadratic, identity_quadratic]
    apply Complex.nonneg_iff.mpr
    have hb := (hbound (WithLp.toLp 2 x)).1
    constructor
    · simpa only [Complex.sub_re, smul_eq_mul, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, sub_zero, hrx] using sub_nonneg.mpr hb
    · simp only [Complex.sub_im, h.self_adjoint, smul_eq_mul, Complex.mul_im,
        Complex.ofReal_im, zero_mul, Complex.ofReal_re, hix, mul_zero, add_zero, sub_zero]
  · apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
    refine ⟨(hscalar C).sub hherm, ?_⟩
    intro x
    have hrx : (⟪(WithLp.toLp 2 x : ComplexVector n), WithLp.toLp 2 x⟫_ℂ).re =
        ‖(WithLp.toLp 2 x : ComplexVector n)‖^2 := (norm_sq_eq_re_inner (𝕜 := ℂ) _).symm
    have hix : (⟪(WithLp.toLp 2 x : ComplexVector n), WithLp.toLp 2 x⟫_ℂ).im = 0 :=
      inner_self_im (𝕜 := ℂ) _
    rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, dotProduct_smul,
      hermitianGram_quadratic, identity_quadratic]
    apply Complex.nonneg_iff.mpr
    have hb := (hbound (WithLp.toLp 2 x)).2
    constructor
    · simpa only [Complex.sub_re, smul_eq_mul, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, sub_zero, hrx] using sub_nonneg.mpr hb
    · simp only [Complex.sub_im, h.self_adjoint, smul_eq_mul, Complex.mul_im,
        Complex.ofReal_im, zero_mul, Complex.ofReal_re, hix, mul_zero, add_zero, zero_sub, neg_zero]

end Gram
end Yau.Proofs.C04ChartsAux
