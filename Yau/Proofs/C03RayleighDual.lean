import Yau.Proofs.C03RayleighExtrema

/-! Covectors are normalized in the actual inverse-transpose, conjugated-coordinate convention. -/
noncomputable section
open scoped Matrix ComplexOrder Topology
namespace Yau.Proofs.C03Aux.Rayleigh
open Yau Yau.Blueprint
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

def normalizedCovector (lam : ℝ) (e : ComplexVector n) : Covector n :=
  (Real.sqrt lam : ℂ) • innerSL ℂ e

theorem normalizedCovector_apply (lam : ℝ) (e v : ComplexVector n) :
    normalizedCovector lam e v = (Real.sqrt lam : ℂ) * inner ℂ e v := rfl

theorem normalizedCovector_norm (lam : ℝ) (e : ComplexVector n) (he : ‖e‖ = 1) :
    ‖normalizedCovector lam e‖ = Real.sqrt lam := by
  rw [normalizedCovector, norm_smul, innerSL_apply_norm, he]
  simp [Complex.norm_real, Real.sqrt_nonneg]

theorem normalizedCovector_coordinates (lam : ℝ) (e : ComplexVector n) :
    WithLp.toLp 2 (fun i => normalizedCovector lam e (stdVec i)) =
      WithLp.toLp 2 (star (WithLp.ofLp ((Real.sqrt lam : ℂ) • e))) := by
  ext i
  simp [normalizedCovector, stdVec, EuclideanSpace.inner_single_right,
    EuclideanSpace.single, star_mul, mul_comm]

theorem dualNormMat_conjugate (H : Herm n) (v : ComplexVector n) :
    dualNormMat H (WithLp.toLp 2 (star (WithLp.ofLp v))) = quadratic H⁻¹ v := by
  unfold dualNormMat quadratic
  simp only [star_star, dotProduct, Matrix.mulVec, Matrix.transpose_apply,
    Finset.mul_sum, Pi.star_apply]
  rw [Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem quadratic_of_eigenvector (H : Herm n) (v : ComplexVector n) (lam : ℝ)
    (hlam : operator H v = (lam : ℂ) • v) : quadratic H v = lam * ‖v‖ ^ 2 := by
  rw [quadratic_eq_inner, hlam, inner_smul_right]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have he : (inner ℂ v v).re = ‖v‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) v
  rw [he]

theorem inverse_eigenvector (H : Herm n) (hH : H.PosDef) (v : ComplexVector n) (lam : ℝ)
    (hlam : lam ≠ 0) (hv : operator H v = (lam : ℂ) • v) :
    operator H⁻¹ v = ((lam⁻¹ : ℝ) : ℂ) • v := by
  have hi : H⁻¹ * H = 1 := Matrix.nonsing_inv_mul H (hH.isUnit.map Matrix.detMonoidHom)
  have hcomp : operator H⁻¹ (operator H v) = v := by
    change WithLp.toLp 2 (H⁻¹ *ᵥ (H *ᵥ WithLp.ofLp v)) = v
    rw [Matrix.mulVec_mulVec, hi, Matrix.one_mulVec, WithLp.toLp_ofLp]
  rw [hv, map_smul] at hcomp
  have hn : (lam : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hlam
  calc
    operator H⁻¹ v = (lam : ℂ)⁻¹ • ((lam : ℂ) • operator H⁻¹ v) := by
      rw [smul_smul, inv_mul_cancel₀ hn, one_smul]
    _ = (lam : ℂ)⁻¹ • v := congrArg ((lam : ℂ)⁻¹ • ·) hcomp
    _ = ((lam⁻¹ : ℝ) : ℂ) • v := by rw [Complex.ofReal_inv]

theorem normalizedCovector_dualNorm (H : Herm n) (hH : H.PosDef)
    (e : ComplexVector n) (lam : ℝ) (he : ‖e‖ = 1) (hlam : 0 < lam)
    (heig : operator H e = (lam : ℂ) • e) :
    dualNormMat H (WithLp.toLp 2 (fun i => normalizedCovector lam e (stdVec i))) = 1 := by
  rw [normalizedCovector_coordinates, dualNormMat_conjugate]
  let v : ComplexVector n := (Real.sqrt lam : ℂ) • e
  have hinv := inverse_eigenvector H hH e lam hlam.ne' heig
  have hv : operator H⁻¹ v = ((lam⁻¹ : ℝ) : ℂ) • v := by
    dsimp only [v]
    rw [map_smul, hinv, smul_smul, smul_smul, mul_comm]
  rw [quadratic_of_eigenvector H⁻¹ v (lam⁻¹) hv]
  have hnorm : ‖v‖ = Real.sqrt lam := by
    dsimp only [v]
    rw [norm_smul, he]
    simp [Complex.norm_real, Real.sqrt_nonneg]
  rw [hnorm, Real.sq_sqrt hlam.le, inv_mul_cancel₀ hlam.ne']

end Yau.Proofs.C03Aux.Rayleigh
