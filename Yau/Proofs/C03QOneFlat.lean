import Yau.Proofs.P04PoleCurvatureEnergy
import Yau.Proofs.C03QOneMatrix

/-! Exact q=1 coefficient and energy factors for the half-flat background. -/
noncomputable section
open scoped Matrix ComplexOrder Manifold ENNReal
namespace Yau.Proofs.C03Aux.QOne
open Yau Yau.Blueprint Yau.NodeProofs.E01Aux Yau.Proofs.P04Aux BundleDbar
variable {n : ℕ} {M : ComplexManifold n}

theorem half_gram_inverse :
    (((1 / 2 : ℝ) : ℂ) • (1 : Herm n))⁻¹ = (2 : ℂ) • (1 : Herm n) := by
  apply Matrix.inv_eq_left_inv
  rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul]
  norm_num

theorem half_gram_inverse_det :
    (((1 / 2 : ℝ) : ℂ) • (1 : Herm n))⁻¹.det = ((2 : ℝ) ^ n : ℂ) := by
  rw [half_gram_inverse, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]
  norm_cast

theorem half_flat_coefficientInner (g : HermitianField M) (x : M.Carrier)
    (hg : gMat g x = ((1 / 2 : ℝ) : ℂ) • (1 : Herm n))
    (F V : Fin n → Fin 1 → ℂ) :
    coefficientInner (r := 1) (CanonicalCoefficients M) g flatMetric x F V =
      ((2 : ℝ) ^ (n + 1) : ℂ) * (star (fun i => F i 0) ⬝ᵥ (fun i => V i 0)) := by
  classical
  unfold coefficientInner
  rw [hg, half_gram_inverse_det, half_gram_inverse]
  simp only [flat_metricMatrix, Fin.sum_univ_one, Matrix.one_apply, Matrix.smul_apply,
    smul_eq_mul, mul_one, mul_ite, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true]
  simp only [dotProduct, Pi.star_apply]
  rw [pow_succ, mul_assoc]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  norm_num only [Complex.ofReal_ofNat]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  ring

theorem half_flat_curvatureEnergy (g : HermitianField M) (φ : M.Carrier → ℝ)
    (x : M.Carrier) (hg : gMat g x = ((1 / 2 : ℝ) : ℂ) • (1 : Herm n))
    (V : Fin n → Fin 1 → ℂ) :
    curvatureEnergy (r := 1) (CanonicalCoefficients M) g flatMetric φ x V =
      (2 : ℝ) ^ (n + 2) *
        ellipsoidQuadratic (levi φ x) (WithLp.toLp 2 (fun i => V i 0)) := by
  rw [flat_curvatureEnergy, hg, half_gram_inverse_det, half_gram_inverse]
  have hv : (fun i => ∑ j, ((2 : ℂ) • (1 : Herm n)) i j * V j 0) =
      WithLp.ofLp ((2 : ℂ) • WithLp.toLp 2 (fun i => V i 0)) := by
    funext i
    simp [Matrix.smul_apply, Matrix.one_apply]
  rw [hv]
  simp only [Complex.ofReal_ofNat]
  rw [show ((2 : ℂ) ^ n).re = (2 : ℝ) ^ n by norm_cast]
  change (2 : ℝ) ^ n * ellipsoidQuadratic (levi φ x)
    ((2 : ℂ) • WithLp.toLp 2 (fun i => V i 0)) = _
  rw [ellipsoidQuadratic_complex_smul]
  norm_num [pow_add]
  ring

end Yau.Proofs.C03Aux.QOne
