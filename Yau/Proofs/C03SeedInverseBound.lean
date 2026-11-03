import Yau.Proofs.C03SeedDbarBounds
import Yau.Proofs.C03QOne

/-! The genuine q=1 variational inverse of the actual scalar source
has no Jacobian factor and has a uniform target-annulus bound. -/

noncomputable section
open Set Metric
open scoped Topology ContDiff Manifold Matrix ComplexOrder ENNReal
namespace Yau.Proofs.C03Aux
open Yau Yau.Blueprint Yau.LeafProofs L14Aux L17Aux Yau.NodeProofs.E01Aux
open Yau.Proofs.P04Aux BundleDbar
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

theorem differential_quadratic_lower (D : ComplexVector n →L[ℂ] ComplexVector n)
    (Hs Ht : Herm n) (d : ℝ)
    (hcong : Hs = (linearMatrix D)ᴴ * Ht * linearMatrix D)
    (hlo : HermLE ((d : ℂ) • (1 : Herm n)) Ht) (v : ComplexVector n) :
    d * ‖D v‖ ^ 2 ≤ ellipsoidQuadratic Hs v := by
  have H := ellipsoidQuadratic_nonneg hlo (D v)
  rw [ellipsoidQuadratic_sub, ellipsoidQuadratic_real_smul, ellipsoidQuadratic_one] at H
  have hq : ellipsoidQuadratic Hs v = ellipsoidQuadratic Ht (D v) := by
    rw [hcong]
    unfold ellipsoidQuadratic
    rw [congruence_quadratic, linearMatrix_mulVec]
  linarith

theorem sheetSeed_inverse_bound (hn : 1 ≤ n) (φ : ComplexVector n → ℝ)
    (O : Set (ComplexVector n)) (hO : IsOpen O)
    (θ : ComplexVector n → ComplexVector n) (δ : ℝ) (hδ : 0 < δ)
    (η : Covector n) (w0 z : ComplexVector n) (hz : z ∈ O)
    (hθ : DifferentiableAt ℂ θ z) (hpoint : ‖θ z - w0‖ ≤ δ)
    (Ht : Herm n) (hHt : Ht.PosDef) (d U G : ℝ) (hd : 0 < d) (hU : 0 ≤ U) (hG : 0 ≤ G)
    (hη : ‖η‖ ≤ Real.sqrt U)
    (hlo : HermLE ((d : ℂ) • (1 : Herm n)) Ht)
    (hcut : ‖seedCutoffDbar δ hδ (θ z - w0)‖ ≤ G)
    (hJ : IsUnit (linearMatrix (fderiv ℂ θ z)).det)
    (hLevi : HermLE ((linearMatrix (fderiv ℂ θ z))ᴴ * Ht *
      linearMatrix (fderiv ℂ θ z)) (leviC φ z)) :
    inverseCurvatureNormSq (r := 1)
      (CanonicalCoefficients (ComplexEuclideanManifold n hn))
      (FlatComplete.euclideanCompleteMetric n hn).form flatMetric φ
      (scalarSeedDbar hn (sheetSeed O θ δ hδ η w0)) z ≤
      ENNReal.ofReal ((2 : ℝ) ^ n * (U * δ ^ 2) * (G ^ 2 / d)) := by
  have hb := QOne.inverseCurvatureNormSq_pullback_le hn φ
    (scalarSeedDbar hn (sheetSeed O θ δ hδ η w0)) z
    (linearMatrix (fderiv ℂ θ z)) Ht hJ hHt 1 (by norm_num)
    (by simpa only [Complex.ofReal_one, one_smul] using hLevi)
    (η (θ z - w0)) (seedCutoffDbar δ hδ (θ z - w0))
    (sheetSeed_actual_source_vector hn O hO θ δ hδ η w0 z hz hθ)
  have hs : ‖η (θ z - w0)‖ ≤ Real.sqrt U * δ :=
    (η.le_opNorm _).trans
      (mul_le_mul hη hpoint (norm_nonneg _) (Real.sqrt_nonneg U))
  have hs2 : ‖η (θ z - w0)‖ ^ 2 ≤ U * δ ^ 2 := by
    have H := mul_self_le_mul_self (norm_nonneg _) hs
    have H' : ‖η (θ z - w0)‖ ^ 2 ≤ (Real.sqrt U * δ) ^ 2 := by
      simpa only [pow_two] using H
    simpa only [mul_pow, Real.sq_sqrt hU] using H'
  have hq := inverse_quadratic_le_of_matrix_lower Ht hHt d hd hlo
    (seedCutoffDbar δ hδ (θ z - w0))
  have hqG : ellipsoidQuadratic Ht⁻¹ (seedCutoffDbar δ hδ (θ z - w0)) ≤ G ^ 2 / d := by
    have H := mul_self_le_mul_self (norm_nonneg _) hcut
    exact hq.trans ((div_le_div_iff_of_pos_right hd).mpr (by simpa only [pow_two] using H))
  apply hb.trans
  apply ENNReal.ofReal_le_ofReal
  simp only [div_one]
  have hq0 := ellipsoidQuadratic_nonneg hHt.inv.posSemidef (seedCutoffDbar δ hδ (θ z - w0))
  calc
    (2 : ℝ) ^ n * (‖η (θ z - w0)‖ ^ 2 *
        ellipsoidQuadratic Ht⁻¹ (seedCutoffDbar δ hδ (θ z - w0))) ≤
        (2 : ℝ) ^ n * ((U * δ ^ 2) * (G ^ 2 / d)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul hs2 hqG hq0 (by positivity)) (by positivity)
    _ = _ := by ring

end Yau.Proofs.C03Aux
