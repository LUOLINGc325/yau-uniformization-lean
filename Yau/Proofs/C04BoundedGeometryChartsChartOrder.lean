import Yau.Proofs.C04BoundedGeometryChartsChartNorms
import Yau.Proofs.C04BoundedGeometryChartsGramOrder
import Yau.Proofs.C04BoundedGeometryChartsActualMetric

/-! Fixed positive upper and lower bounds for the actual Hermitian pullback. -/
noncomputable section
open scoped Topology Manifold ContDiff InnerProductSpace Matrix ComplexOrder
namespace Yau.Proofs.C04ChartsAux
open Yau Yau.Blueprint Yau.LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 5

theorem normalChartMap_pullback_order (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃L[ℂ] TangentVector M p)
    (hU : ∀ i j, (g.form p).toFun (U (stdVec i)) (U (stdVec j)) =
      (1 : Matrix (Fin n) (Fin n) ℂ) i j)
    (e : OpenPartialHomeomorph (ComplexVector n) (ComplexVector n))
    (L : ComplexVector n →L[ℝ] ComplexVector n) (d : ℝ) (z : ComplexVector n)
    (hparam : DifferentiableAt ℝ (normalizedInverseParameter e L d) z)
    (hf : MDifferentiableAt (ComplexModel n) (ComplexModel n) (normalChartMap g p U e L d) z)
    (hA : ‖radialCoframe g p U (normalizedInverseParameter e L d z) -
      ContinuousLinearMap.id ℝ (ComplexVector n)‖ ≤ (1 / 4 : ℝ))
    (hD : ∀ v, (3 / 5 : ℝ) * ‖v‖ ≤ ‖fderiv ℝ (normalizedInverseParameter e L d) z v‖ ∧
      ‖fderiv ℝ (normalizedInverseParameter e L d) z v‖ ≤ (5 / 3 : ℝ) * ‖v‖) :
    HermLE (((1 / 16 : ℝ) : ℂ) • (1 : Herm n))
      (pullbackMat g.form (normalChartMap g p U e L d) z) ∧
      HermLE (pullbackMat g.form (normalChartMap g p U e L d) z)
        ((16 : ℂ) • (1 : Herm n)) := by
  apply hermitianGram_order_of_quadratic
    (g.form (normalChartMap g p U e L d z))
    (mfderiv (ComplexModel n) (ComplexModel n) (normalChartMap g p U e L d) z)
    (1 / 16) 16
  intro v
  have hform := normalChartMap_pullback_re g p U hU e L d z v v hparam hf
  rw [C04Aux.normalModelMetric_apply, real_inner_self_eq_norm_sq] at hform
  have hb := normal_gram_composition_norm_bounds
    (radialCoframe g p U (normalizedInverseParameter e L d z))
    (fderiv ℝ (normalizedInverseParameter e L d) z) hA hD v
  have hn := norm_nonneg (radialCoframe g p U (normalizedInverseParameter e L d z)
    (fderiv ℝ (normalizedInverseParameter e L d) z v))
  have hv := norm_nonneg v
  have hl := (sq_le_sq₀ (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 4) hv) hn).mpr hb.1
  have hu := (sq_le_sq₀ hn (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hv)).mpr hb.2
  have hpair : ((g.form (normalChartMap g p U e L d z)).toFun
      (mfderiv (ComplexModel n) (ComplexModel n) (normalChartMap g p U e L d) z v)
      (mfderiv (ComplexModel n) (ComplexModel n) (normalChartMap g p U e L d) z v)).re =
      ‖radialCoframe g p U (normalizedInverseParameter e L d z)
        (fderiv ℝ (normalizedInverseParameter e L d) z v)‖^2 := by
    linarith only [hform]
  constructor
  · calc
      (1 / 16 : ℝ) * ‖v‖^2 = ((1 / 4 : ℝ) * ‖v‖)^2 := by ring
      _ ≤ _ := hl
      _ = _ := hpair.symm
  · calc
      _ = _ := hpair
      _ ≤ (4 * ‖v‖)^2 := hu
      _ = 16 * ‖v‖^2 := by ring

end Yau.Proofs.C04ChartsAux
