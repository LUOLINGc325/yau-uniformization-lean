import Yau.Proofs.C04BoundedGeometryChartsNormalComplexStructure
import Yau.Proofs.C04NormalModelJets

/-! The model Gram form and complex conjugation are the actual real pullbacks. -/
noncomputable section
open scoped Topology Manifold ContDiff InnerProductSpace
namespace Yau.Proofs.C04ChartsAux
open Yau Yau.LeafProofs.L21Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 5

theorem complexVector_real_inner (a b : ComplexVector n) :
    ⟪a, b⟫_ℝ = (⟪a, b⟫_ℂ).re := by
  simp only [PiLp.inner_apply, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact real_inner_eq_re_inner ℂ (a i) (b i)

theorem stdComplex_norm_le (n : ℕ) : ‖stdComplex n‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro v
  simp only [stdComplex_apply, norm_smul, Complex.norm_I, one_mul]
  exact le_rfl

theorem realPullbackJ_eq_normalModelComplex (g : SmoothMetric M) (hk : KahlerClosed g.form)
    (p : M.Carrier) (U : ComplexVector n ≃L[ℂ] TangentVector M p) :
    realPullbackJ (unitaryExponential g p U) =
      fun y => C04Aux.normalModelComplex (stdComplex n) (radialCoframe g p U y) := by
  funext y
  apply ContinuousLinearMap.ext
  intro w
  exact realPullbackJ_eq_radial_conjugation g hk p U y w

theorem realPullbackMetric_eq_normalModelMetric (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃L[ℂ] TangentVector M p)
    (hU : ∀ i j, (g.form p).toFun (U (stdVec i)) (U (stdVec j)) =
      (1 : Matrix (Fin n) (Fin n) ℂ) i j) (v : ComplexVector n) (a b : RIdx n) :
    realPullbackMetric g.form (unitaryExponential g p U) v a b =
      C04Aux.normalModelMetric (radialCoframe g p U v) (realVec a) (realVec b) := by
  rw [realPullbackMetric_eq_radial_gram g p U hU, C04Aux.normalModelMetric_apply,
    complexVector_real_inner]

theorem realPullbackMetric_entry_jet_le (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃L[ℂ] TangentVector M p)
    (hU : ∀ i j, (g.form p).toFun (U (stdVec i)) (U (stdVec j)) =
      (1 : Matrix (Fin n) (Fin n) ℂ) i j) (v : ComplexVector n) (a b : RIdx n) (m : ℕ) :
    ‖iteratedFDeriv ℝ m (fun y => realPullbackMetric g.form (unitaryExponential g p U) y a b) v‖ ≤
      ‖realVec b‖ * ‖realVec a‖ * ‖iteratedFDeriv ℝ m
        (fun y => C04Aux.normalModelMetric (radialCoframe g p U y)) v‖ := by
  have hG := C04Aux.normal_model_metric_contDiff _ (radialCoframe_smooth g p U)
  have h₁ := norm_iteratedFDeriv_clm_apply_const
    (c := realVec a) (hG.contDiffAt (x := v)) (by simp : (m : ℕ∞ω) ≤ ∞)
  have hEval : ContDiff ℝ ∞ (fun y => C04Aux.normalModelMetric (radialCoframe g p U y) (realVec a)) :=
    hG.clm_apply contDiff_const
  have h₂ := norm_iteratedFDeriv_clm_apply_const
    (c := realVec b) (hEval.contDiffAt (x := v)) (by simp : (m : ℕ∞ω) ≤ ∞)
  have heq : (fun y => realPullbackMetric g.form (unitaryExponential g p U) y a b) =
      fun y => C04Aux.normalModelMetric (radialCoframe g p U y) (realVec a) (realVec b) :=
    funext (fun y => realPullbackMetric_eq_normalModelMetric g p U hU y a b)
  rw [heq]
  exact h₂.trans (by nlinarith [mul_nonneg (norm_nonneg (realVec b)) (sub_nonneg.mpr h₁)])

end Yau.Proofs.C04ChartsAux
