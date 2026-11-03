import Yau.Proofs.C05GradientFlowGeodesic

/-! The displayed covariant Hessian is the actual second differential minus the connection term. -/
noncomputable section
open scoped Topology Manifold ContDiff
namespace Yau.Proofs.C05GradientFlowAux
open Yau Yau.LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

def scalarChartHessian (k : HermitianField M) (f : M.Carrier → ℝ)
    (c : M.Carrier) (z : ComplexVector n) :
    ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ℝ :=
  fderiv ℝ (fderiv ℝ (inChart c f)) z -
    ((ContinuousLinearMap.compL ℝ (ComplexVector n) (ComplexVector n) ℝ
      (fderiv ℝ (inChart c f) z)).comp (chartChristoffelBilin k c z))

theorem scalarChartHessian_apply (k : HermitianField M) (f : M.Carrier → ℝ)
    (c : M.Carrier) (z u v : ComplexVector n) :
    scalarChartHessian k f c z u v =
      fderiv ℝ (fderiv ℝ (inChart c f)) z u v -
        fderiv ℝ (inChart c f) z (chartChristoffelBilin k c z u v) := rfl

theorem scalarChartHessian_basis (k : HermitianField M) (f : M.Carrier → ℝ)
    (c : M.Carrier) (z : ComplexVector n) (hf : ContDiffAt ℝ 2 (inChart c f) z)
    (a b : RIdx n) :
    scalarChartHessian k f c z (realVec a) (realVec b) = realHessInChart k f c z a b := by
  rw [scalarChartHessian_apply, ← rDeriv_rDeriv_eq_hessian hf a b,
    chartChristoffelBilin_basis]
  simp only [map_sum, map_smul, smul_eq_mul, realHessInChart, rDeriv]

theorem realHess_eq_scalarChartHessian (k : HermitianField M) (f : M.Carrier → ℝ)
    (hf : SmoothFn f) (x : M.Carrier) (v w : TangentVector M x) :
    realHess k f x v w = scalarChartHessian k f x (chartPt x x)
      (tangentCoords x x v) (tangentCoords x x w) := by
  have hfx : ContDiffAt ℝ 2 (inChart x f) (chartPt x x) :=
    ((hf x).contDiffAt ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds
      (mem_extChartAt_target x))).of_le (by simp)
  rw [realBilin_eq_sum]
  simp_rw [scalarChartHessian_basis k f x _ hfx]
  unfold realHess
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem realHessInChart_contDiffOn (g : SmoothMetric M) (f : M.Carrier → ℝ)
    (hf : SmoothFn f) (c : M.Carrier) (a b : RIdx n) :
    ContDiffOn ℝ ∞ (fun z => realHessInChart g.form f c z a b) (chartTarget c) := by
  have hO := isOpen_extChartAt_target (I := ComplexModel n) c
  apply (rDeriv_contDiffOn hO (rDeriv_contDiffOn hO (hf c) b) a).sub
  exact ContDiffOn.sum fun q _ => (christoffel_contDiffOn g c q a b).mul
    (rDeriv_contDiffOn hO (hf c) q)

theorem chart_df_velocity_hasDerivAt (k : HermitianField M) (f : M.Carrier → ℝ)
    (c : M.Carrier) (η : ℝ → ComplexVector n × ComplexVector n) (t : ℝ)
    (hf : ContDiffAt ℝ 2 (inChart c f) (η t).1)
    (hη : HasDerivAt η (chartGeodesicSpray k c (η t)) t) :
    HasDerivAt (fun s => fderiv ℝ (inChart c f) (η s).1 (η s).2)
      (scalarChartHessian k f c (η t).1 (η t).2 (η t).2) t := by
  have hZ := hη.fst
  have hV := hη.snd
  change HasDerivAt (fun s => (η s).1) (η t).2 t at hZ
  change HasDerivAt (fun s => (η s).2) (chartGeodesicAcceleration k c (η t).1 (η t).2) t at hV
  rw [chartGeodesicAcceleration_eq] at hV
  have hdf := (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have H := (hdf.hasFDerivAt.comp_hasDerivAt t hZ).clm_apply hV
  convert H using 1 <;>
    first | rfl | simp only [scalarChartHessian_apply, Function.comp_apply, map_neg, sub_eq_add_neg]

end Yau.Proofs.C05GradientFlowAux
