import Yau.Geometry.Calculus
import Mathlib.Analysis.Calculus.FDeriv.CompCLM

open scoped Topology ContDiff
open Filter

noncomputable section

namespace Yau.NodeProofs.P03Aux

/-- The inclusion of the spatial directions into space and parameter. -/
def spatialInjection (n : ℕ) : ComplexVector n →L[ℝ] ComplexVector n × ℝ :=
  (ContinuousLinearMap.id ℝ (ComplexVector n)).prod 0

@[simp] theorem spatialInjection_apply {n : ℕ} (v : ComplexVector n) :
    spatialInjection n v = (v, 0) := rfl

/-- Restricting the actual joint Hessian to a fixed parameter restricts both
of its directions to the spatial inclusion. -/
theorem spatial_secondFDeriv {n : ℕ} (g : ComplexVector n × ℝ → ℝ)
    (z v w : ComplexVector n) (ε : ℝ) (hg : ContDiffAt ℝ 2 g (z, ε)) :
    fderiv ℝ (fderiv ℝ (fun y => g (y, ε))) z v w =
      fderiv ℝ (fderiv ℝ g) (z, ε) (v, 0) (w, 0) := by
  let J := spatialInjection n
  have ht (y : ComplexVector n) : HasFDerivAt (fun x : ComplexVector n => (x, ε)) J y := by
    exact (hasFDerivAt_id y).prodMk (hasFDerivAt_const ε y)
  have hNear : ∀ᶠ p in 𝓝 (z, ε), DifferentiableAt ℝ g p := by
    filter_upwards [hg.eventually (by norm_num)] with p hp
    exact hp.differentiableAt (by norm_num)
  have he : fderiv ℝ (fun y => g (y, ε)) =ᶠ[𝓝 z]
      (fun y => (fderiv ℝ g (y, ε)).comp J) := by
    filter_upwards [(ht z).continuousAt.eventually hNear] with y hy
    exact (hy.hasFDerivAt.comp y (ht y)).fderiv
  have hD := ((hg.fderiv_right (m := 1) (by norm_num)).differentiableAt
    (by norm_num)).hasFDerivAt
  let C : (ComplexVector n × ℝ →L[ℝ] ℝ) →L[ℝ] (ComplexVector n →L[ℝ] ℝ) :=
    (ContinuousLinearMap.compL ℝ (ComplexVector n) (ComplexVector n × ℝ) ℝ).flip J
  have hc := C.hasFDerivAt.comp z (hD.comp z (ht z))
  rw [he.fderiv_eq]
  have hce : fderiv ℝ (fun y => (fderiv ℝ g (y, ε)).comp J) z =
      C.comp ((fderiv ℝ (fderiv ℝ g) (z, ε)).comp J) := by
    exact hc.fderiv
  rw [hce]
  rfl

end Yau.NodeProofs.P03Aux
