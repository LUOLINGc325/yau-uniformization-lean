import Yau.Proofs.V03ChartKahlerTwoForm
import Yau.Proofs.V03TwoFormPullback

/-! Smoothness of the genuine base metric pullback through actual joint
holomorphic coordinate functions and their original within derivatives. -/

open scoped Manifold Topology ContDiff

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau

theorem fixedBaseTwoForm_contDiffOn {n : ℕ} {M : ComplexManifold n}
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P] [FiniteDimensional ℂ P]
    (g : SmoothMetric M) (x : M.Carrier) {S : Set P} (hS : UniqueDiffOn ℂ S)
    {c : P → ComplexVector n} (hc : ContDiffOn ℂ ∞ c S)
    (hmap : Set.MapsTo c S (chartTarget x)) :
    ContDiffOn ℝ ∞ (fun p => (chartKahlerTwoForm g.form x (c p)).compContinuousLinearMap
      ((fderivWithin ℂ c S p).restrictScalars ℝ)) S := by
  have hA := (matrixKahlerBilinear_contDiffOn (hMat_contDiffOn g x)).comp (hc.restrict_scalars ℝ) hmap
  have hD := hc.fderivWithin hS (m := ∞) (by simp)
  have hT : ContDiffOn ℝ ∞ (fun p => (fderivWithin ℂ c S p).restrictScalars ℝ) S := by
    apply contDiffOn_clm_apply.mpr
    intro v
    exact (hD.clm_apply (contDiffOn_const (c := v))).restrict_scalars ℝ
  have hB := bilinearTwoForm_contDiffOn (pullbackBilinear_contDiffOn hA hT)
  simpa only [bilinearTwoForm_pullback, chartKahlerTwoForm, matrixKahlerTwoForm,
    Function.comp_def] using hB

end Yau.Blueprint.V03Proof
