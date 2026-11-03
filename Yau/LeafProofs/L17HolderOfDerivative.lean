import Yau.LeafProofs.L17HolderOfLipschitz
import Yau.LeafProofs.L17BackgroundFunctionSmooth
import Mathlib.Analysis.Calculus.MeanValue

/-! Actual original-chart derivative bounds supply time-independent global Holder elements. -/

noncomputable section

open Set Metric
open scoped ContDiff Manifold

namespace Yau.LeafProofs.L17HolderAux

open Yau.LeafProofs.L17Aux

variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}

theorem chart_lipschitz_of_derivative_bound
    (P : UniformChartPartition g) {L : ℝ} {f : M.Carrier → ℝ} (hf : SmoothFn f)
    (hD : ∀ p z, z ∈ ball (0 : ComplexVector n) P.radius →
      ‖fderiv ℝ (fun w => f (P.charts.chart p w)) z‖ ≤ L / P.radius)
    (p : M.Carrier) (z w : ↥(ball (0 : ComplexVector n) P.radius)) :
    |f (P.charts.chart p w) - f (P.charts.chart p z)| ≤
      (L / P.radius) * ‖(w : ComplexVector n) - z‖ := by
  have hdiff : ∀ y ∈ ball (0 : ComplexVector n) P.radius,
      DifferentiableAt ℝ (fun v => f (P.charts.chart p v)) y := by
    intro y hy
    apply ((smoothFn_comp_backgroundChart_contDiffOn P.charts hf p).contDiffAt
      (isOpen_ball.mem_nhds ((ball_subset_ball P.radius_lt.le) hy))).differentiableAt
    simp
  simpa only [Real.norm_eq_abs] using Convex.norm_image_sub_le_of_norm_fderiv_le
    hdiff (hD p) (convex_ball (0 : ComplexVector n) P.radius) z.property w.property

def timeIndependentOfDerivativeBound
    (P : UniformChartPartition g) {T γ A L : ℝ} (hT : T ≤ P.radius ^ 2)
    (hγ : γ ≤ 1) (hL : 0 ≤ L) (f : M.Carrier → ℝ) (hf : SmoothFn f)
    (hA : ∀ x, |f x| ≤ A)
    (hD : ∀ p z, z ∈ ball (0 : ComplexVector n) P.radius →
      ‖fderiv ℝ (fun w => f (P.charts.chart p w)) z‖ ≤ L / P.radius) :
    HolderSpace P T γ :=
  timeIndependentElement P hT hγ hL f
    (L18Aux.contMDiff_real_of_smoothFn hf).continuous hA
    (chart_lipschitz_of_derivative_bound P hf hD)

theorem timeIndependentOfDerivativeBound_value
    (P : UniformChartPartition g) {T γ A L : ℝ} (hT : T ≤ P.radius ^ 2)
    (hγ : γ ≤ 1) (hL : 0 ≤ L) (f : M.Carrier → ℝ) (hf : SmoothFn f)
    (hA : ∀ x, |f x| ≤ A)
    (hD : ∀ p z, z ∈ ball (0 : ComplexVector n) P.radius →
      ‖fderiv ℝ (fun w => f (P.charts.chart p w)) z‖ ≤ L / P.radius)
    (q : Cylinder M T) :
    holderFun (timeIndependentOfDerivativeBound P hT hγ hL f hf hA hD) q = f q.1 := rfl

theorem timeIndependentOfDerivativeBound_norm_le
    (P : UniformChartPartition g) {T γ A L : ℝ} (hT : T ≤ P.radius ^ 2)
    (hγ : γ ≤ 1) (hA0 : 0 ≤ A) (hL : 0 ≤ L) (f : M.Carrier → ℝ) (hf : SmoothFn f)
    (hA : ∀ x, |f x| ≤ A)
    (hD : ∀ p z, z ∈ ball (0 : ComplexVector n) P.radius →
      ‖fderiv ℝ (fun w => f (P.charts.chart p w)) z‖ ≤ L / P.radius) :
    ‖timeIndependentOfDerivativeBound P hT hγ hL f hf hA hD‖ ≤
      max A ((3 : ℝ) ^ (1 - γ) * L) :=
  timeIndependentElement_norm_le P hT hγ hA0 hL f _ hA
    (chart_lipschitz_of_derivative_bound P hf hD)

end Yau.LeafProofs.L17HolderAux
