import Yau.Proofs.F05BootstrapClosedProductDifferentiation
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! Assembling a joint derivative from its actual spatial/time fields
preserves every finite joint regularity order. -/

open Set
open scoped ContDiff
noncomputable section
namespace Yau.Proofs.F05Aux
variable {D E V : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem F05_product_derivative_contDiff {k : ℕ} {Q : Set D}
    {A : D → E →L[ℝ] V} {J : D → V}
    (hA : ContDiffOn ℝ k A Q) (hJ : ContDiffOn ℝ k J Q) :
    ContDiffOn ℝ k (fun z => F05ProductDerivative (A z) (J z)) Q := by
  let L : V →L[ℝ] (ℝ →L[ℝ] V) := ContinuousLinearMap.smulRightL ℝ ℝ V (1 : ℝ →L[ℝ] ℝ)
  exact (hA.clm_comp contDiffOn_const).add
    ((L.contDiff.comp_contDiffOn hJ).clm_comp contDiffOn_const)

end Yau.Proofs.F05Aux
