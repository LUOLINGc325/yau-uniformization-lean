import Yau.Proofs.P06HodgeRegularityCanonicalChart
import Yau.Proofs.P06HodgeRegularityJetClosedGraph

/-! Every actual spatial jet of fixed positive-time Hodge smoothing is
a bounded linear map from the original complete Hilbert form space. -/
noncomputable section
open MeasureTheory Filter Module
open scoped Topology ContDiff BoundedContinuousFunction

namespace Yau.NodeProofs.P06Aux
open Yau Yau.LeafProofs Yau.LeafProofs.L03

variable {n k : ℕ} {M : ComplexManifold n}

def hodgeCanonicalChartJetCLM {α : Type} [Fintype α] [DecidableEq α]
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (a : ℝ) (ha : 0 < a) (x : M.Carrier) (b : Basis α ℝ (HodgeJets.Fiber n k))
    (χ : ComplexVector n → ℝ) (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hχO : tsupport χ ⊆ chartTarget x) (c : α) (w : List (RIdx n)) :
    L2FormHilbert g μ k →L[ℝ] (ComplexVector n →ᵇ ℝ) := by
  letI : (lebesgueC n).IsAddHaarMeasure := by rw [lebesgueC_eq_volume]; infer_instance
  letI : (lebesgueC n).IsOpenPosMeasure := by rw [lebesgueC_eq_volume]; infer_instance
  let R := hodgeCanonicalChart g μ hμ a ha x b χ hχ hcχ hχO c
  have hR := hodgeCanonicalChart_properties g μ hμ a ha x b χ hχ hcχ hχO c
  exact regularitySmoothLiftJetCLM (lebesgueC n)
    ((chartProjection g μ hμ x χ hχ hcχ hχO (b.coord c).toContinuousLinearMap).comp
      (hodgeHeatHilbert g μ hμ k a)) R (fun f => (hR f).1) hcχ (fun f => (hR f).2.1)
    (fun f => (hR f).2.2) (realModelBasis n) w

theorem hodgeCanonicalChartJetCLM_apply {α : Type} [Fintype α] [DecidableEq α]
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (a : ℝ) (ha : 0 < a) (x : M.Carrier) (b : Basis α ℝ (HodgeJets.Fiber n k))
    (χ : ComplexVector n → ℝ) (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hχO : tsupport χ ⊆ chartTarget x) (c : α) (w : List (RIdx n))
    (f : L2FormHilbert g μ k) (z : ComplexVector n) :
    hodgeCanonicalChartJetCLM g μ hμ a ha x b χ hχ hcχ hχO c w f z =
      regularityCoefficientWord (realModelBasis n) w
        (hodgeCanonicalChart g μ hμ a ha x b χ hχ hcχ hχO c f) z := rfl

end Yau.NodeProofs.P06Aux
