import Yau.Proofs.P06HodgeRegularityCanonicalJets
import Yau.Proofs.P06HodgeRegularityJointLift

/-! Actual fixed positive-time Hodge smoothing applied to a Hilbert C∞
curve is jointly smooth in the original space and time coordinates. -/
noncomputable section
open MeasureTheory Filter Module
open scoped Topology ContDiff BoundedContinuousFunction

namespace Yau.NodeProofs.P06Aux
open Yau Yau.LeafProofs Yau.LeafProofs.L03

variable {n k : ℕ} {M : ComplexManifold n}

theorem hodgeCanonicalChart_joint_contDiffOn {α : Type} [Fintype α] [DecidableEq α]
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (a : ℝ) (ha : 0 < a) (x : M.Carrier) (b : Basis α ℝ (HodgeJets.Fiber n k))
    (χ : ComplexVector n → ℝ) (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hχO : tsupport χ ⊆ chartTarget x) (c : α)
    {T : Set ℝ} (hT : IsOpen T) (h : ℝ → L2FormHilbert g μ k) (hh : ContDiffOn ℝ ∞ h T) :
    ContDiffOn ℝ ∞ (fun p : ComplexVector n × ℝ =>
      hodgeCanonicalChart g μ hμ a ha x b χ hχ hcχ hχO c (h p.2) p.1) (Set.univ ×ˢ T) := by
  have hR := hodgeCanonicalChart_properties g μ hμ a ha x b χ hχ hcχ hχO c
  have hc := regularityJetCurve_contDiffOn (realModelBasis n)
    (hodgeCanonicalChart g μ hμ a ha x b χ hχ hcχ hχO c) (fun f => (hR f).1)
    (hodgeCanonicalChartJetCLM g μ hμ a ha x b χ hχ hcχ hχO c)
    (hodgeCanonicalChartJetCLM_apply g μ hμ a ha x b χ hχ hcχ hχO c)
    hT hh []
  have heq : regularityJetCurve (hodgeCanonicalChartJetCLM g μ hμ a ha x b χ hχ hcχ hχO c) h [] =
      fun p : ComplexVector n × ℝ => hodgeCanonicalChart g μ hμ a ha x b χ hχ hcχ hχO c (h p.2) p.1 := by
    funext p
    exact hodgeCanonicalChartJetCLM_apply g μ hμ a ha x b χ hχ hcχ hχO c [] (h p.2) p.1
  rw [heq] at hc
  exact hc

end Yau.NodeProofs.P06Aux
