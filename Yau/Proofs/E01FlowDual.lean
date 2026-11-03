import Yau.Proofs.E01DualOrder
import Yau.Proofs.V03DualNorm
import Yau.Proofs.V03TimeScalars

/-! The original localized flow supplies both dual-norm order and genuine smooth disc costs. -/

noncomputable section
open scoped Manifold Topology ContDiff Matrix ComplexOrder

namespace Yau.NodeProofs.E01Aux
open Yau Yau.Blueprint
open Yau.Blueprint.V03Proof

variable {n : ℕ} {X : KahlerManifold n}

theorem localized_initial_dualNorm_le {o : Pt X} {h : Flow X} {U P ρ : STF X}
    (hloc : LocalizedFlow X o h U P ρ) (t : ℝ) (ht : 0 ≤ t)
    (y : Pt X) (ξ : Covector n) :
    dualNorm X.metric.form y ξ ≤ dualNorm (h t) y ξ := by
  exact dualNormMat_antitone (gMat (h t) y) (gMat X.metric.form y)
    (gMat_posDef (h t) y) (gMat_posDef X.metric.form y)
    (hloc.2.2.2.2.1 t ht y) (covectorCoords y y ξ)

theorem localized_disc_cost_contDiffOn {o : Pt X} {h : Flow X} {U P ρ : STF X}
    (hloc : LocalizedFlow X o h U P ρ)
    {f : ℂ → Pt X} {ξ : ℂ → Covector n} (hd : IsCotangentDisc f ξ)
    {w : ℂ → ℂ} (hw : ContDiffOn ℂ ∞ w (Metric.closedBall 0 1))
    (s : ℝ) (hs : 0 < s) :
    ContDiffOn ℝ ∞ (fun ζ => dualNorm (h (s * Real.exp (2 * (w ζ).re))) (f ζ) (ξ ζ))
      (Metric.closedBall 0 1) := by
  have hre := Complex.reCLM.contDiff.comp_contDiffOn (hw.restrict_scalars ℝ)
  have ht : ContDiffOn ℝ ∞ (fun ζ => s * Real.exp (2 * (w ζ).re))
      (Metric.closedBall 0 1) :=
    contDiffOn_const.mul ((contDiffOn_const.mul hre).exp)
  exact cotangentDisc_metricFamilyNorm_contDiffOn hloc.1.2.1
    (f := fun ζ => (f ζ, ξ ζ)) hd ht
    (fun ζ _ => (mul_pos hs (Real.exp_pos _)).le)

end Yau.NodeProofs.E01Aux
