import Yau.Proofs.V03GaussDiscCurrent
import Yau.Proofs.V03BaseDiscCurrent

/-! The actual original base and Gauss areas are smooth real functions
of the joint family parameter, by genuine compact closed-disc integration. -/

open scoped Topology ContDiff

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

theorem gaussFamilyArea_contDiffOn {n q : ℕ} {M : ComplexManifold n}
    {G : CotangentPoint M → ComplexVector q} (hG : CotangentImmersion G)
    {f : ℂ × ℂ → CotangentPoint M} {U : Set ℂ} (hU : IsOpen U)
    (hf : CotangentHolomorphicOn f (U ×ˢ Metric.closedBall (0 : ℂ) 1)) :
    ContDiffOn ℝ ∞ (fun z => gaussArea G (fun ζ => f (z, ζ))) U := by
  have hS : UniqueDiffOn ℂ (U ×ˢ Metric.closedBall (0 : ℂ) 1) :=
    hU.uniqueDiffOn.prod uniqueDiffOn_complex_closedDisc
  have hΩ := jointGaussTwoForm_contDiffOn hG hf hS
  have hd := twoFormCoefficient_contDiffOn hΩ ((0, 1) : ℂ × ℂ) ((0, Complex.I) : ℂ × ℂ)
  exact (discIntegral_contDiffOn hU hd).congr (fun z hz => gaussArea_joint_eq_discIntegral hG hf hz)

theorem baseFamilyArea_contDiffOn {n : ℕ} {M : ComplexManifold n}
    (g : SmoothMetric M) {f : ℂ × ℂ → CotangentPoint M} {U : Set ℂ} (hU : IsOpen U)
    (hf : CotangentHolomorphicOn f (U ×ˢ Metric.closedBall (0 : ℂ) 1)) :
    ContDiffOn ℝ ∞ (fun z => (discArea g.form (fun ζ => (f (z, ζ)).1)).toReal) U := by
  have hS : UniqueDiffOn ℂ (U ×ˢ Metric.closedBall (0 : ℂ) 1) :=
    hU.uniqueDiffOn.prod uniqueDiffOn_complex_closedDisc
  have hΩ := jointBaseTwoForm_contDiffOn g hf hS
  have hd := twoFormCoefficient_contDiffOn hΩ ((0, 1) : ℂ × ℂ) ((0, Complex.I) : ℂ × ℂ)
  exact (discIntegral_contDiffOn hU hd).congr (fun z hz => baseArea_joint_eq_discIntegral g hf hz)

end Yau.Blueprint.V03Proof
