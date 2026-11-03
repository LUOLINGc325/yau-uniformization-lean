import Yau.Proofs.V03EuclideanRadial
import Yau.Proofs.V03Energy

/-! The original clock area has the same finite radial limit as the ambient
norm area. Every real conversion is made at a proved finite value. -/

open scoped Manifold Topology ContDiff Matrix ComplexOrder
open MeasureTheory Filter

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

theorem clockArea_eq_normDiscArea {n : ℕ} {X : KahlerManifold n} (F : VariationDisc X) :
    clockArea F = normDiscArea F.w := rfl

theorem clockArea_ne_top_of_closedDisc {n : ℕ} {X : KahlerManifold n}
    {F : VariationDisc X} (hw : ContDiffOn ℂ ∞ F.w (Metric.closedBall 0 1)) :
    clockArea F ≠ ⊤ := normDiscArea_ne_top_of_closedDisc hw

theorem clockArea_radial_tendsto {n : ℕ} {X : KahlerManifold n}
    {F : VariationDisc X} (hw : ContDiffOn ℂ ∞ F.w (Metric.closedBall 0 1)) :
    Tendsto (fun r : ℝ => clockArea (radialVariationDisc F r))
      (𝓝[Set.Icc 0 1] 1) (𝓝 (clockArea F)) := normDiscArea_radial_tendsto hw

theorem clockArea_radial_toReal_tendsto {n : ℕ} {X : KahlerManifold n}
    {F : VariationDisc X} (hw : ContDiffOn ℂ ∞ F.w (Metric.closedBall 0 1)) :
    Tendsto (fun r : ℝ => (clockArea (radialVariationDisc F r)).toReal)
      (𝓝[Set.Icc 0 1] 1) (𝓝 (clockArea F).toReal) :=
  (ENNReal.tendsto_toReal (clockArea_ne_top_of_closedDisc hw)).comp
    (clockArea_radial_tendsto hw)

end Yau.Blueprint.V03Proof
