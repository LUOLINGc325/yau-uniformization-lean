import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

open Set MeasureTheory
open scoped Topology Interval
noncomputable section
namespace Yau.LeafProofs.L17SchauderAux

variable {Z F G : Type*} [TopologicalSpace Z]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

theorem pathIntegral_intervalIntegrable (path : ℝ → Z) (hp : Continuous path)
    (L : F →L[ℝ] G) (f : BoundedContinuousFunction Z F) (a b : ℝ) :
    IntervalIntegrable (fun theta => L (f (path theta))) volume a b :=
  (L.continuous.comp (f.continuous.comp hp)).intervalIntegrable a b

/-- Integration along an actual continuous path is bounded in the genuine
bounded-continuous-function norm. -/
def pathIntegralCLM (path : ℝ → Z) (hp : Continuous path) (L : F →L[ℝ] G) (a b : ℝ) :
    BoundedContinuousFunction Z F →L[ℝ] G :=
  LinearMap.mkContinuous
    { toFun := fun f : BoundedContinuousFunction Z F => ∫ theta in a..b, L (f (path theta))
      map_add' := by
        intro f g
        change (∫ theta in a..b, L (f (path theta)+g (path theta))) = _
        simp only [map_add]
        exact intervalIntegral.integral_add (pathIntegral_intervalIntegrable path hp L f a b)
          (pathIntegral_intervalIntegrable path hp L g a b)
      map_smul' := by
        intro c f
        change (∫ theta in a..b, L (c • f (path theta))) = c • _
        simp only [map_smul]
        exact intervalIntegral.integral_smul c _ }
    (|b-a| *‖L‖) (by
      intro f
      calc
        _ ≤ (‖L‖*‖f‖)*|b-a| := intervalIntegral.norm_integral_le_of_norm_le_const (fun theta _ =>
          (L.le_opNorm _).trans (mul_le_mul_of_nonneg_left (f.norm_coe_le_norm _) (norm_nonneg L)))
        _ = _ := by ring)

theorem pathIntegralCLM_apply (path : ℝ → Z) (hp : Continuous path) (L : F →L[ℝ] G)
    (a b : ℝ) (f : BoundedContinuousFunction Z F) :
    pathIntegralCLM path hp L a b f = ∫ theta in a..b, L (f (path theta)) := rfl

end Yau.LeafProofs.L17SchauderAux
