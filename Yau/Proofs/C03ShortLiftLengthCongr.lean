import Yau.Geometry.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! Curve length depends only on the actual curve on its parameter interval. -/
noncomputable section
open scoped Manifold Topology
open Set Filter MeasureTheory
namespace Yau.Proofs.C03Aux.ShortLift
open Yau
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {M : ComplexManifold n}

theorem curveSpeed_eq_of_eventuallyEq (k : HermitianField M)
    {a b a' b' : M.Carrier} (gamma : PiecewiseC1Curve a b)
    (beta : PiecewiseC1Curve a' b') {t : ℝ}
    (heq : (gamma : ℝ → M.Carrier) =ᶠ[𝓝 t] beta) :
    curveSpeed k gamma t = curveSpeed k beta t := by
  have hp := heq.eq_of_nhds
  have hchart : (fun s : ℝ => extChartAt (ComplexModel n) (beta t) (gamma s))
      =ᶠ[𝓝 t] (fun s : ℝ => extChartAt (ComplexModel n) (beta t) (beta s)) := by
    filter_upwards [heq] with s hs
    rw [hs]
  unfold curveSpeed realTangentDerivative
  simp only [hp, hchart.fderiv_eq]
  rw [hp]

theorem curveLength_eq_on_interval (k : HermitianField M)
    {a b a' b' : M.Carrier} (gamma : PiecewiseC1Curve a b)
    (beta : PiecewiseC1Curve a' b')
    (heq : ∀ t ∈ Icc (0 : ℝ) 1, gamma t = beta t) :
    curveLength k gamma = curveLength k beta := by
  unfold curveLength
  apply integral_congr_ae
  rw [← Measure.restrict_congr_set (Ioo_ae_eq_Icc (μ := volume))]
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  apply curveSpeed_eq_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
  exact heq s ⟨hs.1.le, hs.2.le⟩

end Yau.Proofs.C03Aux.ShortLift
