import Yau.LeafProofs.L22LeviCalculus
import Yau.Proofs.P03CutoffPoleLevi

open scoped Manifold Topology ContDiff
open Filter

noncomputable section

namespace Yau.NodeProofs.P03Aux

open Yau.LeafProofs

variable {n : ℕ} {M : ComplexManifold n}

/-- Actual chart representations agree with the coordinate transition as
germs whenever both original charts contain the represented point. -/
theorem inChart_transition_germ_of_source {A : Type*} (f : M.Carrier → A)
    (a b : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget a)
    (hb : chartInv a z ∈ (extChartAt (ComplexModel n) b).source) :
    inChart a f =ᶠ[𝓝 z]
      (inChart b f) ∘ (fun y => chartPt b (chartInv a y)) := by
  have hi : ContinuousAt (chartInv a) z := continuousAt_extChartAt_symm'' hz
  have hn : ∀ᶠ y in 𝓝 z, chartInv a y ∈ (extChartAt (ComplexModel n) b).source :=
    hi.preimage_mem_nhds ((isOpen_extChartAt_source b).mem_nhds hb)
  filter_upwards [hn] with y hy
  change f (chartInv a y) = f (chartInv b (chartPt b (chartInv a y)))
  exact (congrArg f ((extChartAt (ComplexModel n) b).left_inv hy)).symm

/-- The actual real Hessian Levi quadratic transforms by the complex
Jacobian of the original holomorphic coordinate change. -/
theorem inChart_complexLevi_transition {f : M.Carrier → ℝ} (hf : SmoothFn f)
    (a b : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget a)
    (hb : chartInv a z ∈ (extChartAt (ComplexModel n) b).source) (v : ComplexVector n) :
    L22Aux.complexLeviQuadratic (inChart a f) z v =
      L22Aux.complexLeviQuadratic (inChart b f) (chartPt b (chartInv a z))
        (fderiv ℂ (fun y => chartPt b (chartInv a y)) z v) := by
  have hT : ContDiffAt ℂ 2 (fun y => chartPt b (chartInv a y)) z :=
    (L18Aux.chartTransition_contDiffAt a b hz hb).of_le (by simp)
  have hfb : ContDiffAt ℝ 2 (inChart b f) (chartPt b (chartInv a z)) :=
    ((hf b).contDiffAt ((isOpen_extChartAt_target b).mem_nhds
      ((extChartAt (ComplexModel n) b).map_source hb))).of_le (by simp)
  rw [complexLeviQuadratic_congr_germ (inChart_transition_germ_of_source f a b hz hb)]
  exact L22Aux.complexLeviQuadratic_comp hT hfb v

end Yau.NodeProofs.P03Aux
