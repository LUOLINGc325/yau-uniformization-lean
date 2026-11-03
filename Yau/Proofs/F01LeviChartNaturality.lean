import Yau.LeafProofs.L17RicciNaturality

/-! The actual Levi matrix in a holomorphic local chart is the congruence
of the original native Levi matrix by the actual coordinate differential. -/
noncomputable section
open Set Filter
open scoped Manifold ContDiff Matrix Topology
namespace Yau.NodeProofs.F01Aux
open Yau Yau.LeafProofs.L17Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem leviC_holomorphic_chart (f : M.Carrier → ℝ) (hf : SmoothFn f)
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (he : MDifferentiableOn (ComplexModel n) (ComplexModel n) e e.source)
    {z : ComplexVector n} (hz : z ∈ e.source) :
    leviC (fun w => f (e w)) z =
      (linearMatrix (coordinateDifferential e (e z) z))ᴴ *
        levi f (e z) * linearMatrix (coordinateDifferential e (e z) z) := by
  let a := e z
  let T : ComplexVector n → ComplexVector n := fun w => chartPt a (e w)
  have ha : e z ∈ (extChartAt (ComplexModel n) a).source := mem_extChartAt_source a
  have hzD : z ∈ forwardChartDomain e a := ⟨hz, ha⟩
  have hT : ContDiffAt ℂ 2 T z := ((forwardChart_contDiffOn e he a).contDiffAt
    ((forwardChartDomain_isOpen e a).mem_nhds hzD)).of_le (by simp)
  have hfa : ContDiffAt ℝ 2 (inChart a f) (T z) :=
    ((hf a).contDiffAt ((isOpen_extChartAt_target (I := ComplexModel n) a).mem_nhds
      ((extChartAt (ComplexModel n) a).map_source ha))).of_le (by simp)
  have hgerm : (fun w => f (e w)) =ᶠ[𝓝 z] (inChart a f ∘ T) := by
    filter_upwards [(forwardChartDomain_isOpen e a).mem_nhds hzD] with w hw
    change f (e w) = f (chartInv a (chartPt a (e w)))
    exact (congrArg f ((extChartAt (ComplexModel n) a).left_inv hw.2)).symm
  rw [Yau.LeafProofs.L22Aux.leviC_congr_of_eventuallyEq hgerm, leviC_comp hT hfa,
    ← coordinateDifferential_eq_fderiv e he a hz ha]
  rfl

end Yau.NodeProofs.F01Aux
