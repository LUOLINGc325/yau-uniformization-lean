import Yau.LeafProofs.L17HolomorphicCharts

/-! An actual smooth scalar function has smooth coefficients in every
holomorphic local parametrization, using a fixed native chart locally. -/
noncomputable section
open Set Filter
open scoped Manifold ContDiff Topology
namespace Yau.NodeProofs.F01Aux
open Yau Yau.LeafProofs.L17Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem smoothFn_comp_holomorphic_chart (f : M.Carrier → ℝ) (hf : SmoothFn f)
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (he : MDifferentiableOn (ComplexModel n) (ComplexModel n) e e.source) :
    ContDiffOn ℝ ∞ (fun z => f (e z)) e.source := by
  intro z hz
  let a := e z
  let T : ComplexVector n → ComplexVector n := fun w => chartPt a (e w)
  have ha : e z ∈ (extChartAt (ComplexModel n) a).source := mem_extChartAt_source a
  have hzD : z ∈ forwardChartDomain e a := ⟨hz, ha⟩
  have hT : ContDiffAt ℝ ∞ T z := ((forwardChart_contDiffOn e he a).contDiffAt
    ((forwardChartDomain_isOpen e a).mem_nhds hzD)).restrict_scalars ℝ
  have hfa : ContDiffAt ℝ ∞ (inChart a f) (T z) :=
    (hf a).contDiffAt ((isOpen_extChartAt_target (I := ComplexModel n) a).mem_nhds
      ((extChartAt (ComplexModel n) a).map_source ha))
  have hgerm : (fun w => f (e w)) =ᶠ[𝓝 z] (fun w => inChart a f (T w)) := by
    filter_upwards [(forwardChartDomain_isOpen e a).mem_nhds hzD] with w hw
    change f (e w) = f (chartInv a (chartPt a (e w)))
    exact (congrArg f ((extChartAt (ComplexModel n) a).left_inv hw.2)).symm
  exact ((hfa.comp z hT).congr_of_eventuallyEq hgerm).contDiffWithinAt

end Yau.NodeProofs.F01Aux
