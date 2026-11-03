import Yau.Proofs.C04BoundedGeometryChartsComplexSmooth
import Yau.Proofs.C04BoundedGeometryChartsNormalModels

/-! Real smooth maps with the actual complex chart differential equation are complex smooth maps. -/
noncomputable section
open Filter
open scoped Topology Manifold ContDiff
namespace Yau.Proofs.C04ChartsAux
open Yau Yau.LeafProofs.L12Aux
variable {n q : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 5

theorem contMDiffOn_complex_of_real_chart_I {O : Set (ComplexVector q)} (hO : IsOpen O)
    (f : ComplexVector q → M.Carrier)
    (hf : letI := manifold_realSmooth M
      ContMDiffOn 𝓘(ℝ, ComplexVector q) 𝓘(ℝ, ComplexVector n) ∞ f O)
    (hI : ∀ (c : M.Carrier) x, x ∈ O → f x ∈ (chartAt (ComplexVector n) c).source →
      ∀ v, fderiv ℝ (fun y => chartPt c (f y)) x (Complex.I • v) =
        Complex.I • fderiv ℝ (fun y => chartPt c (f y)) x v) :
    ContMDiffOn (ComplexModel q) (ComplexModel n) ∞ f O := by
  letI := manifold_realSmooth M
  intro x hx
  let c := f x
  let V := O ∩ f ⁻¹' (chartAt (ComplexVector n) c).source
  have hV : IsOpen V := hf.continuousOn.isOpen_inter_preimage hO (chartAt (ComplexVector n) c).open_source
  have hxV : x ∈ V := ⟨hx, mem_chart_source _ _⟩
  have hreal : ContDiffOn ℝ ∞ (fun y => chartPt c (f y)) V := by
    intro y hy
    have hfy : ContMDiffAt 𝓘(ℝ, ComplexVector q) 𝓘(ℝ, ComplexVector n) ∞ f y :=
      hf.contMDiffAt (hO.mem_nhds hy.1)
    have hchart : ContMDiffAt 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ComplexVector n) ∞ (chartPt c) (f y) :=
      contMDiffAt_extChartAt' hy.2
    exact (hchart.comp y hfy).contDiffAt.contDiffWithinAt
  have hcomplex : ContDiffOn ℂ ∞ (fun y => chartPt c (f y)) V :=
    contDiffOn_complex_of_real_and_I hV _ hreal (fun y hy => hI c y hy.1 hy.2)
  have hcm : ContMDiffAt (ComplexModel q) (ComplexModel n) ∞ (fun y => chartPt c (f y)) x :=
    (hcomplex.contDiffAt (hV.mem_nhds hxV)).contMDiffAt
  have hc : f x ∈ (extChartAt (ComplexModel n) c).source := by
    simpa only [extChartAt_source, Set.mem_preimage] using hxV.2
  have ht : chartPt c (f x) ∈ (extChartAt (ComplexModel n) c).target :=
    (extChartAt (ComplexModel n) c).map_source hc
  have hinv : ContMDiffAt (ComplexModel n) (ComplexModel n) ∞ (chartInv c) (chartPt c (f x)) :=
    (contMDiffOn_extChartAt_symm (I := ComplexModel n) c).contMDiffAt
      ((isOpen_extChartAt_target (I := ComplexModel n) c).mem_nhds ht)
  have H := hinv.comp x hcm
  have heq : f =ᶠ[𝓝 x] (fun y => chartInv c (chartPt c (f y))) := by
    filter_upwards [hV.mem_nhds hxV] with y hy
    exact ((extChartAt (ComplexModel n) c).left_inv
      (by simpa only [extChartAt_source, Set.mem_preimage] using hy.2)).symm
  exact (H.congr_of_eventuallyEq heq).contMDiffWithinAt

end Yau.Proofs.C04ChartsAux
