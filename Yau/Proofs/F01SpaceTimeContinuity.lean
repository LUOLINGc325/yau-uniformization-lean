import Yau.Proofs.F01SpaceTimeChart
import Yau.Proofs.F01OrdinaryCharts

/-! Native joint scalar smoothness gives actual manifold-times-time
continuity on the complete original time set. -/
noncomputable section
open Set Filter
open scoped Topology Manifold ContDiff
namespace Yau.NodeProofs.F01Aux
open Yau
variable {n : ℕ} {M : ComplexManifold n}

theorem smoothSpaceTime_continuousOn {F : M.Carrier → ℝ → ℝ} {I : Set ℝ}
    (hF : SmoothSpaceTime F I) :
    ContinuousOn (fun p : M.Carrier × ℝ => F p.1 p.2) (univ ×ˢ I) := by
  rintro ⟨x, t⟩ hp
  let e := ordinaryChart x
  have hx : x ∈ e.target := mem_chart_source (ComplexVector n) x
  have hc := (smoothSpaceTime_holomorphic_chart hF e
    ((ordinaryChart_contMDiffOn x).mdifferentiableOn (by simp))).continuousOn
  have hφ : ContinuousAt (fun p : M.Carrier × ℝ => (e.symm p.1, p.2)) (x, t) :=
    ((e.symm.continuousAt hx).comp continuousAt_fst).prodMk continuousAt_snd
  have hmap : MapsTo (fun p : M.Carrier × ℝ => (e.symm p.1, p.2))
      (e.target ×ˢ I) (e.source ×ˢ I) := fun p hp => ⟨e.map_target hp.1, hp.2⟩
  have hcomp := (hc (e.symm x, t) ⟨e.map_target hx, hp.2⟩).comp
    (f := fun p : M.Carrier × ℝ => (e.symm p.1, p.2)) (x := (x, t)) hφ.continuousWithinAt hmap
  have hlocal : ContinuousWithinAt (fun p : M.Carrier × ℝ => F p.1 p.2) (e.target ×ˢ I) (x, t) := by
    apply hcomp.congr_of_mem
    · intro p hp
      exact (congrArg (fun y => F y p.2) (e.right_inv hp.1)).symm
    · exact ⟨hx, hp.2⟩
  apply hlocal.mono_of_mem_nhdsWithin
  have hn : {p : M.Carrier × ℝ | p.1 ∈ e.target} ∈ 𝓝 (x, t) :=
    (e.open_target.preimage continuous_fst).mem_nhds hx
  filter_upwards [mem_nhdsWithin_of_mem_nhds hn, self_mem_nhdsWithin] with p hpt hpi
  exact ⟨hpt, hpi.2⟩

end Yau.NodeProofs.F01Aux
