import Yau.Proofs.F04ChartContinuity

open Filter Set
open scoped Topology ContDiff Manifold
noncomputable section
namespace Yau.F04Proof
open Yau.Parabolic Yau.LeafProofs.L18Aux

/-- Actual smoothness in one genuine center chart near each physical
 point gives smoothness in EVERY physical chart, on any supplied time set.
 Relative neighborhoods retain closed time faces. -/
theorem smoothSpaceTime_of_local_center_charts
    {n : ℕ} {M : ComplexManifold n} {I : Set ℝ} {v : M.Carrier → ℝ → ℝ}
    (hLocal : ∀ x : M.Carrier, ∃ O : Set (Space n), IsOpen O ∧ chartPt x x ∈ O ∧ O ⊆ chartTarget x ∧
      ContDiffOn ℝ ∞ (fun p : Point n => v (chartInv x p.1) p.2) (O ×ˢ I)) :
    SmoothSpaceTime v I := by
  intro a p hp
  let y := chartInv a p.1
  obtain ⟨O,hO,hyO,_hOt,hv⟩ := hLocal y
  have hTrans : ContDiffAt ℝ ∞ (fun z => chartPt y (chartInv a z)) p.1 :=
    (chartTransition_contDiffAt a y hp.1 (mem_extChartAt_source y)).restrict_scalars ℝ
  have hMap : ContDiffAt ℝ ∞ (fun q : Point n => (chartPt y (chartInv a q.1),q.2)) p :=
    (hTrans.comp p contDiffAt_fst).prodMk contDiffAt_snd
  have hInv : ContinuousAt (fun q : Point n => chartInv a q.1) p :=
    ((continuousOn_extChartAt_symm (I := ComplexModel n) a).continuousAt
      ((isOpen_extChartAt_target (I := ComplexModel n) a).mem_nhds hp.1)).comp continuousAt_fst
  have hNearO : ∀ᶠ q : Point n in 𝓝 p, chartPt y (chartInv a q.1) ∈ O :=
    (hTrans.continuousAt.comp continuousAt_fst).eventually (hO.mem_nhds hyO)
  have hNearSource : ∀ᶠ q : Point n in 𝓝 p,
      chartInv a q.1 ∈ (extChartAt (ComplexModel n) y).source :=
    hInv.eventually ((isOpen_extChartAt_source (I := ComplexModel n) y).mem_nhds (mem_extChartAt_source y))
  have hPre : (fun q : Point n => (chartPt y (chartInv a q.1),q.2)) ⁻¹' (O ×ˢ I) ∈
      𝓝[chartTarget a ×ˢ I] p := by
    filter_upwards [mem_nhdsWithin_of_mem_nhds hNearO,self_mem_nhdsWithin] with q hq hqD
    exact ⟨hq,hqD.2⟩
  have hc := (hv (chartPt y y,p.2) ⟨hyO,hp.2⟩).comp_of_preimage_mem_nhdsWithin p hMap.contDiffWithinAt hPre
  have he : (fun q : Point n => v (chartInv a q.1) q.2) =ᶠ[𝓝[chartTarget a ×ˢ I] p]
      (fun q => v (chartInv y (chartPt y (chartInv a q.1))) q.2) := by
    filter_upwards [mem_nhdsWithin_of_mem_nhds hNearSource] with q hq
    exact congrArg (fun x => v x q.2) ((extChartAt (ComplexModel n) y).left_inv hq).symm
  exact hc.congr_of_eventuallyEq_of_mem he hp

end Yau.F04Proof
