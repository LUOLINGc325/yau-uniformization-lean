import Yau.Proofs.F04Source

open Filter Set
open scoped Topology ContDiff Manifold

noncomputable section

namespace Yau.F04Proof

open Yau.Blueprint

theorem chartwise_continuousOn {n : ℕ} {M : ComplexManifold n} {I : Set ℝ}
    {v : M.Carrier → ℝ → ℝ}
    (hv : ∀ x, ContinuousOn (fun p : ComplexVector n × ℝ => v (chartInv x p.1) p.2)
      (chartTarget x ×ˢ I)) :
    ContinuousOn (fun p : M.Carrier × ℝ => v p.1 p.2) (univ ×ˢ I) := by
  rintro ⟨x, t⟩ hp
  have hx : chartPt x x ∈ chartTarget x := mem_extChartAt_target x
  have hcz := LeafProofs.chartInv_chartPt_of_mem x x (mem_chart_source _ _)
  have hmapc : ContinuousAt (fun p : M.Carrier × ℝ => (chartPt x p.1, p.2)) (x, t) :=
    ((continuousAt_extChartAt (I := ComplexModel n) x).comp continuousAt_fst).prodMk continuousAt_snd
  have hnear : ∀ᶠ p : M.Carrier × ℝ in 𝓝[univ ×ˢ I] (x, t),
      p.1 ∈ (extChartAt (ComplexModel n) x).source := by
    apply nhdsWithin_le_nhds
    exact continuousAt_fst.eventually
      ((isOpen_extChartAt_source (I := ComplexModel n) x).mem_nhds (mem_extChartAt_source x))
  have hmap : Tendsto (fun p : M.Carrier × ℝ => (chartPt x p.1, p.2))
      (𝓝[univ ×ˢ I] (x, t)) (𝓝[chartTarget x ×ˢ I] (chartPt x x, t)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hmapc.mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [hnear, self_mem_nhdsWithin] with p hpx hpt
    exact ⟨(extChartAt (ComplexModel n) x).map_source hpx, hpt.2⟩
  have hcomp := (hv x (chartPt x x, t) ⟨hx, hp.2⟩).tendsto.comp hmap
  have heq : (fun p : M.Carrier × ℝ => v (chartInv x (chartPt x p.1)) p.2)
      =ᶠ[𝓝[univ ×ˢ I] (x, t)] (fun p => v p.1 p.2) := by
    filter_upwards [hnear] with p hpx
    exact congrArg (fun y => v y p.2) ((extChartAt (ComplexModel n) x).left_inv hpx)
  have hh := (tendsto_congr' heq).mp hcomp
  change Tendsto (fun p : M.Carrier × ℝ => v p.1 p.2)
    (𝓝[univ ×ˢ I] (x, t)) (𝓝 (v x t))
  simpa only [hcz] using hh

theorem smoothSpaceC1Time_continuousOn {n : ℕ} {M : ComplexManifold n} {I : Set ℝ}
    {v : M.Carrier → ℝ → ℝ} (hv : SmoothSpaceC1Time v I) :
    ContinuousOn (fun p : M.Carrier × ℝ => v p.1 p.2) (univ ×ˢ I) :=
  chartwise_continuousOn (fun x => (hv.2 x).continuousOn)

theorem smoothSpaceTime_continuousOn {n : ℕ} {M : ComplexManifold n} {I : Set ℝ}
    {v : M.Carrier → ℝ → ℝ} (hv : SmoothSpaceTime v I) :
    ContinuousOn (fun p : M.Carrier × ℝ => v p.1 p.2) (univ ×ˢ I) :=
  chartwise_continuousOn (fun x => (hv x).continuousOn)

end Yau.F04Proof
