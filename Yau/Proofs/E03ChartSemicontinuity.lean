import Yau.Proofs.F04ChartContinuity

/-! Relative upper semicontinuity in actual manifold charts transports to space-time. -/

noncomputable section
open scoped Topology ContDiff Manifold
open Filter Set

namespace Yau.NodeProofs.E03Aux
open Yau Yau.Blueprint

theorem chartwise_upperSemicontinuousOn {n : ℕ} {M : ComplexManifold n} {I : Set ℝ}
    {v : M.Carrier → ℝ → ℝ}
    (hv : ∀ c, UpperSemicontinuousOn
      (fun p : ComplexVector n × ℝ => v (chartInv c p.1) p.2) (chartTarget c ×ˢ I)) :
    UpperSemicontinuousOn (fun p : M.Carrier × ℝ => v p.1 p.2) (univ ×ˢ I) := by
  rintro ⟨y, t⟩ hp a ha
  have hy : chartPt y y ∈ chartTarget y := mem_extChartAt_target (I := ComplexModel n) y
  have hround : chartInv y (chartPt y y) = y :=
    (extChartAt (ComplexModel n) y).left_inv (mem_extChartAt_source (I := ComplexModel n) y)
  have hmapc : ContinuousAt (fun p : M.Carrier × ℝ => (chartPt y p.1, p.2)) (y, t) :=
    ((continuousAt_extChartAt (I := ComplexModel n) y).comp continuousAt_fst).prodMk continuousAt_snd
  have hnear : ∀ᶠ p : M.Carrier × ℝ in 𝓝[univ ×ˢ I] (y, t),
      p.1 ∈ (extChartAt (ComplexModel n) y).source := by
    apply nhdsWithin_le_nhds
    exact continuousAt_fst.eventually
      ((isOpen_extChartAt_source (I := ComplexModel n) y).mem_nhds
        (mem_extChartAt_source (I := ComplexModel n) y))
  have hmap : Tendsto (fun p : M.Carrier × ℝ => (chartPt y p.1, p.2))
      (𝓝[univ ×ˢ I] (y, t)) (𝓝[chartTarget y ×ˢ I] (chartPt y y, t)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hmapc.mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [hnear, self_mem_nhdsWithin] with p hpx hpt
    exact ⟨(extChartAt (ComplexModel n) y).map_source hpx, hpt.2⟩
  have hval : v (chartInv y (chartPt y y)) t < a := by rwa [hround]
  have hcut : ∀ᶠ q in 𝓝[chartTarget y ×ˢ I] (chartPt y y, t),
      v (chartInv y q.1) q.2 < a := hv y (chartPt y y, t) ⟨hy, hp.2⟩ a hval
  filter_upwards [hmap.eventually hcut, hnear] with p hlt hpx
  have hr : chartInv y (chartPt y p.1) = p.1 :=
    (extChartAt (ComplexModel n) y).left_inv hpx
  change v (chartInv y (chartPt y p.1)) p.2 < a at hlt
  rwa [hr] at hlt

end Yau.NodeProofs.E03Aux
