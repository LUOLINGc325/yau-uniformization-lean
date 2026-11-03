import Yau.Proofs.F01BufferedGeometry
import Yau.Proofs.F01BufferedExhaustion
import Yau.Proofs.F01ChartScaleBudget
import Yau.Proofs.F01BoundedGeometryComplete

/-! Actual bounded geometry and induced-distance completeness of the
explicit conformal approximation on the base-point sublevel component.
Only smoothness, compactness of the fixed original sublevel and u≥0 are
used. No regular-level, complete metric, or BG witness is assumed. -/
open Set Metric
open scoped Manifold ContDiff ComplexOrder Matrix.Norms.Frobenius
noncomputable section
namespace Yau.NodeProofs.F01Aux
open Yau Yau.LeafProofs
variable {n : ℕ} (M : ComplexManifold n)

theorem approximatingMetric_boundedGeometry {g : HermitianField M} (hg : MetricSmooth g)
    {u : M.Carrier → ℝ} (hu : SmoothFn u) (hnonneg : ∀ x, 0 ≤ u x)
    (o : M.Carrier) {L : ℝ} (hL : 0 < L) (ho : u o < L)
    (hK : IsCompact {x | u x ≤ L}) :
    LeafCandidates.HermitianBoundedGeometry (approximatingMetric M g u hu o L ho) := by
  classical
  let N := sublevelManifold M u hu o L ho
  let α : HermitianField N := approximatingMetric M g u hu o L ho
  obtain ⟨r, s, A, hr, hs, hA, hcover, hgrad⟩ :=
    finite_buffered_exhaustion_data M hK ⟨o, ho.le⟩ hu
  obtain ⟨c, hc, _hc1, hcr, hbudget⟩ := exists_chart_scale_budget s hs r
    (fun q _ => (hr q).1) hL hA.le
  let I := {q : M.Carrier // q ∈ s}
  letI : Fintype I := Fintype.ofFinite I
  have hfamilies := fun i : I => buffered_approximation_geometry M hg hu hnonneg o hL ho i.val
    (hr i.val).1 hc (hcr i.val i.property) hA.le (hr i.val).2
    (hgrad i.val i.property) hbudget
  choose D B hD hB hcharts using hfamilies
  obtain ⟨C, hC, hBC, hDC⟩ := exists_finite_uniform_budgets (Finset.univ : Finset I) B D
  refine ⟨1, by norm_num, C, hC, ?_⟩
  intro p
  have hpK : p.val ∈ {x | u x ≤ L} := (sublevelManifold_point_level M u hu o L ho p).le
  rcases mem_iUnion.mp (hcover hpK) with ⟨q, hq⟩
  rcases mem_iUnion.mp hq with ⟨hqs, z₀, hz₀, hcenter⟩
  let i : I := ⟨q, hqs⟩
  obtain ⟨eL, hcenterL, hsourceL, heL, heiL, hcomp, hsmooth, hjets⟩ :=
    hcharts i p z₀ (ball_subset_closedBall hz₀) hcenter
  refine ⟨eL, hcenterL, hsourceL, heL, heiL, ?_, hsmooth, ?_⟩
  · intro z hz
    have h := matrix_sandwich_mono (hD i) (hC 0) (hDC i (Finset.mem_univ _)) (hcomp z hz)
    change (L17Aux.pullbackMatrix α eL z - ((C 0)⁻¹ : ℂ) • 1).PosSemidef ∧
      ((C 0 : ℂ) • 1 - L17Aux.pullbackMatrix α eL z).PosSemidef
    simpa only [Complex.ofReal_inv] using h
  · intro k z hz i₁ j₁
    exact (hjets k z hz i₁ j₁).trans (hBC i (Finset.mem_univ _) k)

theorem approximatingMetric_completeDistance {g : HermitianField M} (hg : MetricSmooth g)
    {u : M.Carrier → ℝ} (hu : SmoothFn u) (hnonneg : ∀ x, 0 ≤ u x)
    (o : M.Carrier) {L : ℝ} (hL : 0 < L) (ho : u o < L)
    (hK : IsCompact {x | u x ≤ L}) :
    IsCompleteDistance (inducedDistance (approximatingMetric M g u hu o L ho)) :=
  completeDistance_of_hermitianBoundedGeometry _
    (approximatingMetric_metricSmooth M hg hu o hL ho)
    (approximatingMetric_boundedGeometry M hg hu hnonneg o hL ho hK)

theorem approximatingMetric_actual_geometry {g : HermitianField M} (hg : MetricSmooth g)
    {u : M.Carrier → ℝ} (hu : SmoothFn u) (hnonneg : ∀ x, 0 ≤ u x)
    (o : M.Carrier) {L : ℝ} (hL : 0 < L) (ho : u o < L)
    (hK : IsCompact {x | u x ≤ L}) :
    MetricSmooth (approximatingMetric M g u hu o L ho) ∧
      LeafCandidates.HermitianBoundedGeometry (approximatingMetric M g u hu o L ho) ∧
      IsCompleteDistance (inducedDistance (approximatingMetric M g u hu o L ho)) := by
  have hsm := approximatingMetric_metricSmooth M hg hu o hL ho
  have hbg := approximatingMetric_boundedGeometry M hg hu hnonneg o hL ho hK
  exact ⟨hsm, hbg, completeDistance_of_hermitianBoundedGeometry _ hsm hbg⟩

end Yau.NodeProofs.F01Aux
