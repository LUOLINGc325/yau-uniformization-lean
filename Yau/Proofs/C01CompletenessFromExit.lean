import Yau.Proofs.C01ExitSphere

/-! Compact containment of actual metric balls implies sequence
completeness of the exact project length distance. The containing compact
sets use the original complete metric. -/

noncomputable section

open Filter
open scoped Manifold Topology ContDiff

namespace Yau.NodeProofs.C01Aux

open Yau Yau.Blueprint
open Yau.LeafProofs.L12Aux Yau.LeafProofs.L23Aux

variable {n : ℕ} {M : ComplexManifold n}

theorem complete_distance_of_compact_sublevels
    (k : HermitianField M) (hk : MetricSmooth k) (o : M.Carrier)
    (hcompact : ∀ R : ℝ, IsCompact {x : M.Carrier | inducedDistance k o x ≤ R}) :
    IsCompleteDistance (inducedDistance k) := by
  letI := metricSpaceOfField k hk
  have hball (R : ℝ) : IsCompact (Metric.closedBall o R) := by
    convert hcompact R using 1
    ext x
    simp only [Metric.mem_closedBall, Set.mem_ofPred_eq, metricSpaceOfField_dist,
      inducedDistance_symm k hk x o]
  letI : ProperSpace M.Carrier := ProperSpace.of_seq_closedBall
    (x := o) (r := fun j : ℕ => (j : ℝ)) tendsto_natCast_atTop_atTop
    (Eventually.of_forall fun j => hball j)
  intro u hu
  have huc : CauchySeq u := by
    apply Metric.cauchySeq_iff.mpr
    intro ε hε
    obtain ⟨N, hN⟩ := hu ε hε
    exact ⟨N, fun m hm j hj => hN m j hm hj⟩
  obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete huc
  exact ⟨x, Metric.tendsto_atTop.mp hx⟩

theorem complete_distance_of_original_ball_containment
    (g : SmoothMetric M) (k : HermitianField M) (hk : MetricSmooth k) (o : M.Carrier)
    (hcontain : ∀ R : ℝ, ∃ L : ℝ, ∀ x : M.Carrier,
      inducedDistance k o x ≤ R → inducedDistance g.form o x ≤ L) :
    IsCompleteDistance (inducedDistance k) := by
  apply complete_distance_of_compact_sublevels k hk o
  intro R
  obtain ⟨L, hL⟩ := hcontain R
  exact (isCompact_inducedDistance_sublevel g o L).of_isClosed_subset
    (isClosed_le (Yau.LeafProofs.L23Aux.continuous_distFrom k hk o) continuous_const)
    (fun x hx => hL x hx)

theorem complete_distance_of_exit_profile
    (g : SmoothMetric M) (k : HermitianField M) (hk : MetricSmooth k) (o : M.Carrier)
    (hgrowth : ∀ R : ℝ, ∃ L : ℝ, 0 ≤ L ∧ R < exitDistanceProfile g k o L)
    (hcross : ∀ L : ℝ, 0 ≤ L → ∀ x : M.Carrier,
      L ≤ inducedDistance g.form o x → exitDistanceProfile g k o L ≤ inducedDistance k o x) :
    IsCompleteDistance (inducedDistance k) := by
  apply complete_distance_of_original_ball_containment g k hk o
  intro R
  obtain ⟨L, hL, hR⟩ := hgrowth R
  refine ⟨L, ?_⟩
  intro x hx
  by_contra hfail
  have hexit := hcross L hL x (le_of_lt (lt_of_not_ge hfail))
  exact (not_lt_of_ge (hexit.trans hx)) hR

end Yau.NodeProofs.C01Aux
