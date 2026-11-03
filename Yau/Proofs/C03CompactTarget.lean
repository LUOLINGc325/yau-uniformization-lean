import Yau.LeafProofs.L23FieldMetric
import Mathlib.Topology.MetricSpace.Thickening

/-! A compact target set has one fixed compact neighborhood containing
all sufficiently short metric neighborhoods of its points. -/

noncomputable section
open Set Metric
open scoped Topology

namespace Yau.Proofs.C03Aux
open Yau Yau.LeafProofs L12Aux L23Aux
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ}

theorem exists_compact_target_neighborhood (X : KahlerManifold n)
    (K : Set X.manifold.Carrier) (hK : IsCompact K) :
    ∃ (K' : Set X.manifold.Carrier) (ε : ℝ), IsCompact K' ∧ 0 < ε ∧ K ⊆ K' ∧
      ∀ o ∈ K, ∀ y : X.manifold.Carrier, inducedDistance X.metric.form o y ≤ ε → y ∈ K' := by
  letI := metricSpaceOfField X.metric.form (metricSmooth_of_smoothMetric X.metric)
  letI : LocallyCompactSpace X.manifold.Carrier := manifold_locallyCompact X.manifold
  obtain ⟨U, hU, hKU, hUc⟩ := exists_isOpen_superset_and_isCompact_closure hK
  obtain ⟨ε, hε, hεU⟩ := hK.exists_cthickening_subset_open hU hKU
  refine ⟨closure U, ε, hUc, hε, hKU.trans subset_closure, ?_⟩
  intro o ho y hy
  apply subset_closure
  apply hεU
  apply mem_cthickening_of_dist_le y o ε K ho
  rw [dist_comm]
  exact hy

end Yau.Proofs.C03Aux
