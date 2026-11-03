import Yau.Proofs.P06OneOneEnergyProjection
import Yau.Proofs.P06HodgeEnergyMinimization
import Yau.Proofs.P06HodgeEuler
import Yau.Proofs.P06MatrixHilbertSchmidt

noncomputable section
open MeasureTheory Filter
open scoped Topology InnerProductSpace

namespace Yau.NodeProofs.P06Aux
open Yau Yau.LeafProofs.L03
variable {n : ℕ} {M : ComplexManifold n}

theorem oneOneProjectionHilbert_normal (g : SmoothMetric M) (μ : Measure M.Carrier)
    (x b : L2FormHilbert g μ 2) (hb : oneOneProjectionHilbert g μ b = b) :
    inner ℝ (x - oneOneProjectionHilbert g μ x) (b - oneOneProjectionHilbert g μ x) = 0 := by
  rw [inner_sub_left, oneOneProjectionHilbert_selfadjoint, map_sub, hb,
    oneOneProjectionHilbert_idempotent, sub_self]

/-- The actual variational Hodge resolvent preserves the (1,1) subspace,
using the genuine q contraction of the original energy projection. -/
theorem hodgeImplicitResolvent_oneOne (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (hk : IsKahler g)
    (s : ℝ) (hs : 0 < s) (f : L2FormHilbert g μ 2)
    (hf : oneOneProjectionHilbert g μ f = f) :
    oneOneProjectionHilbert g μ (hodgeImplicitResolvent g μ hμ 2 s hs f) =
      hodgeImplicitResolvent g μ hμ 2 s hs f := by
  obtain ⟨u, hu, hvar⟩ := hodgeImplicitResolvent_energy g μ hμ s hs f
  let v := oneOneProjectionEnergy g μ hμ hk u
  have hv : hodgeEnergyValue g μ hμ v = oneOneProjectionHilbert g μ (hodgeEnergyValue g μ hμ u) :=
    oneOneProjectionEnergy_value g μ hμ hk u
  have hq : hodgeEnergy g μ hμ v ≤ hodgeEnergy g μ hμ u := oneOneProjectionEnergy_q_le g μ hμ hk u
  have hd : ‖hodgeEnergyValue g μ hμ v - f‖ ^ 2 ≤ ‖hodgeEnergyValue g μ hμ u - f‖ ^ 2 -
      ‖hodgeEnergyValue g μ hμ u - hodgeEnergyValue g μ hμ v‖ ^ 2 := by
    rw [hv]
    exact Clip.distance_sq_le_of_normal_inequality _ _ _
      (le_of_eq (oneOneProjectionHilbert_normal g μ _ f hf))
  have he := hodgeEnergy_competitor_eq g μ hμ f s⁻¹ (inv_pos.mpr hs) u v hvar hq hd
  rw [← hu]
  exact (he.trans hv).symm

/-- The original same-time CFC heat preserves type, via its actual
resolvent Euler approximation in operator norm. -/
theorem hodgeHeatHilbert_oneOne (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (hk : IsKahler g)
    (f : L2FormHilbert g μ 2) (hf : oneOneProjectionHilbert g μ f = f)
    (t : ℝ) (ht : 0 ≤ t) :
    oneOneProjectionHilbert g μ (hodgeHeatHilbert g μ hμ 2 t f) = hodgeHeatHilbert g μ hμ 2 t f := by
  let K : Set (L2FormHilbert g μ 2) := {u | oneOneProjectionHilbert g μ u = u}
  have hc : IsClosed K := isClosed_eq (oneOneProjectionHilbert g μ).continuous continuous_id
  exact hodgeHeat_mem_of_resolvent_invariant g μ hμ 2 K hc
    (fun s hs u hu => hodgeImplicitResolvent_oneOne g μ hμ hk s hs u hu) f hf t ht

/-- Every typed Hilbert value has a globally real (1,1) representative
in the original raw L² space. -/
theorem exists_oneOneL2_representative (g : SmoothMetric M) (μ : Measure M.Carrier)
    (f : L2FormHilbert g μ 2) (hf : oneOneProjectionHilbert g μ f = f) :
    ∃ (A : RealForm M 2) (hA : L2RealForm g.form μ A), RealOneOne A ∧ realizeActualForm g μ A hA = f := by
  obtain ⟨A, hA, he⟩ := l2FormHilbert_exists_section g μ f
  change realizeActualForm g μ A hA = f at he
  refine ⟨P06Weitzenbock.oneOneProjection A, l2RealForm_oneOneProjection g μ A hA,
    P06Weitzenbock.oneOneProjection_type A, ?_⟩
  rw [← oneOneProjectionHilbert_realize g μ A hA, he, hf]

end Yau.NodeProofs.P06Aux
