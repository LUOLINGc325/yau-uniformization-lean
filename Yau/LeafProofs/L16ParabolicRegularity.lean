import Yau.LeafProofs.L16ParabolicCoordinates
import Yau.LeafProofs.L16CoordinateRegularity

open MeasureTheory Filter
open scoped Topology ContDiff
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic

theorem smooth_representative_of_finite_parabolic_weak_jets {n : ℕ} {u : Point n → ℝ}
    (hjets : ∀ N : ℕ, ∃ U : List (ParabolicJointIdx n) → Point n → ℝ,
      FiniteParabolicWeakJet N u U) :
    ∃ v : Point n → ℝ, ContDiff ℝ ∞ v ∧ v =ᵐ[volume] u := by
  let e := parabolicCoordinateEquiv n
  have hCoord : ∀ N : ℕ, ∃ U : List (Fin (Fintype.card (ParabolicJointIdx n))) →
      (Fin (Fintype.card (ParabolicJointIdx n)) → ℝ) → ℝ,
      FiniteCoordinateWeakJet N (u ∘ e.symm) U := by
    intro N
    obtain ⟨U,hU⟩ := hjets N
    exact ⟨_,finiteParabolicWeakJet_to_coordinate hU⟩
  obtain ⟨v,hv,hAE⟩ := smooth_representative_of_finite_coordinate_weak_jets hCoord
  refine ⟨v ∘ e,hv.comp e.contDiff,?_⟩
  obtain ⟨c,hc,hMap⟩ := parabolicCoordinateEquiv_map_volume n
  have hMapped : v =ᵐ[Measure.map e (volume : Measure (Point n))] (u ∘ e.symm) := by
    rw [hMap]
    exact Measure.ae_smul_measure hAE (ENNReal.ofReal c)
  have hPull := e.toHomeomorph.toMeasurableEquiv.measurableEmbedding.ae_map_iff.mp hMapped
  filter_upwards [hPull] with p hp
  change v (e p) = u p
  simpa only [Homeomorph.toMeasurableEquiv_coe,ContinuousLinearEquiv.coe_toHomeomorph,
    Function.comp_def,ContinuousLinearEquiv.symm_apply_apply] using hp

end Yau.LeafProofs.L16Aux
