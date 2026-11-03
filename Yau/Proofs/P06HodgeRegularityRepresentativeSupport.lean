import Yau.Proofs.P06HodgeRegularitySmoothChart

/-! Continuous actual representatives retain the literal compact support
of their rough class when the measure has full support. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff

namespace Yau.NodeProofs.P06Aux

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E]

theorem regularityContinuous_tsupport_subset_of_ae
    (ν : Measure E) [ν.IsOpenPosMeasure] {f u : E → ℝ}
    (hf : Continuous f) (hAE : f =ᵐ[ν] u) {K : Set E} (hK : IsClosed K)
    (hu : tsupport u ⊆ K) : tsupport f ⊆ K := by
  apply closure_minimal _ hK
  intro z hz
  by_contra hzK
  have hzero : f =ᵐ[ν.restrict Kᶜ] (fun _ => (0 : ℝ)) := by
    filter_upwards [ae_restrict_mem hK.measurableSet.compl, ae_restrict_of_ae hAE] with y hy hae
    rw [hae]
    exact image_eq_zero_of_notMem_tsupport (fun h => hy (hu h))
  have hp := Measure.eqOn_open_of_ae_eq hzero hK.isOpen_compl hf.continuousOn continuousOn_const hzK
  exact hz hp

end Yau.NodeProofs.P06Aux
