import Yau.Proofs.V03PenaltyOrdered
import Yau.Proofs.V03CentersOrdered

/-! All clauses of the original localization contract, with the literal
sequence, positive-penalty and index order. -/

open scoped Manifold Topology ContDiff Matrix ComplexOrder
open Filter

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

variable {n q : ℕ} {X : KahlerManifold n}

theorem localizationEstimates {d : VariationData X q} (hd : VariationSetup d) :
    LocalizationEstimates d := by
  refine ⟨localizedInfimum_zero_tendsto hd, ?_, ?_⟩
  · filter_upwards [admissible_nonempty_eventually hd] with j hj
    have hfinite := localizedInfimum_finite_of_nonempty hd hj (ε := 0) le_rfl
    refine ⟨hj, hfinite.1, hfinite.2, (localizedInfimum_mono d j).monotoneOn _,
      localizedInfimum_right_tendsto_of_nonempty hd hj, ?_⟩
    intro ε hε F hF r hr
    obtain ⟨δ, hδ0, hδr⟩ := EReal.exists_between_coe_real hr
    have hδ : 0 < δ := EReal.coe_lt_coe_iff.mp (by simpa only [EReal.coe_zero] using hδ0)
    filter_upwards [minimizingSequence_penalty_upper hd hj hε hF hδ] with ν hν
    exact hν.trans (add_le_add le_rfl hδr.le)
  · intro F hF
    exact ⟨localizedMinimizers_penalty_zero hd hF, localizedMinimizers_wall_zero hd hF,
      localizedMinimizers_centers_zero hd hF, localizedMinimizers_norm_average_bounded hd hF⟩

end Yau.Blueprint.V03Proof
