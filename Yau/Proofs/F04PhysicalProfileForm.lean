import Yau.Proofs.F04BilinearQuadraticBound
import Yau.Proofs.F04CompactLpProfiles

open Set
open scoped Topology

noncomputable section

set_option maxHeartbeats 1000000

namespace Yau.F04Proof

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Evaluate a bilinear continuous-time profile at the clamped physical time.
This gives one globally defined actual form without coefficient choices outside
 the physical time slab. -/
def physicalProfileForm {T : ℝ} (hT : 0 ≤ T)
    (Φ : V →L[ℝ] V →L[ℝ] C(Icc (0 : ℝ) T, ℝ)) (t : ℝ) : V →L[ℝ] V →L[ℝ] ℝ :=
  (ContinuousLinearMap.compL ℝ V C(Icc (0 : ℝ) T, ℝ) ℝ
    (ContinuousMap.evalCLM ℝ ⟨timeClamp T hT t, timeClamp_mem T hT t⟩)).comp Φ

theorem physicalProfileForm_apply {T : ℝ} (hT : 0 ≤ T)
    (Φ : V →L[ℝ] V →L[ℝ] C(Icc (0 : ℝ) T, ℝ)) (t : ℝ) (u v : V) :
    physicalProfileForm hT Φ t u v = Φ u v ⟨timeClamp T hT t, timeClamp_mem T hT t⟩ := rfl

theorem physicalProfileForm_continuous {T : ℝ} (hT : 0 ≤ T)
    (Φ : V →L[ℝ] V →L[ℝ] C(Icc (0 : ℝ) T, ℝ)) (u v : V) :
    Continuous (fun t => physicalProfileForm hT Φ t u v) :=
  (Φ u v).continuous.comp ((continuous_timeClamp T hT).subtype_mk _)

theorem physicalProfileForm_norm_le {T : ℝ} (hT : 0 ≤ T)
    (Φ : V →L[ℝ] V →L[ℝ] C(Icc (0 : ℝ) T, ℝ)) {C : ℝ}
    (hC : 0 ≤ C) (hΦ : ∀ u v, ‖Φ u v‖ ≤ C * ‖u‖ * ‖v‖) (t : ℝ) : ‖physicalProfileForm hT Φ t‖ ≤ C := by
  apply (physicalProfileForm hT Φ t).opNorm_le_bound₂ hC
  intro u v
  change ‖Φ u v ⟨timeClamp T hT t, timeClamp_mem T hT t⟩‖ ≤ C * ‖u‖ * ‖v‖
  exact ((Φ u v).norm_coe_le_norm _).trans (hΦ u v)

end Yau.F04Proof
