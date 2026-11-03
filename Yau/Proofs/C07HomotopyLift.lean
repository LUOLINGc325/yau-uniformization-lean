import Yau.Proofs.C07JointLift

/-! The endpoints of the actual lifted rows of a fixed-endpoint homotopy agree. -/

open scoped Topology

noncomputable section

namespace Yau.Proofs.C07Aux

open Yau Yau.Blueprint

variable {n : ℕ} {M : ComplexManifold n}

theorem chart_lift_homotopy_endpoint
    {Φ : ComplexVector n → M.Carrier} {r : ℝ} (hΦ : IsLocalBiholomorphism Φ r)
    (H : C(unitInterval × unitInterval, M.Carrier))
    (η : unitInterval × unitInterval → ComplexVector n)
    (hball : ∀ p, η p ∈ Metric.ball 0 r) (hlift : ∀ p, Φ (η p) = H p)
    (hstart : ∀ s, η (0, s) = 0)
    (hrows : ∀ s, Continuous (fun t => η (t, s)))
    (htarget : ∀ s, H (1, s) = H (1, 0)) :
    ∀ s, η (1, s) = η (1, 0) := by
  have hstartc : Continuous (fun s => η (0, s)) :=
    continuous_const.congr fun s => (hstart s).symm
  have hjoint := chart_lift_joint_continuous hΦ H η hball hlift hstartc hrows
  have hend : Continuous (fun s => η (1, s)) :=
    hjoint.comp (continuous_const.prodMk continuous_id)
  have hcomp : Φ ∘ (fun s => η (1, s)) = Φ ∘ (fun _ => η (1, 0)) := by
    funext s
    exact (hlift (1, s)).trans ((htarget s).trans (hlift (1, 0)).symm)
  have heq := chart_lifts_unique hΦ hend continuous_const
    (fun s => hball (1, s)) (fun _ => hball (1, 0)) hcomp (0 : unitInterval) rfl
  exact fun s => congrFun heq s

end Yau.Proofs.C07Aux
