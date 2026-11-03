import Yau.LeafProofs.L05PerturbationNearJets
import Yau.LeafProofs.L05PerturbationPairHolder

open Filter Set Metric
open scoped Topology ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05Aux
open Yau.Parabolic

theorem perturb_highest_jet_holder {n : ℕ} {D Q : Set (Point n)} {u : Point n → ℝ}
    (hu : C2 D u) (hQD : Q⊆D) {eta E rstar J : ℝ} (heta : 0 ≤ eta) (heta1 : eta ≤ 1)
    (hrstar : 0 < rstar) (hE : 0 ≤ E) (hJ : 0 ≤ J)
    (hBounds : ∀ z∈Q, ‖spatialDD u z‖ ≤ J ∧ |timeD D u z| ≤ J)
    (hApprox : ∀ z∈Q, ∀ r : ℝ, 0 < r → r ≤ rstar → ∀ p∈perturbClosed z.1 r z.2,
      |u p-perturbTaylor D u z p| ≤ E*r^(2+eta)) :
    HolderBound eta Q (spatialDD u) (1+J+8*E*4^(2+eta)+2*J*(4/rstar)^eta) ∧
      HolderBound eta Q (timeD D u) (1+J+8*E*4^(2+eta)+2*J*(4/rstar)^eta) := by
  have hNearC : 0 ≤ 8*E*4^(2+eta) := by positivity
  constructor
  · apply perturb_holder_of_near_pairs heta heta1 hrstar hJ hNearC (spatialDD u)
      (fun p hp => (hBounds p hp).1)
    intro p hp q hq hd hNear
    exact (perturb_near_jet_bounds hu hQD hE hApprox hp hq hd hNear).2
  · apply perturb_holder_of_near_pairs heta heta1 hrstar hJ hNearC (timeD D u)
      (fun p hp => by simpa only [Real.norm_eq_abs] using (hBounds p hp).2)
    intro p hp q hq hd hNear
    rw [Real.norm_eq_abs]
    have hTime := (perturb_near_jet_bounds hu hQD hE hApprox hp hq hd hNear).1
    have hFour : 0 ≤ 4*E*4^(2+eta)*(parabolicDistance p q)^eta := by positivity
    nlinarith only [hTime,hFour]

end Yau.LeafProofs.L05Aux
