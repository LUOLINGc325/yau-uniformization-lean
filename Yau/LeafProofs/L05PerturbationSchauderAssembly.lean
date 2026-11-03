import Yau.LeafProofs.L05PerturbationJetHolder
import Yau.LeafProofs.L16InteriorPlateauJets

open Filter Set Metric
open scoped Topology ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05Aux
open Yau.Parabolic

theorem perturb_schauder_of_centered_estimates {n : ℕ} {u : Point n → ℝ}
    (hu : C2 (backward 1) u) {eta E rstar J : ℝ} (heta : 0 ≤ eta) (heta1 : eta ≤ 1)
    (hrstar : 0 < rstar) (hE : 0 ≤ E) (hJ : 0 ≤ J)
    (hBounds : ∀ z∈backward (3/4), |u z| ≤ J ∧ ‖spatialD u z‖ ≤ J ∧
      ‖spatialDD u z‖ ≤ J ∧ |timeD (backward 1) u z| ≤ J)
    (hApprox : ∀ z∈backward (3/4), ∀ r : ℝ, 0 < r → r ≤ rstar →
      ∀ p∈perturbClosed z.1 r z.2,
        |u p-perturbTaylor (backward 1) u z p| ≤ E*r^(2+eta)) :
    SchauderBound eta (backward (3/4)) u (1+J+8*E*4^(2+eta)+2*J*(4/rstar)^eta) := by
  let C := 1+J+8*E*4^(2+eta)+2*J*(4/rstar)^eta
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hCJ : J ≤ C := by
    have h1 : 0 ≤ 8*E*4^(2+eta) := by positivity
    have h2 : 0 ≤ 2*J*(4/rstar)^eta := by positivity
    dsimp only [C]
    linarith
  have hQD : backward (n := n) (3/4)⊆backward 1 := by
    intro p hp
    refine ⟨ball_subset_ball (by norm_num) hp.1,?_,hp.2.2⟩
    have hh := hp.2.1
    change -(1 : ℝ)^2 < p.2
    norm_num at hh ⊢
    linarith
  have hHigh := perturb_highest_jet_holder hu hQD heta heta1 hrstar hE hJ
    (fun z hz => ⟨(hBounds z hz).2.2.1,(hBounds z hz).2.2.2⟩) hApprox
  have hRestr : ∀ p∈backward (n := n) (3/4),
      timeD (backward (3/4)) u p=timeD (backward 1) u p := by
    intro p hp
    exact L16Aux.timeD_backward_restrict_radius (by norm_num) (by norm_num) hu hp
  refine ⟨L16Aux.c2_backward_restrict_radius (by norm_num) (by norm_num) hu,hC,?_,hHigh.1,?_⟩
  · intro p hp
    exact ⟨((hBounds p hp).1).trans hCJ,((hBounds p hp).2.1).trans hCJ⟩
  · refine ⟨hHigh.2.1,?_,?_⟩
    · intro p hp
      rw [hRestr p hp]
      exact hHigh.2.2.1 p hp
    · intro p hp q hq
      rw [hRestr p hp,hRestr q hq]
      exact hHigh.2.2.2 p hp q hq

end Yau.LeafProofs.L05Aux
