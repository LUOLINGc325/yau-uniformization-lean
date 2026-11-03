import Yau.LeafProofs.L05PerturbationJetCoefficients

open Filter Set Metric
open scoped Topology ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05Aux
open Yau.Parabolic

theorem perturb_near_jet_bounds {n : ℕ} {D Q : Set (Point n)} {u : Point n → ℝ}
    (hu : C2 D u) (hQD : Q⊆D) {eta E rstar : ℝ} (hE : 0 ≤ E)
    (hApprox : ∀ z∈Q, ∀ r : ℝ, 0 < r → r ≤ rstar → ∀ p∈perturbClosed z.1 r z.2,
      |u p-perturbTaylor D u z p| ≤ E*r^(2+eta))
    {z w : Point n} (hz : z∈Q) (hw : w∈Q)
    (hd : 0 < parabolicDistance z w) (hNear : parabolicDistance z w ≤ rstar/4) :
    |timeD D u z-timeD D u w| ≤ (4*E*4^(2+eta))*(parabolicDistance z w)^eta ∧
      ‖spatialDD u z-spatialDD u w‖ ≤ (8*E*4^(2+eta))*(parabolicDistance z w)^eta := by
  let d := parabolicDistance z w
  have hd0 : 0 < d := hd
  have hRadius : 4*d ≤ rstar := by linarith only [hNear]
  have hTaylor : ∀ p∈perturbClosed z.1 d (min z.2 w.2),
      |perturbTaylor D u z p-perturbTaylor D u w p| ≤ 2*E*(4*d)^(2+eta) := by
    intro p hp
    have hBoth := perturb_common_cylinder z w hp
    have hZ := hApprox z hz (4*d) (by positivity) hRadius p hBoth.1
    have hW := hApprox w hw (4*d) (by positivity) hRadius p hBoth.2
    have hTri : |perturbTaylor D u z p-perturbTaylor D u w p| ≤
        |u p-perturbTaylor D u z p|+|u p-perturbTaylor D u w p| := by
      have hh := abs_sub (u p-perturbTaylor D u w p) (u p-perturbTaylor D u z p)
      have hId : (u p-perturbTaylor D u w p)-(u p-perturbTaylor D u z p)=
          perturbTaylor D u z p-perturbTaylor D u w p := by ring
      rw [hId] at hh
      linarith only [hh]
    linarith only [hTri,hZ,hW]
  have hB : 0 ≤ 2*E*(4*d)^(2+eta) := mul_nonneg (by positivity) (Real.rpow_nonneg (by positivity) _)
  obtain ⟨hTime,hSpace⟩ := perturb_taylor_coefficient_bounds hu (hQD hz) (hQD hw) hd0 hB z.1 hTaylor
  have hPower : (4*d)^(2+eta)=4^(2+eta)*(d^2*d^eta) := by
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) hd0.le,Real.rpow_add hd0,Real.rpow_two]
  have hTimeEq : 2*(2*E*(4*d)^(2+eta))/d^2=(4*E*4^(2+eta))*d^eta := by
    rw [hPower]
    field_simp [hd0.ne']
    ring
  have hSpaceEq : 4*(2*E*(4*d)^(2+eta))/d^2=(8*E*4^(2+eta))*d^eta := by
    rw [hPower]
    field_simp [hd0.ne']
    ring
  exact ⟨hTime.trans_eq hTimeEq,hSpace.trans_eq hSpaceEq⟩

end Yau.LeafProofs.L05Aux
