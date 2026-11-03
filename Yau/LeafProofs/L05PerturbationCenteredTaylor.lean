import Yau.LeafProofs.L05PerturbationCoordinates
import Yau.LeafProofs.L05PerturbationTaylorBasic
import Yau.LeafProofs.L05PerturbationCenteredPullbackGeometry

open Filter Set Metric
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05Aux
open Yau.Parabolic

theorem perturb_normalize_taylor_identity {n : ℕ} {u : Point n → ℝ}
    (hu : C2 (backward 1) u) (z : Point n) {r N : ℝ} (hr : 0 < r) (hN : 0 < N)
    (hBuf : perturbClosed z.1 r z.2⊆backward 1) (q0 : ℝ) (p : Point n) :
    N*(perturbNormalize u z r N q0 p-
      perturbTaylor (backward 1) (perturbNormalize u z r N q0) (0,0) p)=
      u (perturbCenter z r p)-perturbTaylor (backward 1) u z (perturbCenter z r p) := by
  have hOrigin : ((0,0) : Point n)∈backward 1 := by norm_num [backward]
  have hD := perturb_normalize_spatialD (N := N) (q0 := q0) hu z hr hBuf hOrigin
  have hDD := perturb_normalize_spatialDD (N := N) (q0 := q0) hu z hr hBuf hOrigin
  have hT := perturb_normalize_timeD (N := N) (q0 := q0) hu z hr hBuf hOrigin
  simp only [perturbCenter_zero] at hD hDD hT
  have hV : perturbNormalize u z r N q0 (0,0)=0 := by simp [perturbNormalize,perturbCenter_zero]
  dsimp only [perturbTaylor]
  rw [hV,hD,hDD,hT]
  simp only [Prod.fst,Prod.snd,sub_zero,perturbCenter,add_sub_cancel_left,
    smul_apply,map_smul,smul_eq_mul]
  dsimp only [perturbNormalize,perturbCenter]
  field_simp [hN.ne']  <;>  ring

theorem perturb_centered_remainder_pullback {n : ℕ} {u : Point n → ℝ}
    (hu : C2 (backward 1) u) (z : Point n) {r N rho eta E0 : ℝ} (hr : 0 < r) (hN : 0 < N)
    (hBuf : perturbClosed z.1 r z.2⊆backward 1) (q0 : ℝ)
    (hError : ∀ R : ℝ, 0 < R → R ≤ rho → ∀ p∈perturbClosed (0 : Space n) R 0,
      |perturbNormalize u z r N q0 p-
        perturbTaylor (backward 1) (perturbNormalize u z r N q0) (0,0) p| ≤ E0*R^(2+eta)) :
    ∀ R : ℝ, 0 < R → R ≤ r*rho → ∀ p∈perturbClosed z.1 R z.2,
      |u p-perturbTaylor (backward 1) u z p| ≤ ((N*E0)/r^(2+eta))*R^(2+eta) := by
  intro R hR hRho p hp
  let w := perturbCenter (perturbInverseCenter z r) r⁻¹ p
  have hw : w∈perturbClosed (0 : Space n) (R/r) 0 := perturb_inverse_center_closed_mem hr z hp
  have hRadius : R/r ≤ rho := (div_le_iff₀ hr).mpr (by simpa only [mul_comm] using hRho)
  have hBound := hError (R/r) (div_pos hR hr) hRadius w hw
  have hIdentity := perturb_normalize_taylor_identity hu z hr hN hBuf q0 w
  have hInv : perturbCenter z r w=p := perturb_center_inverse_left hr z p
  rw [hInv] at hIdentity
  rw [← hIdentity,abs_mul,abs_of_pos hN]
  have hScale : N*(E0*(R/r)^(2+eta))=((N*E0)/r^(2+eta))*R^(2+eta) := by
    rw [Real.div_rpow hR.le hr.le]
    ring
  exact (mul_le_mul_of_nonneg_left hBound hN.le).trans_eq hScale

end Yau.LeafProofs.L05Aux
