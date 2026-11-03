import Yau.LeafProofs.L05PerturbationCoordinates
import Yau.LeafProofs.L05PerturbationRescaledOperator

open Filter Set Metric
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05Aux
open Yau.Parabolic

theorem perturb_centered_smul_norm {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] (a : ℝ) (v : V) : ‖a • v‖ = |a| * ‖v‖ := by
  rw [norm_smul,Real.norm_eq_abs]

theorem perturb_normalized_origin_hessian_pullback {n : ℕ} {u : Point n → ℝ}
    (hu : C2 (backward 1) u) (z : Point n) {r N q0 SA : ℝ}
    (hr : 0 < r) (hN : 0 < N) (hBuf : perturbClosed z.1 r z.2 ⊆ backward 1)
    (hNorm : ‖hessian (perturbNormalize u z r N q0) (0,0)‖ ≤ SA) :
    ‖hessian u z‖ ≤ (N/r^2)*SA := by
  have hOrigin : ((0,0) : Point n) ∈ backward 1 := by norm_num [backward]
  have hH := perturb_normalize_hessian (N := N) (q0 := q0) hu z hr hBuf hOrigin
  simp only [perturbCenter_zero] at hH
  have hPref : 0 < r^2/N := div_pos (sq_pos_of_pos hr) hN
  rw [hH,perturb_sym_smul_norm,abs_of_pos hPref] at hNorm
  have hCancel : (N/r^2)*(r^2/N) = 1 := by field_simp [hr.ne',hN.ne']
  have hScaled := mul_le_mul_of_nonneg_left hNorm (div_pos hN (sq_pos_of_pos hr)).le
  rwa [← mul_assoc,hCancel,one_mul] at hScaled

theorem perturb_normalized_origin_jet_pullback {n : ℕ} {u : Point n → ℝ}
    (hu : C2 (backward 1) u) (z : Point n) {r N q0 Sb SA Sq Q0 : ℝ}
    (hr : 0 < r) (hN : 0 < N) (hBuf : perturbClosed z.1 r z.2⊆backward 1)
    (hDNorm : ‖spatialD (perturbNormalize u z r N q0) (0,0)‖ ≤ Sb)
    (hDDNorm : ‖spatialDD (perturbNormalize u z r N q0) (0,0)‖ ≤ SA)
    (hTNorm : |timeD (backward 1) (perturbNormalize u z r N q0) (0,0)| ≤ Sq)
    (hq : |q0| ≤ Q0) :
    ‖spatialD u z‖ ≤ (N/r)*Sb ∧ ‖spatialDD u z‖ ≤ (N/r^2)*SA ∧
      |timeD (backward 1) u z| ≤ Q0+(N/r^2)*Sq := by
  have hOrigin : ((0,0) : Point n)∈backward 1 := by norm_num [backward]
  have hD := perturb_normalize_spatialD (N := N) (q0 := q0) hu z hr hBuf hOrigin
  have hDD := perturb_normalize_spatialDD (N := N) (q0 := q0) hu z hr hBuf hOrigin
  have hT := perturb_normalize_timeD (N := N) (q0 := q0) hu z hr hBuf hOrigin
  simp only [perturbCenter_zero] at hD hDD hT
  have hPrefD : 0 < r/N := div_pos hr hN
  have hPrefDD : 0 < r^2/N := div_pos (sq_pos_of_pos hr) hN
  have hCancelD : (N/r)*(r/N)=1 := by field_simp [hr.ne',hN.ne']
  have hCancelDD : (N/r^2)*(r^2/N)=1 := by field_simp [hr.ne',hN.ne']
  have hD' : (r/N)*‖spatialD u z‖ ≤ Sb := by
    rw [hD,norm_smul,Real.norm_eq_abs,abs_of_pos hPrefD] at hDNorm
    exact hDNorm
  have hDD' : (r^2/N)*‖spatialDD u z‖ ≤ SA := by
    have hScale := perturb_centered_smul_norm (r^2/N) (spatialDD u z)
    rw [hDD,hScale,abs_of_pos hPrefDD] at hDDNorm
    exact hDDNorm
  have hT' : (r^2/N)*|timeD (backward 1) u z-q0| ≤ Sq := by
    rw [hT,abs_mul,abs_of_pos hPrefDD] at hTNorm
    exact hTNorm
  have hDu := mul_le_mul_of_nonneg_left hD' (div_pos hN hr).le
  have hDDu := mul_le_mul_of_nonneg_left hDD' (div_pos hN (sq_pos_of_pos hr)).le
  have hTu := mul_le_mul_of_nonneg_left hT' (div_pos hN (sq_pos_of_pos hr)).le
  rw [← mul_assoc,hCancelD,one_mul] at hDu
  rw [← mul_assoc,hCancelDD,one_mul] at hDDu hTu
  refine ⟨hDu,hDDu,?_⟩
  have hTri := abs_add_le (timeD (backward 1) u z-q0) q0
  rw [sub_add_cancel] at hTri
  linarith only [hTu,hq,hTri]

end Yau.LeafProofs.L05Aux
