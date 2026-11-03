import Yau.LeafProofs.L05PucciHarnackDoublingChain
import Yau.LeafProofs.L05PucciHarnackMovingCenter
import Yau.LeafProofs.L05PucciHarnackScaledDensity

open Filter MeasureTheory Set
open scoped Topology ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05Aux
open Yau.Parabolic

theorem harnack_positive_ball_reaches_low_point
    {n : ℕ} {ell L : ℝ} (hell : 0 < ell) (hL : ell ≤ L)
    {u : Point n → ℝ} (hu : harnackSuper0 ell L u)
    {c : Space n} {r t0 H : ℝ}
    (hc : ‖c‖ ≤ 3/8) (hr : 0 < r) (hr1 : r ≤ 1/128)
    (ht : t0∈Icc (-7/8 : ℝ) (-13/32)) (hH : 0 < H)
    (hBall : ∀ x∈Metric.closedBall c r, H ≤ u (x,t0))
    {z : Point n} (hz : z∈harnackQplus n) :
    harnackPropagationC n ell L*r^(harnackPropagationExponent n ell L)*H ≤ u z := by
  obtain ⟨N,_,hRadiusLo,hRadiusHi,hTimeLo,hTimeHi,hSeed⟩ :=
    harnack_doubling_chain hell hL hu hc hr hr1 ht hH hBall
  have hTime : harnackDoublingTime r t0 N∈Icc (-7/8 : ℝ) (-3/8) :=
    ⟨by linarith [ht.1],by linarith [ht.2]⟩
  have hAmp : 0 < (harnackDoublingBeta n ell L)^N*H :=
    mul_pos (pow_pos (harnack_doublingBeta_bounds hell).1 _) hH
  have hSmallSeed : ∀ x∈Metric.closedBall c (1/128),
      (harnackDoublingBeta n ell L)^N*H ≤ u (x,harnackDoublingTime r t0 N) := by
    intro x hx
    exact hSeed x (Metric.closedBall_subset_closedBall (by linarith : (1/128 : ℝ) ≤ harnackDoublingRadius r N) hx)
  have hMove := harnack_positive_ball_moves hell hL hu hc hTime hAmp hSmallSeed hz
  have hFactor := harnack_doubling_amplitude_lower (n := n) (L := L) hell hr N
    (by change harnackDoublingRadius r N ≤ 1; linarith)
  calc
    _ ≤ harnackPropagationC n ell L*((harnackDoublingBeta n ell L)^N*H) := by
      have h := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hFactor hH.le)
        (harnack_propagationC_pos n ell L).le
      simpa only [mul_assoc] using h
    _ ≤ u z := hMove

theorem harnack_dense_cube_radius_bound
    {n : ℕ} (hn : 0 < n) {ell L : ℝ} (hell : 0 < ell) (hL : ell ≤ L)
    {u : Point n → ℝ} (hu : harnackSuper0 ell L u)
    {c : Space n} {r a H : ℝ} (hc : ‖c‖ ≤ 3/8) (hr : 0 < r) (hr1 : r ≤ 1/128)
    (ht : a+r^2∈Icc (-7/8 : ℝ) (-13/32)) (hH : 0 < H)
    (hclosed : harnackClosed c (harnackLocalRadius n*r) a (2*r^2) ⊆ unitClosed n)
    (hopen : harnackOpen c (harnackLocalRadius n*r) a (2*r^2) ⊆ unitOpen n)
    (hdense : (1-harnackDelta n ell L)*harnackMu (harnackBox c r a) <
      harnackMu (harnackBox c r a ∩ {z | H < u z}))
    {z : Point n} (hz : z∈harnackQplus n) (hu1 : u z ≤ 1) :
    r^(harnackPropagationExponent n ell L) ≤
      harnackLocalM n ell L/(harnackPropagationC n ell L*H) := by
  have hM : 0 < harnackLocalM n ell L := lt_trans (by norm_num) (harnack_localM_gt_one n ell L)
  have hHnorm : 0 < H/harnackLocalM n ell L := div_pos hH hM
  have hThreshold : harnackLocalM n ell L*(H/harnackLocalM n ell L)=H := by field_simp
  have hDenseNorm : (1-harnackDelta n ell L)*harnackMu (harnackBox c r a) <
      harnackMu (harnackBox c r a ∩ {z | harnackLocalM n ell L*(H/harnackLocalM n ell L) < u z}) := by
    simpa only [hThreshold] using hdense
  have hForward := harnack_cube_density_forward hell hL hu hr hHnorm hclosed hopen hDenseNorm
  have hd : (1 : ℝ) ≤ 2*Real.sqrt (2*n) := by
    have hNat : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hs := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2*n)
    nlinarith [Real.sqrt_nonneg (2*n)]
  have hBall : ∀ x∈Metric.closedBall c r, H/harnackLocalM n ell L ≤ u (x,a+r^2) := by
    intro x hx
    have hR : r ≤ 2*Real.sqrt (2*n)*r := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hd hr.le
    exact (hForward (x,a+r^2) ⟨Metric.closedBall_subset_closedBall hR hx,le_rfl,
      by nlinarith [sq_nonneg r]⟩).le
  have hProp := harnack_positive_ball_reaches_low_point hell hL hu hc hr hr1 ht hHnorm hBall hz
  have hBound := hProp.trans hu1
  have hMult := mul_le_mul_of_nonneg_right hBound hM.le
  have hEq : (harnackPropagationC n ell L*r^(harnackPropagationExponent n ell L)*
      (H/harnackLocalM n ell L))*harnackLocalM n ell L=
      r^(harnackPropagationExponent n ell L)*(harnackPropagationC n ell L*H) := by
    field_simp [hM.ne']
  rw [hEq,one_mul] at hMult
  exact (le_div_iff₀ (mul_pos (harnack_propagationC_pos n ell L) hH)).mpr hMult

end Yau.LeafProofs.L05Aux
