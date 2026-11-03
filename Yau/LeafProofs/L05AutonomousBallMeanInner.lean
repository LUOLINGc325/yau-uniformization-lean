import Yau.LeafProofs.L05AutonomousBallMeanError

open Set Filter MeasureTheory Metric
open scoped Topology Interval
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05AutonomousAux
open Yau.Parabolic

def autoBallMeanInnerError {n : ℕ} (omega r eta : ℝ) (v : Space n → ℝ)
    (q1 q2 : ℝ → ℝ) (x : Space n) : ℝ :=
  if ‖x‖∈Icc eta (2*eta) then v x*autoGreenCutoffError (2*n) omega r ‖x‖ (q1 ‖x‖) (q2 ‖x‖) else 0

theorem auto_ballMean_inner_error_integral_bound {n : ℕ} (hn : 0 < n) (omega r : ℝ)
    {eta L B1 B2 eps D : ℝ} (heta : 0 < eta)
    (hL : 0 ≤ L) (hB1 : 0 ≤ B1) (hB2 : 0 ≤ B2) (heps : 0 ≤ eps) (hD : 0 ≤ D)
    (v : Space n → ℝ) (q1 q2 : ℝ → ℝ)
    (hv : ∀ x : Space n, ‖x‖∈Icc eta (2*eta) → |v x| ≤ L*‖x‖)
    (hM : ∀ s∈Icc eta (2*eta), |s^(2*n-1)*autoGreenPrimitive (2*n) omega r s| ≤ eps)
    (hN : ∀ s∈Icc eta (2*eta), |s^(2*n-1)*(-autoGreenIntegrand (2*n) r s/((2*n : ℝ)*omega))| ≤ D)
    (hq1 : ∀ s∈Icc eta (2*eta), |q1 s| ≤ B1/eta)
    (hq2 : ∀ s∈Icc eta (2*eta), |q2 s| ≤ B2/eta^2) :
    |∫ x : Space n, autoBallMeanInnerError omega r eta v q1 q2 x| ≤
      (2*n : ℝ)*(volume : Measure (Space n)).real (ball 0 1)*L*
        (eps*(2*B2+((2*n : ℝ)-1)*B1)+4*D*B1*eta) := by
  have hB := auto_ballMean_shell_integral_bound hn heta (by linarith : eta ≤ 2*eta)
    (g := autoBallMeanInnerError omega r eta v q1 q2)
    (C := L*eps*(2*B2+((2*n : ℝ)-1)*B1)/eta+4*L*D*B1)
    (by intro x hx; simp only [autoBallMeanInnerError,ite_eq_right hx])
    (by
      intro x hx
      rw [autoBallMeanInnerError,ite_eq_left hx]
      simpa only [Nat.cast_mul,Nat.cast_ofNat] using auto_green_inner_error_bound (by omega : 1 ≤ 2*n) omega r heta hx hL hB1 hB2 heps hD
        (hv x hx) (hM ‖x‖ hx) (by simpa only [Nat.cast_mul,Nat.cast_ofNat] using hN ‖x‖ hx) (hq1 ‖x‖ hx) (hq2 ‖x‖ hx))
  convert hB using 1
  field_simp [heta.ne']
  ; ring

theorem auto_ballMean_inner_error_tendsto {n : ℕ} (hn : 0 < n) (omega : ℝ)
    {r B1 B2 : ℝ} (hr : 0 < r) (hB1 : 0 ≤ B1) (hB2 : 0 ≤ B2)
    {f : Space n → ℝ} (hf : ∀ x∈closedBall 0 r, ContDiffAt ℝ 2 f x)
    (q1 q2 : ℝ → ℝ → ℝ)
    (hq1 : ∀ eta : ℝ, 0 < eta → ∀ s∈Icc eta (2*eta), |q1 eta s| ≤ B1/eta)
    (hq2 : ∀ eta : ℝ, 0 < eta → ∀ s∈Icc eta (2*eta), |q2 eta s| ≤ B2/eta^2) :
    Tendsto (fun eta : ℝ => ∫ x : Space n,
      autoBallMeanInnerError omega r eta (fun y => f y-f 0) (q1 eta) (q2 eta) x)
      (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨L,hL,hLin⟩ := auto_ballMean_local_linear_bound hr hf
  obtain ⟨D,hD,hControl⟩ := auto_green_inner_shell_control (by omega : 2 ≤ 2*n) omega hr
  let Z : ℝ := (2*n : ℝ)*(volume : Measure (Space n)).real (ball 0 1)
  let A : ℝ := Z*L*(2*B2+((2*n : ℝ)-1)*B1)
  let B : ℝ := Z*L*4*D*B1
  have hdim : 0 < (2*n : ℝ) := by exact_mod_cast (show 0 < 2*n by omega)
  have hZ : 0 ≤ Z := mul_nonneg hdim.le (auto_ball_volume_pos n zero_lt_one).le
  have hd0 : 0 ≤ (2*n : ℝ)-1 := by
    have hd1 : (1 : ℝ) ≤ 2*n := by exact_mod_cast (show 1 ≤ 2*n by omega)
    linarith
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  apply Metric.tendsto_nhds.mpr
  intro eps heps
  let t : ℝ := eps/(2*(A+B+1))
  have ht : 0 < t := by dsimp only [t]; positivity
  have hTeq : 2*(A+B+1)*t=eps := by dsimp only [t]; field_simp
  obtain ⟨delta,hdelta,hdeltar,hSmall⟩ := hControl t ht
  have hDelta : 0 < min delta t := lt_min hdelta ht
  have hEvent : Ioo (0 : ℝ) (min delta t)∈𝓝[>] 0 :=
    mem_nhdsGT_iff_exists_Ioo_subset.mpr ⟨min delta t,hDelta,subset_rfl⟩
  filter_upwards [hEvent] with eta heta
  have hed : eta < delta := heta.2.trans_le (min_le_left _ _)
  have het : eta < t := heta.2.trans_le (min_le_right _ _)
  have hBound := auto_ballMean_inner_error_integral_bound hn omega r heta.1 hL.le hB1 hB2 ht.le hD.le
    (fun y => f y-f 0) (q1 eta) (q2 eta)
    (by
      intro x hx
      apply hLin x
      simp only [mem_closedBall,dist_zero_right]
      linarith [hx.2])
    (fun s hs => (hSmall eta heta.1 hed s hs).1)
    (fun s hs => by simpa only [Nat.cast_mul,Nat.cast_ofNat] using (hSmall eta heta.1 hed s hs).2)
    (hq1 eta heta.1) (hq2 eta heta.1)
  have hR : (2*n : ℝ)*(volume : Measure (Space n)).real (ball 0 1)*L*
      (t*(2*B2+((2*n : ℝ)-1)*B1)+4*D*B1*eta)=A*t+B*eta := by
    dsimp only [A,B,Z]; ring
  rw [hR] at hBound
  have hLast : A*t+B*eta < eps := by nlinarith [mul_le_mul_of_nonneg_left het.le hB]
  simpa only [Real.dist_eq,sub_zero] using hBound.trans_lt hLast

end Yau.LeafProofs.L05AutonomousAux
