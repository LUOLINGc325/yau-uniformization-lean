import Yau.LeafProofs.L05AutonomousBallMeanInner

open Set Filter MeasureTheory Metric
open scoped Topology Interval
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05AutonomousAux
open Yau.Parabolic

theorem auto_green_cutoff_error_abs {d : ℕ} (hd : 1 ≤ d) (omega r : ℝ)
    {s : ℝ} (hs : 0 < s) (q1 q2 : ℝ) :
    |autoGreenCutoffError d omega r s q1 q2| ≤
      |autoGreenPrimitive d omega r s| *|q2|+
      2*|-autoGreenIntegrand d r s/((d : ℝ)*omega)| *|q1|+
      ((d : ℝ)-1)/s*|autoGreenPrimitive d omega r s| *|q1| := by
  have hd0 : 0 ≤ (d : ℝ)-1 := by
    have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hCoeff : 0 ≤ ((d : ℝ)-1)/s := div_nonneg hd0 hs.le
  have h := (abs_add_le (autoGreenPrimitive d omega r s*q2+
    2*(-autoGreenIntegrand d r s/((d : ℝ)*omega))*q1)
    (((d : ℝ)-1)/s*autoGreenPrimitive d omega r s*q1)).trans
    (add_le_add (abs_add_le (autoGreenPrimitive d omega r s*q2)
      (2*(-autoGreenIntegrand d r s/((d : ℝ)*omega))*q1)) le_rfl)
  simpa only [autoGreenCutoffError,abs_mul,abs_of_nonneg hCoeff,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] using h

theorem auto_green_outer_error_bound {d : ℕ} (hd : 1 ≤ d) (omega : ℝ)
    {r eta s C B1 B2 q1 q2 : ℝ} (hr : 0 < r) (heta : 0 < eta) (hetar : eta < r/8)
    (hs : s∈Icc (r-2*eta) (r-eta)) (hC : 0 ≤ C) (hB1 : 0 ≤ B1) (hB2 : 0 ≤ B2)
    (hK : |autoGreenPrimitive d omega r s| ≤ C*(r-s)^2)
    (hKp : |-autoGreenIntegrand d r s/((d : ℝ)*omega)| ≤ C*(r-s))
    (hq1 : |q1| ≤ B1/eta) (hq2 : |q2| ≤ B2/eta^2) :
    |autoGreenCutoffError d omega r s q1 q2| ≤ C*(4*B2+((d : ℝ)+3)*B1) := by
  have hsHalf : r/2 ≤ s := by linarith [hs.1]
  have hsR : s ≤ r := by linarith [hs.2]
  have hsp : 0 < s := (half_pos hr).trans_le hsHalf
  have hDist : r-s ≤ 2*eta := by linarith [hs.1]
  have hd0 : 0 ≤ (d : ℝ)-1 := by
    have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hCoeff : ((d : ℝ)-1)/s ≤ 2*((d : ℝ)-1)/r := by
    have h := div_le_div_of_nonneg_left hd0 (half_pos hr) hsHalf
    convert h using 1 <;> field_simp <;> ring
  have hKv : |autoGreenPrimitive d omega r s| ≤ 4*C*eta^2 := by
    apply hK.trans
    have hSquare : (r-s)^2 ≤ (2*eta)^2 := pow_le_pow_left₀ (sub_nonneg.mpr hsR) hDist 2
    nlinarith [mul_le_mul_of_nonneg_left hSquare hC]
  have hKpv : |-autoGreenIntegrand d r s/((d : ℝ)*omega)| ≤ 2*C*eta :=
    hKp.trans (by nlinarith [mul_le_mul_of_nonneg_left hDist hC])
  have hE := auto_green_cutoff_error_abs hd omega r hsp q1 q2
  calc
    _ ≤ (4*C*eta^2)*(B2/eta^2)+2*(2*C*eta)*(B1/eta)+
        (2*((d : ℝ)-1)/r)*(4*C*eta^2)*(B1/eta) := by
      apply hE.trans
      gcongr
    _ = 4*C*B2+4*C*B1+8*((d : ℝ)-1)*C*B1*eta/r := by field_simp [heta.ne']; ring
    _ ≤ 4*C*B2+4*C*B1+((d : ℝ)-1)*C*B1 := by
      have hLast : 8*((d : ℝ)-1)*C*B1*eta/r ≤ ((d : ℝ)-1)*C*B1 := by
        rw [div_le_iff₀ hr]
        have h := mul_le_mul_of_nonneg_left (show 8*eta ≤ r by linarith)
          (mul_nonneg (mul_nonneg hd0 hC) hB1)
        nlinarith
      exact add_le_add le_rfl hLast
    _ = _ := by ring

def autoBallMeanOuterError {n : ℕ} (omega r eta : ℝ) (v : Space n → ℝ)
    (q1 q2 : ℝ → ℝ) (x : Space n) : ℝ :=
  if ‖x‖∈Icc (r-2*eta) (r-eta) then
    v x*autoGreenCutoffError (2*n) omega r ‖x‖ (q1 ‖x‖) (q2 ‖x‖) else 0

theorem auto_ballMean_outer_error_integral_bound {n : ℕ} (hn : 0 < n) (omega : ℝ)
    {r eta C L B1 B2 : ℝ} (hr : 0 < r) (heta : 0 < eta) (hetar : eta < r/8)
    (hC : 0 ≤ C) (hL : 0 ≤ L) (hB1 : 0 ≤ B1) (hB2 : 0 ≤ B2)
    (hK : ∀ s∈Icc (r/2) r, |-autoGreenIntegrand (2*n) r s/((2*n : ℝ)*omega)| ≤ C*(r-s) ∧
      |autoGreenPrimitive (2*n) omega r s| ≤ C*(r-s)^2)
    (v : Space n → ℝ) (hv : ∀ x∈closedBall 0 r, |v x| ≤ L*‖x‖)
    (q1 q2 : ℝ → ℝ)
    (hq1 : ∀ s∈Icc (r-2*eta) (r-eta), |q1 s| ≤ B1/eta)
    (hq2 : ∀ s∈Icc (r-2*eta) (r-eta), |q2 s| ≤ B2/eta^2) :
    |∫ x : Space n, autoBallMeanOuterError omega r eta v q1 q2 x| ≤
      (2*n : ℝ)*(volume : Measure (Space n)).real (ball 0 1)*
        (r^(2*n-1)*(L*r)*C*(4*B2+((2*n : ℝ)+3)*B1))*eta := by
  have hB := auto_ballMean_shell_integral_bound hn (by linarith : 0 < r-2*eta)
    (by linarith : r-2*eta ≤ r-eta)
    (g := autoBallMeanOuterError omega r eta v q1 q2)
    (C := r^(2*n-1)*(L*r)*C*(4*B2+((2*n : ℝ)+3)*B1))
    (by intro x hx; simp only [autoBallMeanOuterError,ite_eq_right hx])
    (by
      intro x hx
      have hxR : ‖x‖ ≤ r := by linarith [hx.2]
      have hxH : ‖x‖∈Icc (r/2) r := ⟨by linarith [hx.1],hxR⟩
      have hPoint : |autoGreenCutoffError (2*n) omega r ‖x‖ (q1 ‖x‖) (q2 ‖x‖)| ≤
          C*(4*B2+((2*n : ℝ)+3)*B1) := by
        simpa only [Nat.cast_mul,Nat.cast_ofNat] using auto_green_outer_error_bound
          (by omega : 1 ≤ 2*n) omega hr heta hetar hx hC hB1 hB2 (hK ‖x‖ hxH).2
          (by simpa only [Nat.cast_mul,Nat.cast_ofNat] using (hK ‖x‖ hxH).1)
          (hq1 ‖x‖ hx) (hq2 ‖x‖ hx)
      have hV : |v x| ≤ L*r := (hv x (by simpa only [mem_closedBall,dist_zero_right] using hxR)).trans
        (mul_le_mul_of_nonneg_left hxR hL)
      rw [autoBallMeanOuterError,ite_eq_left hx,abs_mul]
      calc
        _ = (‖x‖^(2*n-1)*|v x|)*|autoGreenCutoffError (2*n) omega r ‖x‖ (q1 ‖x‖) (q2 ‖x‖)| := by ring
        _ ≤ r^(2*n-1)*(L*r)*(C*(4*B2+((2*n : ℝ)+3)*B1)) := by
          apply mul_le_mul ?_ hPoint (abs_nonneg _) (by positivity)
          exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg x) hxR _) hV (abs_nonneg _)
            (pow_nonneg hr.le _)
        _ = _ := by ring)
  convert hB using 1 <;> ring

theorem auto_ballMean_outer_error_tendsto {n : ℕ} (hn : 0 < n) (omega : ℝ)
    {r B1 B2 : ℝ} (hr : 0 < r) (hB1 : 0 ≤ B1) (hB2 : 0 ≤ B2)
    {f : Space n → ℝ} (hf : ∀ x∈closedBall 0 r, ContDiffAt ℝ 2 f x)
    (q1 q2 : ℝ → ℝ → ℝ)
    (hq1 : ∀ eta : ℝ, 0 < eta → ∀ s∈Icc (r-2*eta) (r-eta), |q1 eta s| ≤ B1/eta)
    (hq2 : ∀ eta : ℝ, 0 < eta → ∀ s∈Icc (r-2*eta) (r-eta), |q2 eta s| ≤ B2/eta^2) :
    Tendsto (fun eta : ℝ => ∫ x : Space n,
      autoBallMeanOuterError omega r eta (fun y => f y-f 0) (q1 eta) (q2 eta) x)
      (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨L,hL,hLin⟩ := auto_ballMean_local_linear_bound hr hf
  obtain ⟨C,hC,hK⟩ := auto_green_outer_bounds (2*n) omega hr
  let W : ℝ := (2*n : ℝ)*(volume : Measure (Space n)).real (ball 0 1)*
    (r^(2*n-1)*(L*r)*C*(4*B2+((2*n : ℝ)+3)*B1))
  have hT : Tendsto (fun eta : ℝ => W*eta) (𝓝[>] 0) (𝓝 0) := by
    have hid : Tendsto (fun eta : ℝ => eta) (𝓝[>] 0) (𝓝 0) :=
      tendsto_id.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    simpa only [mul_zero] using (tendsto_const_nhds (x := W)).mul hid
  apply squeeze_zero_norm' ?_ hT
  have hEvent : Ioo (0 : ℝ) (r/8)∈𝓝[>] 0 :=
    mem_nhdsGT_iff_exists_Ioo_subset.mpr ⟨r/8,(show 0 < r/8 by positivity),subset_rfl⟩
  filter_upwards [hEvent] with eta heta
  simpa only [Real.norm_eq_abs,W] using auto_ballMean_outer_error_integral_bound hn omega hr heta.1
    heta.2 hC.le hL.le hB1 hB2
    (fun s hs => by simpa only [Nat.cast_mul,Nat.cast_ofNat] using hK s hs)
    (fun y => f y-f 0) hLin (q1 eta) (q2 eta) (hq1 eta heta.1) (hq2 eta heta.1)

end Yau.LeafProofs.L05AutonomousAux
