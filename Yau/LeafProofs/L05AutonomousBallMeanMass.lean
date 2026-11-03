import Yau.LeafProofs.L05AutonomousBallMeanGreen

open Set Filter MeasureTheory Metric
open scoped Topology ContDiff
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05AutonomousAux
open Yau.Parabolic

def autoBallMeanOmega (n : ℕ) : ℝ := (volume : Measure (Space n)).real (ball 0 1)

theorem auto_ballMean_omega_pos (n : ℕ) : 0 < autoBallMeanOmega n := auto_ball_volume_pos n zero_lt_one

theorem auto_ball_mean_green_zero {n : ℕ} (hn : 0 < n) {r : ℝ} (hr : 0 < r)
    {f : Space n → ℝ} (hf : ∀ x∈closedBall 0 r, ContDiffAt ℝ 2 f x) :
    (∫ x in ball (0 : Space n) r, f x)/(volume : Measure (Space n)).real (ball 0 r)-f 0=
      ∫ x : Space n, autoRadialGreen (2*n) (autoBallMeanOmega n) r ‖x‖*autoBallMeanLaplacian f x := by
  have hG := auto_ballMean_green_identity hn (auto_ballMean_omega_pos n) hr hf
  have hVol : (volume : Measure (Space n)).real (ball 0 r)=autoBallMeanOmega n*r^(2*n) := by
    rw [auto_ball_volume_scale n hr]
    exact mul_comm _ _
  rw [← hVol] at hG
  have hcf : ContinuousOn f (closedBall 0 r) := fun x hx => (hf x hx).continuousAt.continuousWithinAt
  have hF : IntegrableOn f (ball 0 r) volume :=
    (hcf.integrableOn_compact (isCompact_closedBall 0 r)).mono_set ball_subset_closedBall
  have hConst : IntegrableOn (fun _ : Space n => f 0) (ball 0 r) volume :=
    integrableOn_const measure_ball_lt_top.ne
  rw [integral_sub hF hConst,setIntegral_const,smul_eq_mul] at hG
  convert hG using 1
  field_simp [(auto_ball_volume_pos n hr).ne']
  <;> ring

theorem auto_ballMean_kernel_mass {n : ℕ} (hn : 0 < n) {r : ℝ} (hr : 0 < r) :
    (∫ x : Space n, autoRadialGreen (2*n) (autoBallMeanOmega n) r ‖x‖)=
      r^2/(2*((2*n : ℝ)+2)) := by
  have hC : ContDiff ℝ 2 (fun x : Space n => ‖x‖^2) := contDiff_norm_sq ℝ
  have hG := auto_ball_mean_green_zero hn hr (fun x _ => hC.contDiffAt)
  simp only [norm_zero,zero_pow (by norm_num : (2 : ℕ)≠0),sub_zero] at hG
  rw [auto_ball_second_moment n hn hr] at hG
  have hEq : (∫ x : Space n, autoRadialGreen (2*n) (autoBallMeanOmega n) r ‖x‖*
      autoBallMeanLaplacian (fun y : Space n => ‖y‖^2) x)=
      (2*(2*n : ℝ))*(∫ x : Space n, autoRadialGreen (2*n) (autoBallMeanOmega n) r ‖x‖) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact ae_of_all volume fun x => by
      change autoRadialGreen (2*n) (autoBallMeanOmega n) r ‖x‖*autoBallMeanLaplacian (fun y : Space n => ‖y‖^2) x=
        (2*(2*n : ℝ))*autoRadialGreen (2*n) (autoBallMeanOmega n) r ‖x‖
      by_cases hx : x=0
      · subst x
        have hK : autoRadialGreen (2*n) (autoBallMeanOmega n) r ‖(0 : Space n)‖=0 :=
          auto_radialGreen_zero_outside (2*n) (autoBallMeanOmega n) r (by simp only [norm_zero,mem_Ioo]; intro h; exact (lt_irrefl 0) h.1)
        rw [hK,zero_mul,mul_zero]
      · rw [auto_ballMean_normSq_laplacian hx]
        ring
  rw [hEq] at hG
  have hd : 0 < (2*n : ℝ) := by exact_mod_cast (show 0 < 2*n by omega)
  apply (eq_div_iff (by positivity : (2*((2*n : ℝ)+2))≠0)).mpr
  apply mul_left_cancel₀ hd.ne'
  have hEq' : ((2*n : ℝ)/((2*n : ℝ)+2))*r^2=
      (2*n : ℝ)*r^2/((2*n : ℝ)+2) := by ring
  rw [hEq'] at hG
  have h := (eq_div_iff (by positivity : ((2*n : ℝ)+2)≠0)).mp hG.symm
  nlinarith only [h]

end Yau.LeafProofs.L05AutonomousAux
