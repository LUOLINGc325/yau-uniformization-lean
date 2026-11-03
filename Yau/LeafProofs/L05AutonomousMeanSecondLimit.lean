import Yau.LeafProofs.L05AutonomousBallMeanMass

noncomputable section
open Filter Set MeasureTheory Metric
open scoped Topology ContDiff
namespace Yau.LeafProofs.L05AutonomousAux
open Yau.Parabolic

/-- The exact positive Green identity and its mass identify the actual small-ball second-order coefficient. -/
theorem auto_ball_mean_second_limit {n : ℕ} (hn : 0< n) {f : Space n → ℝ} (hf : ContDiff ℝ ∞ f) :
    Tendsto (fun r : ℝ => ((∫ x in ball (0 : Space n) r, f x)/
      (volume : Measure (Space n)).real (ball 0 r)-f 0)/r^2) (𝓝[>] 0)
      (𝓝 (autoBallMeanLaplacian f 0/(2*((2*n : ℝ)+2)))) := by
  let D : ℝ := 2*((2*n : ℝ)+2)
  have hD : 0< D := by dsimp only [D];positivity
  have hLap : Continuous (autoBallMeanLaplacian f) := continuousOn_univ.mp
    (auto_ballMean_laplacian_continuousOn (fun x _ => hf.contDiffAt.of_le (by simp)))
  apply Metric.tendsto_nhds.mpr
  intro eps heps
  let E : ℝ := eps*D/2
  have hE : 0< E := by dsimp only [E];positivity
  obtain ⟨delta,hdelta,hclose⟩ := Metric.continuousAt_iff.mp hLap.continuousAt E hE
  have hEvent : Ioo (0 : ℝ) delta∈𝓝[>] 0 :=
    mem_nhdsGT_iff_exists_Ioo_subset.mpr ⟨delta,hdelta,subset_rfl⟩
  filter_upwards [hEvent] with r hr
  let K : Space n → ℝ := fun x => autoRadialGreen (2*n) (autoBallMeanOmega n) r ‖x‖
  have hK : Integrable K := auto_ballMean_kernel_integrable hn (autoBallMeanOmega n) hr.1
  have hKL : Integrable (fun x => K x*autoBallMeanLaplacian f x) :=
    auto_ballMean_kernel_source_integrable hn (autoBallMeanOmega n) hr.1 (fun x _ => hf.contDiffAt.of_le (by simp))
  have hKC : Integrable (fun x => K x*autoBallMeanLaplacian f 0) := hK.mul_const _
  have hFun : (fun x => K x*(autoBallMeanLaplacian f x-autoBallMeanLaplacian f 0))=
      (fun x => K x*autoBallMeanLaplacian f x-K x*autoBallMeanLaplacian f 0) := by funext x;ring
  have hDiffInt : Integrable (fun x => K x*(autoBallMeanLaplacian f x-autoBallMeanLaplacian f 0)) := by
    rw [hFun]
    exact hKL.sub hKC
  have hKmass : (∫ x, K x)=r^2/D := auto_ballMean_kernel_mass hn hr.1
  have hDiff : (∫ x, K x*(autoBallMeanLaplacian f x-autoBallMeanLaplacian f 0))=
      (∫ x, K x*autoBallMeanLaplacian f x)-(∫ x, K x)*autoBallMeanLaplacian f 0 := by
    rw [hFun,integral_sub hKL hKC,integral_mul_const]
  have hGreen : (∫ x in ball (0 : Space n) r, f x)/(volume : Measure (Space n)).real (ball 0 r)-f 0=
      ∫ x, K x*autoBallMeanLaplacian f x :=
    auto_ball_mean_green_zero hn hr.1 (fun x _ => hf.contDiffAt.of_le (by simp))
  have hError : ((∫ x in ball (0 : Space n) r, f x)/(volume : Measure (Space n)).real (ball 0 r)-f 0)/r^2-
      autoBallMeanLaplacian f 0/D=(∫ x, K x*(autoBallMeanLaplacian f x-autoBallMeanLaplacian f 0))/r^2 := by
    rw [hGreen,hDiff,hKmass]
    field_simp [hD.ne',hr.1.ne']
  have hPoint (x : Space n) : ‖K x*(autoBallMeanLaplacian f x-autoBallMeanLaplacian f 0)‖≤ E*K x := by
    have hK0 : 0≤ K x := auto_radialGreen_nonneg (r := r) (by omega : 0< 2*n) (auto_ballMean_omega_pos n) ‖x‖
    by_cases hx : x∈ball (0 : Space n) r
    · have hxdelta : dist x 0< delta := (show dist x 0< r from hx).trans hr.2
      have hh : ‖autoBallMeanLaplacian f x-autoBallMeanLaplacian f 0‖≤ E :=
        (by simpa only [dist_eq_norm] using (hclose hxdelta).le)
      rw [norm_mul,Real.norm_eq_abs,abs_of_nonneg hK0]
      exact (mul_le_mul_of_nonneg_left hh hK0).trans_eq (mul_comm _ _)
    · have hz : K x=0 := auto_radialGreen_zero_outside (2*n) (autoBallMeanOmega n) r (by
        intro hs
        exact hx (by simpa only [mem_ball,dist_zero_right] using hs.2))
      simp only [hz,zero_mul,norm_zero,mul_zero,le_refl]
  have hNorm := norm_integral_le_of_norm_le (hK.const_mul E) (ae_of_all volume hPoint)
  rw [integral_const_mul,hKmass] at hNorm
  have hDiv : ‖(∫ x, K x*(autoBallMeanLaplacian f x-autoBallMeanLaplacian f 0))/r^2‖≤ eps/2 := by
    rw [norm_div,Real.norm_of_nonneg (sq_nonneg r)]
    exact (div_le_div_of_nonneg_right hNorm (sq_nonneg r)).trans_eq (by
      dsimp only [E]
      field_simp [hD.ne',hr.1.ne'])
  rw [dist_eq_norm,hError]
  exact hDiv.trans_lt (half_lt_self heps)

end Yau.LeafProofs.L05AutonomousAux
