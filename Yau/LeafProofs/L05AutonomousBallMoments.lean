import Yau.LeafProofs.L05AutonomousHessianEnergy
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Group.Integral

noncomputable section
open Filter Set MeasureTheory Matrix
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
namespace Yau.LeafProofs.L05AutonomousAux
open Yau.Parabolic Yau.LeafProofs.L05Aux

/-- The actual polar decomposition gives every nonnegative integral power moment. -/
theorem auto_ball_norm_power (n : ℕ) (hn : 0<n) (k : ℕ) {r : ℝ} (hr : 0<r) :
    (∫ x in Metric.ball (0 : Space n) r, ‖x‖^k)=
      (2*n : ℝ)*((volume : Measure (Space n)).real (Metric.ball 0 1))*
        (r^(2*n+k)/(2*n+k : ℕ)) := by
  have hdim : 0<Module.finrank ℝ (Space n) := by rw [complexVector_finrank_real]; omega
  let : Nontrivial (Space n) := Module.finrank_pos_iff.mp hdim
  have hd : 0<2*n := by omega
  have heq : (Metric.ball (0 : Space n) r).indicator (fun x => ‖x‖^k)=
      (fun x => (Iio r).indicator (fun s : ℝ => s^k) ‖x‖) := by
    funext x
    by_cases hx : ‖x‖<r
    · simp [Set.indicator,Metric.mem_ball,dist_zero_right,hx]
    · simp [Set.indicator,Metric.mem_ball,dist_zero_right,hx]
  rw [← integral_indicator measurableSet_ball,heq,integral_fun_norm_addHaar (volume : Measure (Space n)),
    complexVector_finrank_real]
  simp only [nsmul_eq_mul,smul_eq_mul]
  have hrad : (fun s : ℝ => s^(2*n-1)*(Iio r).indicator (fun q : ℝ => q^k) s)=
      (Iio r).indicator (fun s : ℝ => s^(2*n-1+k)) := by
    funext s
    by_cases hs : s<r
    · simp [Set.indicator,hs,pow_add]
    · simp [Set.indicator,hs]
  rw [hrad,setIntegral_indicator measurableSet_Iio,Ioi_inter_Iio]
  rw [← integral_Ioc_eq_integral_Ioo,← intervalIntegral.integral_of_le hr.le,_root_.integral_pow]
  have hexp : 2*n-1+k+1=2*n+k := by omega
  rw [hexp,zero_pow (by omega : 2*n+k≠0),sub_zero]
  have hcast : (↑(2*n-1+k) : ℝ)+1=↑(2*n+k) := by exact_mod_cast hexp
  rw [hcast]
  push_cast
  ring

/-- All radial power integrals used in the Green calculation are genuine Bochner integrals. -/
theorem auto_ball_norm_power_integrable (n : ℕ) (hn : 0<n) (k : ℕ) {r : ℝ} (_hr : 0<r) :
    IntegrableOn (fun x : Space n => ‖x‖^k) (Metric.ball 0 r) := by
  have hdim : 0<Module.finrank ℝ (Space n) := by rw [complexVector_finrank_real]; omega
  let : Nontrivial (Space n) := Module.finrank_pos_iff.mp hdim
  apply (integrableOn_fun_norm_addHaar (volume : Measure (Space n))).mpr
  rw [complexVector_finrank_real]
  have hh : IntegrableOn (fun s : ℝ => s^(2*n-1+k)) (Ioo 0 r) :=
    (intervalIntegral.intervalIntegrable_pow (a := 0) (b := r) (2*n-1+k)).1.mono_set Ioo_subset_Ioc_self
  change IntegrableOn (fun s : ℝ => s^(2*n-1)*s^k) (Ioo 0 r)
  simpa only [← pow_add] using hh

theorem auto_ball_volume_pos (n : ℕ) {r : ℝ} (hr : 0<r) :
    0<(volume : Measure (Space n)).real (Metric.ball 0 r) :=
  ENNReal.toReal_pos (ne_of_gt (Metric.measure_ball_pos volume 0 hr)) measure_ball_lt_top.ne

theorem auto_ball_volume_scale (n : ℕ) {r : ℝ} (hr : 0<r) :
    (volume : Measure (Space n)).real (Metric.ball 0 r)=
      r^(2*n)*(volume : Measure (Space n)).real (Metric.ball 0 1) := by
  simp only [measureReal_def]
  rw [(volume : Measure (Space n)).addHaar_ball_of_pos (0 : Space n) hr,
    ENNReal.toReal_mul,ENNReal.toReal_ofReal (pow_nonneg hr.le _),complexVector_finrank_real]

/-- Exact second radial moment, valid also in real dimension two (n=1). -/
theorem auto_ball_second_moment (n : ℕ) (hn : 0<n) {r : ℝ} (hr : 0<r) :
    (∫ x in Metric.ball (0 : Space n) r, ‖x‖^2)/
      ((volume : Measure (Space n)).real (Metric.ball 0 r))=
        ((2*n : ℝ)/((2*n : ℝ)+2))*r^2 := by
  rw [auto_ball_norm_power n hn 2 hr,auto_ball_volume_scale n hr,pow_add]
  have hv : (volume : Measure (Space n)).real (Metric.ball 0 1)≠0 :=
    (auto_ball_volume_pos n zero_lt_one).ne'
  have hrp : r^(2*n)≠0 := pow_ne_zero _ hr.ne'
  have hd : (2*n : ℝ)+2≠0 := by positivity
  push_cast
  field_simp

/-- The actual compactly supported probability law used by the native spatial averages. -/
def autoBallProbability (n : ℕ) (r : ℝ) : Measure (Space n) :=
  ((volume : Measure (Space n)) (Metric.ball 0 r))⁻¹ •
    (volume : Measure (Space n)).restrict (Metric.ball 0 r)

theorem autoBallProbability_isProbability (n : ℕ) {r : ℝ} (hr : 0<r) :
    IsProbabilityMeasure (autoBallProbability n r) := by
  constructor
  simp only [autoBallProbability,Measure.smul_apply,Measure.restrict_apply MeasurableSet.univ,
    univ_inter,smul_eq_mul]
  exact ENNReal.inv_mul_cancel (ne_of_gt (Metric.measure_ball_pos volume 0 hr)) measure_ball_lt_top.ne

theorem autoBallProbability_integral (n : ℕ) (r : ℝ) (f : Space n → ℝ) :
    (∫ x, f x ∂autoBallProbability n r)=
      (∫ x in Metric.ball (0 : Space n) r, f x)/
        ((volume : Measure (Space n)).real (Metric.ball 0 r)) := by
  rw [autoBallProbability,integral_smul_measure]
  simp only [ENNReal.toReal_inv,smul_eq_mul,measureReal_def,div_eq_inv_mul]

theorem autoBallProbability_closedBall_ae (n : ℕ) (r : ℝ) :
    ∀ᵐ x ∂autoBallProbability n r, x∈Metric.closedBall (0 : Space n) r := by
  exact Measure.ae_smul_measure
    ((ae_restrict_mem measurableSet_ball).mono fun x hx => Metric.ball_subset_closedBall hx) _

theorem auto_ball_integral_neg (n : ℕ) (r : ℝ) (f : Space n → ℝ) :
    (∫ x in Metric.ball (0 : Space n) r, f (-x))=∫ x in Metric.ball (0 : Space n) r, f x := by
  calc
    _ = ∫ x, ((Metric.ball (0 : Space n) r).indicator f) (-x) := by
      rw [← integral_indicator measurableSet_ball]
      apply integral_congr_ae
      exact ae_of_all volume fun x => by simp [Set.indicator,Metric.mem_ball,dist_zero_right,norm_neg]
    _ = ∫ x, (Metric.ball (0 : Space n) r).indicator f x := integral_neg_eq_self _ volume
    _ = _ := integral_indicator measurableSet_ball

theorem autoBallProbability_integral_neg (n : ℕ) (r : ℝ) (f : Space n → ℝ) :
    (∫ x, f (-x) ∂autoBallProbability n r)=∫ x, f x ∂autoBallProbability n r := by
  rw [autoBallProbability_integral,autoBallProbability_integral,auto_ball_integral_neg]

theorem autoBallProbability_linear_zero (n : ℕ) (r : ℝ) (L : Space n →L[ℝ] ℝ) :
    (∫ x, L x ∂autoBallProbability n r)=0 := by
  have hh := autoBallProbability_integral_neg n r (fun x => L x)
  have heq : (fun x : Space n => L (-x))=(fun x => -(L x)) := by funext x; exact L.map_neg x
  rw [heq,integral_neg] at hh
  linarith only [hh]

end Yau.LeafProofs.L05AutonomousAux
