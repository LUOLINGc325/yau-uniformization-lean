import Yau.LeafProofs.L05AutonomousCutoffAverage

noncomputable section
open Filter Set MeasureTheory Matrix
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
namespace Yau.LeafProofs.L05AutonomousAux
open Yau.Parabolic Yau.LeafProofs.L05Aux

/-- A fixed cutoff and fixed buffer give a uniform commutator integral budget before every source. -/
theorem auto_ellipsoid_cutoff_integral_bound {n : ℕ} {φ : Space n → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hcφ : HasCompactSupport φ) {R b : ℝ} (hb : 0≤ b)
    (hsupp : tsupport φ⊆Metric.closedBall (0 : Space n) R) :
    ∃ C : ℝ, 0< C ∧ ∀ (B : Space n ≃L[ℝ] Space n) {r L M : ℝ},
      0< r → 0≤ L → 0≤ M → ‖B.toContinuousLinearMap‖≤ b →
      ‖B.toContinuousLinearMap‖^2≤ r^2*L →
      ∀ f : Space n → ℝ, Continuous f → HasCompactSupport f → (∀ x, |f x|≤ M) →
      |∫ x, φ x*((autoSpatialAverage (autoLinearBallProbability B) f x-f x)/r^2)|≤ C*M*L := by
  obtain ⟨C₀,hC₀,hpoint⟩ := auto_ellipsoid_cutoff_scaled hφ hcφ
  let region := Metric.closedBall (0 : Space n) (R+b)
  let volumeRegion := (volume : Measure (Space n)).real region
  let C := C₀*volumeRegion+1
  have hVol : 0≤ volumeRegion := ENNReal.toReal_nonneg
  have hC : 0< C := by dsimp only [C];positivity
  refine ⟨C,hC,?_⟩
  intro B r L M hr hL hM hB hBsq f hf hcf hbound
  have hpair := (auto_ellipsoid_average_commutator B hφ.continuous hf hcφ hcf).2.2
  have hpairDiv : (∫ x, φ x*((autoSpatialAverage (autoLinearBallProbability B) f x-f x)/r^2))=
      ∫ x, f x*((autoSpatialAverage (autoLinearBallProbability B) φ x-φ x)/r^2) := by
    simp_rw [← mul_div_assoc,integral_div]
    rw [hpair]
  rw [hpairDiv]
  have hzero (x : Space n) (hx : x∉region) :
      f x*((autoSpatialAverage (autoLinearBallProbability B) φ x-φ x)/r^2)=0 := by
    rw [auto_ellipsoid_cutoff_vanish hsupp hb B hB hx]
    simp only [zero_div,mul_zero]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
  let : IsFiniteMeasure ((volume : Measure (Space n)).restrict region) :=
    isFiniteMeasure_restrict.mpr (isCompact_closedBall (0 : Space n) (R+b)).measure_lt_top.ne
  have hint := norm_integral_le_of_norm_le_const (μ := (volume : Measure (Space n)).restrict region)
    (ae_of_all _ fun x => show ‖f x*((autoSpatialAverage (autoLinearBallProbability B) φ x-φ x)/r^2)‖≤ M*(C₀*L) from by
      rw [norm_mul,Real.norm_eq_abs,Real.norm_eq_abs]
      exact mul_le_mul (hbound x) (hpoint B hr hL hBsq x) (abs_nonneg _) hM)
  rw [measureReal_restrict_apply_univ,Real.norm_eq_abs] at hint
  exact hint.trans (by dsimp only [C,volumeRegion] at *;nlinarith only [mul_nonneg hM hL])

end Yau.LeafProofs.L05AutonomousAux
