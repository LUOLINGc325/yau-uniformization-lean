import Yau.LeafProofs.L05AutonomousJointSecondPairing
import Yau.LeafProofs.L05AutonomousSecondCoefficient

noncomputable section
open Filter Set MeasureTheory
open scoped Topology ContDiff
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05AutonomousAux
open Yau.Parabolic

theorem auto_joint_line_second_derivative {n : ℕ} {f : Point n → ℝ} (hf : ContDiff ℝ ∞ f)
    (x v : Point n) (s : ℝ) :
    deriv (deriv (fun t : ℝ => f (x+t • v))) s=
      fderiv ℝ (fderiv ℝ f) (x+s • v) v v := by
  have hfirst : deriv (fun t : ℝ => f (x+t • v))=(fun t => fderiv ℝ f (x+t • v) v) := by
    funext t
    exact (hf.differentiable (by simp) (x+t • v)).deriv_comp_add_smul
  have hD : DifferentiableAt ℝ (fderiv ℝ f) (x+s • v) :=
    (hf.fderiv_right (m := ∞) (by simp)).differentiable (by simp) _
  have hdv : DifferentiableAt ℝ (fun y => fderiv ℝ f y v) (x+s • v) :=
    hD.clm_apply (differentiableAt_const v)
  rw [hfirst,hdv.deriv_comp_add_smul,fderiv_clm_apply hD (differentiableAt_const v)]
  simp

/-- The second difference is the literal integral of the genuine spatial Hessian. -/
theorem auto_joint_second_identity {n : ℕ} {f : Point n → ℝ} (hf : ContDiff ℝ ∞ f)
    (x v : Point n) :
    f (x+v)+f (x-v)-2*f x=
      ∫ s in (-1 : ℝ)..1, (1-|s|)*fderiv ℝ (fderiv ℝ f) (x+s • v) v v := by
  have hg : ContDiff ℝ ∞ (fun t : ℝ => f (x+t • v)) :=
    hf.comp (contDiff_const.add (contDiff_id.smul contDiff_const))
  have hh := auto_triangular_second_identity hg
  simp_rw [auto_joint_line_second_derivative hf x v] at hh
  simpa only [one_smul,neg_smul,one_smul,zero_smul,add_zero,sub_eq_add_neg] using hh

/-- The actual spatial second difference is a positive average of the full joint Hessian
in the genuine spatial inclusion direction; the original source is smooth only here. -/
theorem auto_joint_second_as_probability {n : ℕ} {f : Point n → ℝ} (hf : ContDiff ℝ ∞ f)
    (p : Point n) (e : Space n) {h : ℝ} (hh : h≠0) :
    autoSecond f e h p=∫ s, fderiv ℝ (fderiv ℝ f) (p+(s*h) • (e,0)) (e,0) (e,0) ∂autoTentMeasure := by
  rw [autoTentMeasure_integral,autoSecond_point_translation]
  have hv : h • ((e,0) : Point n)=(h • e,0) := by simp
  rw [← hv,auto_joint_second_identity hf p (h • (e,0)),← intervalIntegral.integral_div]
  apply intervalIntegral.integral_congr
  intro s hs
  change ((1-|s|)*fderiv ℝ (fderiv ℝ f) (p+s • (h • (e,0))) (h • (e,0)) (h • (e,0)))/h^2=_
  simp only [smul_smul,map_smul,ContinuousLinearMap.smul_apply,smul_eq_mul]
  field_simp

theorem auto_joint_second_limit {n : ℕ} {f : Point n → ℝ} (hf : ContDiff ℝ ∞ f)
    (x : Point n) (e : Space n) : Tendsto (fun h => autoSecond f e h x) (𝓝[>] 0)
      (𝓝 (fderiv ℝ (fderiv ℝ f) x (e,0) (e,0))) := by
  let H : Point n → ℝ := fun z => fderiv ℝ (fderiv ℝ f) z (e,0) (e,0)
  have hH : Continuous H :=
    (((((hf.fderiv_right (m := ∞) (by simp)).fderiv_right (m := ∞) (by simp)).clm_apply
      contDiff_const).clm_apply contDiff_const).continuous)
  let : IsProbabilityMeasure autoTentMeasure := autoTentMeasure_isProbability
  apply Metric.tendsto_nhds.mpr
  intro eta heta
  obtain ⟨delta,hdelta,hclose⟩ := Metric.continuousAt_iff.mp hH.continuousAt (eta/2) (half_pos heta)
  have hevent : Ioo (0 : ℝ) (delta/(‖((e,0) : Point n)‖+1))∈𝓝[>] 0 :=
    mem_nhdsGT_iff_exists_Ioo_subset.mpr ⟨_,div_pos hdelta (by positivity),subset_rfl⟩
  filter_upwards [hevent] with h hh
  let path : ℝ → Point n := fun s => x+(s*h) • (e,0)
  have hc : Continuous (fun s => H (path s)) :=
    hH.comp (continuous_const.add ((continuous_id.mul continuous_const).smul continuous_const))
  have hInt := autoTentMeasure_continuous_integrable hc
  have hDiff : autoSecond f e h x-H x=∫ s, (H (path s)-H x) ∂autoTentMeasure := by
    rw [auto_joint_second_as_probability hf x e hh.1.ne',integral_sub hInt (integrable_const _),
      integral_const,probReal_univ,one_smul]
  have hBound := norm_integral_le_of_norm_le_const (μ := autoTentMeasure)
    (f := fun s => H (path s)-H x) (C := eta/2) (by
      filter_upwards [autoTentMeasure_interval_ae] with s hs
      have hsabs : |s| ≤ 1 := abs_le.mpr hs
      have hhdelta : h*(‖((e,0) : Point n)‖+1) < delta := (lt_div_iff₀ (by positivity)).mp hh.2
      have hd : dist (path s) x < delta := by
        rw [dist_eq_norm,show path s-x=(s*h) • ((e,0) : Point n) by dsimp only [path];abel,
          norm_smul,Real.norm_eq_abs,abs_mul,abs_of_pos hh.1]
        have hb := mul_le_mul_of_nonneg_right hsabs (mul_nonneg hh.1.le (norm_nonneg ((e,0) : Point n)))
        nlinarith only [hb,hhdelta,hh.1]
      simpa only [dist_eq_norm] using (hclose hd).le)
  rw [dist_eq_norm,hDiff]
  exact (by simpa only [probReal_univ,mul_one] using hBound : ‖∫ s, (H (path s)-H x) ∂autoTentMeasure‖ ≤ eta/2).trans_lt
    (half_lt_self heta)

/-- Smooth compact tests have a genuine global second-difference bound. Its constant may
depend on the test, and is used only as a dominated-convergence majorant. -/
theorem auto_joint_test_second_bound {n : ℕ} {phi : Point n → ℝ}
    (hphi : ContDiff ℝ ∞ phi) (hcphi : HasCompactSupport phi) (e : Space n) :
    ∃ C : ℝ, 0 ≤ C ∧ (∀ p, |fderiv ℝ (fderiv ℝ phi) p (e,0) (e,0)| ≤ C) ∧
      ∀ p h, h≠0 → |autoSecond phi e h p| ≤ C := by
  let D : Point n → ℝ := fun p => fderiv ℝ (fderiv ℝ phi) p (e,0) (e,0)
  have hD : Continuous D :=
    (((((hphi.fderiv_right (m := ∞) (by simp)).fderiv_right (m := ∞) (by simp)).clm_apply
      contDiff_const).clm_apply contDiff_const).continuous)
  have hcD : HasCompactSupport D :=
    ((hcphi.fderiv (𝕜 := ℝ)).fderiv (𝕜 := ℝ)).comp_left
      (g := fun L : Point n →L[ℝ] Point n →L[ℝ] ℝ => L (e,0) (e,0)) (by simp)
  obtain ⟨C,hC⟩ := hD.bounded_above_of_compact_support hcD
  let C' := max C 0
  have hBound (p : Point n) : |D p| ≤ C' := by
    rw [← Real.norm_eq_abs]
    exact (hC p).trans (le_max_left _ _)
  refine ⟨C',le_max_right _ _,hBound,?_⟩
  intro p h hh
  let : IsProbabilityMeasure autoTentMeasure := autoTentMeasure_isProbability
  rw [auto_joint_second_as_probability hphi p e hh,← Real.norm_eq_abs]
  have hI := norm_integral_le_of_norm_le_const (μ := autoTentMeasure)
    (f := fun s => D (p+(s*h) • (e,0))) (C := C')
    (ae_of_all _ fun s => by simpa only [Real.norm_eq_abs] using hBound _)
  simpa only [probReal_univ,mul_one] using hI

end Yau.LeafProofs.L05AutonomousAux
