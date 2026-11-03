import Yau.LeafProofs.L05AutonomousSecondTensor
import Yau.LeafProofs.L05AutonomousSecondWeight
import Yau.LeafProofs.L05AutonomousTranslateMass
import Yau.LeafProofs.L05AutonomousLocalEnergy

noncomputable section
open Filter Set MeasureTheory Matrix
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
namespace Yau.LeafProofs.L05AutonomousAux
open Yau.Parabolic Yau.LeafProofs.L05Aux

/-- Jensen and actual Haar translations transfer the real Hessian energy to every nonzero second difference. -/
theorem auto_spatial_second_energy (n : ℕ) : ∃ C : ℝ, 0< C ∧
    ∀ f : Space n → ℝ, ContDiff ℝ ∞ f → ∀ (r R h : ℝ), 0< r → r+|h|< R → h≠0 →
    ∀ e : Space n, ‖e‖≤ 1 →
      IntegrableOn (fun x => (autoSpatialSecond f e h x)^2) (Metric.ball (0 : Space n) r) ∧
      (∫ x in Metric.ball (0 : Space n) r, (autoSpatialSecond f e h x)^2)≤
        C*(∫ x in Metric.ball (0 : Space n) R, ‖secondFDerivMatrix f x‖^2) := by
  obtain ⟨A,hA,hDirection⟩ := auto_second_direction_budget n
  refine ⟨A^2,sq_pos_of_pos hA,?_⟩
  intro f hf r R h hr hbuffer hh e he
  let : IsProbabilityMeasure autoTentMeasure := autoTentMeasure_isProbability
  let H2 : Space n → ℝ := fun x => ‖secondFDerivMatrix f x‖^2
  let G : Space n → ℝ := (Metric.ball (0 : Space n) R).indicator H2
  let path : ℝ → Space n := fun s => (s*h) • e
  have hH2 : Continuous H2 := auto_hessian_sq_continuous hf
  have hGm : Measurable G := hH2.measurable.indicator measurableSet_ball
  have hH2int : IntegrableOn H2 (Metric.ball (0 : Space n) R) :=
    (hH2.continuousOn.integrableOn_compact (isCompact_closedBall (0 : Space n) R)).mono_set Metric.ball_subset_closedBall
  have hGi : Integrable G := (integrable_indicator_iff measurableSet_ball).mpr hH2int
  have hG0 (x : Space n) : 0≤ G x := by
    by_cases hx : x∈Metric.ball (0 : Space n) R
    · simpa only [G,indicator_of_mem hx,H2] using sq_nonneg ‖secondFDerivMatrix f x‖
    · simp only [G,indicator_of_notMem hx,le_refl]
  have hpath : Continuous path := (continuous_id.mul continuous_const).smul continuous_const
  have hMass := auto_translation_average_local_bound autoTentMeasure hpath.measurable hGm hGi hG0
    (Metric.ball (0 : Space n) r)
  have hSecondCont : Continuous (fun x => (autoSpatialSecond f e h x)^2) := by
    apply Continuous.pow
    exact (((hf.continuous.comp (continuous_id.add_const (h • e))).add
      (hf.continuous.comp (continuous_id.sub continuous_const))).sub (continuous_const.mul hf.continuous)).div_const _
  have hSecondInt : IntegrableOn (fun x => (autoSpatialSecond f e h x)^2) (Metric.ball (0 : Space n) r) :=
    (hSecondCont.continuousOn.integrableOn_compact (isCompact_closedBall (0 : Space n) r)).mono_set Metric.ball_subset_closedBall
  have hPoint (x : Space n) (hx : x∈Metric.ball (0 : Space n) r) :
      (autoSpatialSecond f e h x)^2≤ A^2*(∫ s, G (x+path s) ∂autoTentMeasure) := by
    have hIn (s : ℝ) (hs : s∈Icc (-1 : ℝ) 1) : x+path s∈Metric.ball (0 : Space n) R := by
      have hxnorm : ‖x‖< r := by simpa only [Metric.mem_ball,dist_zero_right] using hx
      have hsabs : |s|≤ 1 := abs_le.mpr hs
      have hv : ‖path s‖≤ |h| := by
        change ‖(s*h) • e‖≤ |h|
        rw [norm_smul,Real.norm_eq_abs,abs_mul]
        calc
          _ ≤ 1*|h| *1 := by gcongr
          _ = _ := by ring
      have hnorm := (norm_add_le x (path s)).trans_lt (by linarith only [hxnorm,hv,hbuffer] : ‖x‖+‖path s‖< R)
      simpa only [Metric.mem_ball,dist_zero_right] using hnorm
    have hDcont : Continuous (fun s : ℝ => fderiv ℝ (fderiv ℝ f) (x+path s) e e) :=
      (((((hf.fderiv_right (m := ∞) (by simp)).fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).clm_apply
        contDiff_const).continuous).comp (continuous_const.add hpath)
    have hHi : Integrable (fun s => H2 (x+path s)) autoTentMeasure :=
      autoTentMeasure_continuous_integrable (hH2.comp (continuous_const.add hpath))
    have hEq : (fun s => H2 (x+path s)) =ᵐ[autoTentMeasure] (fun s => G (x+path s)) := by
      filter_upwards [autoTentMeasure_interval_ae] with s hs
      exact (indicator_of_mem (hIn s hs) H2).symm
    have hGiShift : Integrable (fun s => G (x+path s)) autoTentMeasure := hHi.congr hEq
    have hSq (z : Space n) : (fderiv ℝ (fderiv ℝ f) z e e)^2≤ A^2*H2 z := by
      have hd := hDirection f z e he
      have hh := (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hA.le (norm_nonneg (secondFDerivMatrix f z)))).mpr hd
      simpa only [sq_abs,mul_pow,H2] using hh
    have hInt := integral_mono_ae (autoTentMeasure_continuous_integrable (hDcont.pow 2))
      (hGiShift.const_mul (A^2)) (by
        filter_upwards [autoTentMeasure_interval_ae] with s hs
        rw [show G (x+path s)=H2 (x+path s) from indicator_of_mem (hIn s hs) H2]
        exact hSq _)
    rw [integral_const_mul] at hInt
    exact (auto_spatial_second_square_probability hf x e hh).trans hInt
  refine ⟨hSecondInt,?_⟩
  have hInt := integral_mono_ae hSecondInt (hMass.1.const_mul (A^2)) (by
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    exact hPoint x hx)
  rw [integral_const_mul] at hInt
  have hGtotal : (∫ x, G x)=∫ x in Metric.ball (0 : Space n) R, H2 x := integral_indicator measurableSet_ball
  exact hInt.trans ((mul_le_mul_of_nonneg_left hMass.2 (sq_nonneg A)).trans_eq (by rw [hGtotal]))

theorem autoSpatialSecond_point_eq {n : ℕ} (u : Point n → ℝ) (e : Space n) (h : ℝ) (p : Point n) :
    autoSpatialSecond (fun x => u (x,p.2)) e h p.1=autoSecond u e h p := rfl

end Yau.LeafProofs.L05AutonomousAux
