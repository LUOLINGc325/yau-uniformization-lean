import Yau.LeafProofs.L05AutonomousMollifiedHessianBounds

noncomputable section
open Filter Set MeasureTheory Matrix
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius BoundedContinuousFunction
namespace Yau.LeafProofs.L05AutonomousAux
open Yau.Parabolic Yau.LeafProofs.L05Aux

/-- The genuine smooth Hessian budget survives the mollifier limit for every actual nonzero step. -/
theorem auto_uniform_second_differences :
    ∀ n : ℕ, 0 < n → ∀ ell L : ℝ, 0 < ell → ell ≤ L →
    ∃ C : ℝ, 0 < C ∧
      ∀ F : Sym n → ℝ, Continuous F → globalElliptic F ell L → ConcaveOn ℝ univ F → F 0=0 →
      ∀ u : Point n → ℝ, ContinuousOn u (unitClosed n) → (∀ p∈unitClosed n, |u p|≤ 1) →
        viscositySolution (unitOpen n) (fun H _ => F H) (fun _ => 0) u →
        ∀ e : Space n, ‖e‖=1 → ∀ h : ℝ, h≠0 → |h| < 1/512 →
        ∀ p∈autoClosed (0 : Space n) (11/16) 0, |autoSecond u e h p| ≤ C := by
  intro n hn ell L hell hL
  obtain ⟨B,hB,hForU⟩ := auto_uniform_mollified_hessian n hn ell L hell hL
  obtain ⟨D,hD,hDirection⟩ := auto_second_direction_budget n
  refine ⟨D*B,mul_pos hD hB,?_⟩
  intro F hF hE hConc h0 u hu hb hsol e he h hh hsmall p hp
  obtain ⟨w,hwu,hw,hcw,hw1,hHessian⟩ := hForU F hF hE hConc h0 u hu hb hsol
  let eps := autoDyadicStep (1/512 : ℝ)
  have heps (j : ℕ) : 0 < eps j := auto_dyadicStep_pos (by norm_num) j
  have hepsSmall (j : ℕ) : eps j < 1/256 :=
    (auto_dyadicStep_le (by norm_num : (0 : ℝ) ≤ 1/512) j).trans_lt (by norm_num)
  have hAbs (j : ℕ) : |autoSecond (autoSpatialMollify (eps j) (heps j) w) e h p| ≤ D*B := by
    let f : Space n → ℝ := fun x => autoSpatialMollify (eps j) (heps j) w (x,p.2)
    have hf := autoSpatialMollify_spatial_contDiff (eps j) (heps j) w hw p.2
    have hPath (s : ℝ) (hs : s∈Icc (-1 : ℝ) 1) :
        (p.1+(s*h) • e,p.2)∈autoClosed (0 : Space n) (45/64) 0 := by
      have hx : ‖p.1‖ ≤ 11/16 := by simpa only [Metric.mem_closedBall,dist_zero_right] using hp.1
      have hsabs : |s| ≤ 1 := abs_le.mpr hs
      have hv : ‖(s*h) • e‖ ≤ |h| := by
        rw [norm_smul,Real.norm_eq_abs,abs_mul,he,mul_one]
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hsabs (abs_nonneg h)
      have hxNorm : ‖p.1+(s*h) • e‖ ≤ 45/64 := by
        have ht := norm_add_le p.1 ((s*h) • e)
        linarith only [ht,hx,hv,hsmall]
      have ht : -(11/16 : ℝ)^2 ≤ p.2 ∧ p.2 ≤ 0 := by simpa only [zero_sub,mem_Icc] using hp.2
      exact ⟨by simpa only [Metric.mem_closedBall,dist_zero_right] using hxNorm,
        by change (0 : ℝ)-(45/64)^2 ≤ p.2 ∧ p.2 ≤ 0;exact ⟨by linarith only [ht.1],ht.2⟩⟩
    let : IsProbabilityMeasure autoTentMeasure := autoTentMeasure_isProbability
    have hBound := norm_integral_le_of_norm_le_const (μ := autoTentMeasure)
      (f := fun s => fderiv ℝ (fderiv ℝ f) (p.1+(s*h) • e) e e) (C := D*B) (by
        filter_upwards [autoTentMeasure_interval_ae] with s hs
        have hDir := hDirection f (p.1+(s*h) • e) e he.le
        have hH := hHessian (eps j) (heps j) (hepsSmall j) _ (hPath s hs)
        have hDirNorm : ‖fderiv ℝ (fderiv ℝ f) (p.1+(s*h) • e) e e‖ ≤
            D*‖secondFDerivMatrix f (p.1+(s*h) • e)‖ := by
          simpa only [Real.norm_eq_abs] using hDir
        exact hDirNorm.trans (mul_le_mul_of_nonneg_left hH hD.le))
    have hEq : autoSecond (autoSpatialMollify (eps j) (heps j) w) e h p=
        ∫ s, fderiv ℝ (fderiv ℝ f) (p.1+(s*h) • e) e e ∂autoTentMeasure :=
      auto_spatial_second_as_probability hf p.1 e hh
    rw [hEq]
    simpa only [Real.norm_eq_abs,probReal_univ,mul_one] using hBound
  have hUniform := autoSpatialMollify_uniform w hw eps heps (auto_dyadicStep_tendsto _)
  have hlim : Tendsto (fun j => autoSecond (autoSpatialMollify (eps j) (heps j) w) e h p) atTop
      (𝓝 (autoSecond w e h p)) := by
    have hplus := hUniform.tendsto_at (p.1+h • e,p.2)
    have hminus := hUniform.tendsto_at (p.1-h • e,p.2)
    have hcenter := hUniform.tendsto_at p
    exact ((hplus.add hminus).sub (hcenter.const_mul 2)).div_const (h^2)
  have hFinal : |autoSecond w e h p| ≤ D*B :=
    le_of_tendsto (continuous_abs.tendsto _ |>.comp hlim) (Eventually.of_forall hAbs)
  obtain ⟨hp0,hpPlus,hpMinus⟩ := auto_second_closed_unit (by norm_num : (0 : ℝ) < 11/16)
    (by linarith only [hsmall] : (11/16 : ℝ)+|h| < 1) he.le hp
  rwa [auto_second_congr hwu e h p hp0 hpPlus hpMinus] at hFinal

end Yau.LeafProofs.L05AutonomousAux
