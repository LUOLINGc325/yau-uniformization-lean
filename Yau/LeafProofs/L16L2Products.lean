import Yau.LeafProofs.L16SmoothEnergy

open MeasureTheory Filter
open scoped Topology ContDiff Convolution
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic Yau.ParabolicCandidates

theorem real_memLp_toLp_norm_sq {n : ℕ} {μ : Measure (Point n)} {f : Point n → ℝ}
    (hf : MemLp f 2 μ) : ‖hf.toLp f‖^2 = ∫ p, ‖f p‖^2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with p hp
  rw [hp]
  exact real_inner_self_eq_norm_sq (f p)

theorem tendsto_toLp_of_integral_sq_sub {n : ℕ} {μ : Measure (Point n)}
    {f : ℕ → Point n → ℝ} {g : Point n → ℝ}
    (hf : ∀ k, MemLp (f k) 2 μ) (hg : MemLp g 2 μ)
    (hLim : Tendsto (fun k => ∫ p, ‖f k p-g p‖^2 ∂μ) atTop (𝓝 0)) :
    Tendsto (fun k => (hf k).toLp (f k)) atTop (𝓝 (hg.toLp g)) := by
  have hEq (k : ℕ) : ‖(hf k).toLp (f k)-hg.toLp g‖^2 = ∫ p, ‖f k p-g p‖^2 ∂μ := by
    rw [← MemLp.toLp_sub]
    exact real_memLp_toLp_norm_sq ((hf k).sub hg)
  have hSq : Tendsto (fun k => ‖(hf k).toLp (f k)-hg.toLp g‖^2) atTop (𝓝 0) := by
    simpa only [hEq] using hLim
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hSqrt := (Real.continuous_sqrt.tendsto 0).comp hSq
  simpa only [Real.sqrt_sq_eq_abs,abs_norm,Real.sqrt_zero,Function.comp_def] using hSqrt

theorem tendsto_integral_weighted_mul_of_L2 {n : ℕ} {μ : Measure (Point n)}
    {f g : ℕ → Point n → ℝ} {u v η : Point n → ℝ}
    (hf : ∀ k, MemLp (f k) 2 μ) (hg : ∀ k, MemLp (g k) 2 μ)
    (hu : MemLp u 2 μ) (hv : MemLp v 2 μ) (hη : MemLp η (⊤ : ENNReal) μ)
    (hF : Tendsto (fun k => ∫ p, ‖f k p-u p‖^2 ∂μ) atTop (𝓝 0))
    (hG : Tendsto (fun k => ∫ p, ‖g k p-v p‖^2 ∂μ) atTop (𝓝 0)) :
    Tendsto (fun k => ∫ p, η p*f k p*g k p ∂μ) atTop (𝓝 (∫ p, η p*u p*v p ∂μ)) := by
  let M := (ContinuousLinearMap.mul ℝ ℝ).holderL μ (⊤ : ENNReal) 2 2 (hη.toLp η)
  let B := (ContinuousLinearMap.mul ℝ ℝ).lpPairing μ 2 2
  have hFLp := tendsto_toLp_of_integral_sq_sub hf hu hF
  have hGLp := tendsto_toLp_of_integral_sq_sub hg hv hG
  have hMLp := M.continuous.tendsto (hu.toLp u) |>.comp hFLp
  have hPair := B.continuous₂.tendsto (M (hu.toLp u),hv.toLp v) |>.comp
    (hMLp.prodMk_nhds hGLp)
  have hIdentify (a b : Point n → ℝ) (ha : MemLp a 2 μ) (hb : MemLp b 2 μ) :
      B (M (ha.toLp a)) (hb.toLp b) = ∫ p, η p*a p*b p ∂μ := by
    rw [ContinuousLinearMap.lpPairing_eq_integral]
    apply integral_congr_ae
    have hM := (ContinuousLinearMap.mul ℝ ℝ).coeFn_holder (hη.toLp η) (ha.toLp a) (r := 2)
    filter_upwards [hM,hη.coeFn_toLp,ha.coeFn_toLp,hb.coeFn_toLp] with p hp hηp hap hbp
    simpa only [M,ContinuousLinearMap.holderL_apply_apply,ContinuousLinearMap.mul_apply',hηp,hap,hbp] using
      congrArg (fun t : ℝ => t*b p) hp
  simpa only [Function.comp_def,Function.uncurry_def,hIdentify] using hPair

theorem integrable_weighted_mul_of_memLp {n : ℕ} {μ : Measure (Point n)}
    {η u v : Point n → ℝ} (hη : MemLp η (⊤ : ENNReal) μ)
    (hu : MemLp u 2 μ) (hv : MemLp v 2 μ) : Integrable (fun p => η p*u p*v p) μ := by
  have h : MemLp (fun p => η p*u p) 2 μ := hη.mul hu
  exact h.integrable_mul hv

end Yau.LeafProofs.L16Aux
