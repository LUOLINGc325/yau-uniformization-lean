import Yau.LeafProofs.L19NormalContraction
import Yau.LeafProofs.L19SmoothDensity
import Yau.LeafProofs.L19HeatGaussianTailDoubleBall

/-! Uniformly bounded genuine smooth compact approximations of ball indicators. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace
namespace Yau.LeafProofs.L19Aux
open L12Aux L18Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

theorem kernelBall_regularAbs_lipschitz {ε : ℝ} (hε : 0 < ε) :
    LipschitzWith 1 (regularAbs ε) := by
  apply lipschitzWith_of_nnnorm_deriv_le ((regularAbs_contDiff hε).differentiable (by simp))
  intro r
  have hr : |deriv (regularAbs ε) r| ≤ 1 := by
    rw [(regularAbs_hasDerivAt hε r).deriv]
    exact regularAbs_ratio_abs_le hε r
  exact_mod_cast hr

/-- A smooth clip has a uniform absolute bound even outside the interval.
It is applied only to genuine smooth compact scalars below. -/
theorem kernelBall_smoothNormalClip_abs_le_one {ε : ℝ} (hε : 0 < ε) (r : ℝ) :
    |smoothNormalClip 1 ε r| ≤ 1 := by
  have h₁ := (kernelBall_regularAbs_lipschitz hε).dist_le_mul r (r - 1)
  have h₂ := (kernelBall_regularAbs_lipschitz hε).dist_le_mul 1 0
  have hzero : regularAbs ε 0 = ε := by simp [regularAbs, Real.sqrt_sq hε.le]
  simp only [Real.dist_eq, NNReal.coe_one, one_mul, sub_sub_cancel, abs_one] at h₁
  simp only [Real.dist_eq, NNReal.coe_one, one_mul, sub_zero, abs_one, hzero] at h₂
  have hsum := (abs_add_le (regularAbs ε r - regularAbs ε (r - 1))
    (regularAbs ε 1 - ε)).trans (add_le_add h₁ h₂)
  rw [smoothNormalClip, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  apply (div_le_one (by norm_num : (0 : ℝ) < 2)).mpr
  convert hsum using 1 <;> congr 1 <;> ring

/-- The independently constructed smooth core is dense with a common absolute
bound for every ball indicator. No regularity of the indicator is assumed. -/
theorem kernelBall_exists_bounded_core_approx (g : SmoothMetric M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (x : M.Carrier) (r : ℝ) (hr : 0 < r) :
    ∃ k : ℕ → ScalarEnergyDomain g μ hμ,
      (∀ j z, |k j z| ≤ 1) ∧
      Tendsto (fun j => scalarEnergyDomainL2 g μ hμ (k j)) atTop
        (𝓝 (scalarBallL2 g μ hμ x r hr)) := by
  classical
  let f := scalarBallL2 g μ hμ x r hr
  obtain ⟨q,hqmem,hq⟩ := mem_closure_iff_seq_limit.mp
    (scalarEnergyDomainL2_denseRange g μ hμ f)
  choose a ha using hqmem
  have haLim : Tendsto (fun j => scalarEnergyDomainL2 g μ hμ (a j)) atTop (𝓝 f) := by
    simpa only [ha] using hq
  let ε : ℕ → ℝ := fun j => 1 / ((j : ℝ) + 1)
  have hεpos (j : ℕ) : 0 < ε j := by dsimp [ε]; positivity
  have hεlim : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let k : ℕ → ScalarEnergyDomain g μ hμ :=
    fun j => smoothNormalClipDomain g μ hμ 1 (ε j) (hεpos j) (a j)
  have hfclip : normalClipL2 μ 1 (by norm_num) f = f := by
    apply Lp.ext
    filter_upwards [normalClipL2_coe μ 1 (by norm_num) f,
      scalarBallL2_coe g μ hμ x r hr] with z hz hf
    rw [hz, hf]
    by_cases h : z ∈ distBall g.form x r <;> simp [Set.indicator, h, normalClip]
  refine ⟨k, fun j z => kernelBall_smoothNormalClip_abs_le_one (hεpos j) _, ?_⟩
  have ht := smoothNormalClipL2_tendsto_moving μ 1 (by norm_num) _ f
    haLim ε hεpos hεlim
  simpa only [k, smoothNormalClipDomain_L2, hfclip] using ht

end Yau.LeafProofs.L19Aux
