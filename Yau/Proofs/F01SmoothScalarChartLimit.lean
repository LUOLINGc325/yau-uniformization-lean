import Yau.Proofs.F01AtlasLimitScalarSmooth
import Yau.Proofs.F01SpatialHolderEndpointLimit

/-! The terminal scalar charts of one genuine sequence glue to one
native smooth function. Values and every actual spatial jet converge
to that function; compatibility is proved by uniqueness of limits. -/
noncomputable section
open Set Filter Metric
open scoped ContDiff Manifold Topology
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic Yau.LeafProofs.L17Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem smooth_scalar_limit_of_chart_limits
    (g : HermitianField M) (hg : MetricSmooth g) (A : BoundedChartFamily g)
    (f : ℕ → M.Carrier → ℝ) {σ : ℝ} (hσ : 0 < σ) (hσr : σ ≤ A.radius)
    (hLocal : ∀ a : M.Carrier, ∃ W : Space n → ℝ,
      ContDiffOn ℝ ∞ W (ball 0 (1 / 2)) ∧
      ∀ q, TendstoUniformlyOn
        (fun m x => iteratedFDeriv ℝ q
          (fun z => (σ ^ 2)⁻¹ * f m ((A.chart a) (σ • z))) x)
        (iteratedFDeriv ℝ q W) atTop (ball 0 (1 / 2))) :
    ∃ u : M.Carrier → ℝ, SmoothFn u ∧
      (∀ x, Tendsto (fun m => f m x) atTop (𝓝 (u x))) ∧
      ∀ a q, TendstoUniformlyOn
        (fun m x => iteratedFDeriv ℝ q
          (fun z => (σ ^ 2)⁻¹ * f m ((A.chart a) (σ • z))) x)
        (iteratedFDeriv ℝ q (fun z => (σ ^ 2)⁻¹ * u ((A.chart a) (σ • z))))
        atTop (ball 0 (1 / 2)) := by
  classical
  choose W hW hQ using hLocal
  have hσ2 : σ ^ 2 ≠ 0 := pow_ne_zero 2 hσ.ne'
  have hValues (a : M.Carrier) (x : Space n) (hx : x ∈ ball 0 (1 / 2)) :
      Tendsto (fun m => (σ ^ 2)⁻¹ * f m ((A.chart a) (σ • x))) atTop (𝓝 (W a x)) := by
    have hEval : Continuous (fun D : ContinuousMultilinearMap ℝ
        (fun _ : Fin 0 => Space n) ℝ => D 0) := by fun_prop
    have hh := hEval.continuousAt.tendsto.comp ((hQ a 0).tendsto_at hx)
    change Tendsto (fun m => (σ ^ 2)⁻¹ * f m ((A.chart a) (σ • x))) atTop (𝓝 (W a x)) at hh
    exact hh
  let u : M.Carrier → ℝ := fun x => σ ^ 2 * W x 0
  have hUnscaled (a : M.Carrier) (x : Space n) (hx : x ∈ ball 0 (1 / 2)) :
      Tendsto (fun m => f m ((A.chart a) (σ • x))) atTop (𝓝 (σ ^ 2 * W a x)) := by
    have hh : Tendsto (fun m => σ ^ 2 * ((σ ^ 2)⁻¹ * f m ((A.chart a) (σ • x))))
        atTop (𝓝 (σ ^ 2 * W a x)) := tendsto_const_nhds.mul (hValues a x hx)
    simpa only [← mul_assoc, mul_inv_cancel₀ hσ2, one_mul] using hh
  have hPoint (x : M.Carrier) : Tendsto (fun m => f m x) atTop (𝓝 (u x)) := by
    simpa only [smul_zero, A.center x] using
      hUnscaled x 0 (mem_ball_self (by norm_num))
  have hEq (a : M.Carrier) (x : Space n) (hx : x ∈ ball 0 (1 / 2)) :
      u ((A.chart a) (σ • x)) = σ ^ 2 * W a x :=
    tendsto_nhds_unique (hPoint _) (hUnscaled a x hx)
  have hSmooth : SmoothFn u := by
    apply smoothFn_of_bounded_atlas_coefficients g hg A (r := σ / 2)
      (by positivity) (by linarith) u
    intro a
    have hInv : ContDiffOn ℝ ∞ (fun z : Space n => σ⁻¹ • z) (ball 0 (σ / 2)) :=
      (σ⁻¹ • ContinuousLinearMap.id ℝ (Space n)).contDiff.contDiffOn
    have hMap : MapsTo (fun z : Space n => σ⁻¹ • z) (ball 0 (σ / 2)) (ball 0 (1 / 2)) := by
      intro z hz
      rw [mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hσ)]
      have hzN : ‖z‖ < σ / 2 := by simpa only [mem_ball, dist_zero_right] using hz
      calc
        _ < σ⁻¹ * (σ / 2) := mul_lt_mul_of_pos_left hzN (inv_pos.mpr hσ)
        _ = 1 / 2 := by field_simp [hσ.ne']
    apply (contDiffOn_const.mul ((hW a).comp hInv hMap)).congr
    intro z hz
    simpa only [Function.comp_apply, smul_smul, mul_inv_cancel₀ hσ.ne', one_smul]
      using hEq a (σ⁻¹ • z) (hMap hz)
  refine ⟨u, hSmooth, hPoint, ?_⟩
  intro a q
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [(Metric.tendstoUniformlyOn_iff.mp (hQ a q)) ε hε] with m hm
  intro x hx
  have he : (fun z => (σ ^ 2)⁻¹ * u ((A.chart a) (σ • z))) =ᶠ[𝓝 x] W a := by
    filter_upwards [isOpen_ball.mem_nhds hx] with z hz
    rw [hEq a z hz, ← mul_assoc, inv_mul_cancel₀ hσ2, one_mul]
  rw [(he.iteratedFDeriv ℝ q).eq_of_nhds]
  exact hm x hx

end Yau.NodeProofs.F01Aux
