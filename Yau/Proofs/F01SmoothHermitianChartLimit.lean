import Yau.Proofs.F01ChartMatrixRecovery
import Yau.Proofs.F01HermitianFieldMatrixLimit
import Yau.Proofs.F01AtlasLimitMetricSmooth
import Yau.Proofs.F01FrobeniusEntryJetBounds

/-! Smooth limits in the original bounded charts assemble to one
native smooth Hermitian field. Overlap compatibility follows from
uniqueness of the original metric sequence's pointwise limits. -/
noncomputable section
open Set Filter Metric
open scoped ContDiff Manifold Topology Matrix ComplexOrder Matrix.Norms.Frobenius
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic Yau.LeafProofs.L17Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem smooth_hermitian_limit_of_chart_limits
    (g : HermitianField M) (hg : MetricSmooth g) (A : BoundedChartFamily g)
    (k : ℕ → HermitianField M) {σ ell C : ℝ}
    (hσ : 0 < σ) (hσr : σ ≤ A.radius) (hell : 0 < ell)
    (hLower : ∀ m x, (gMat (k m) x - (ell : ℂ) • gMat g x).PosSemidef)
    (hUpper : ∀ m x, ((C : ℂ) • gMat g x - gMat (k m) x).PosSemidef)
    (hLocal : ∀ a : M.Carrier, ∃ G : Space n → Matrix (Fin n) (Fin n) ℂ,
      ContDiffOn ℝ ∞ G (ball 0 (1 / 2)) ∧
      ∀ q, TendstoUniformlyOn
        (fun m x => iteratedFDeriv ℝ q
          (fun z => pullbackMatrix (k m) (A.chart a) (σ • z)) x)
        (iteratedFDeriv ℝ q G) atTop (ball 0 (1 / 2))) :
    ∃ K : HermitianField M, MetricSmooth K ∧
      (∀ x, Tendsto (fun m => gMat (k m) x) atTop (𝓝 (gMat K x))) ∧
      (∀ x, (gMat K x - (ell : ℂ) • gMat g x).PosSemidef ∧
        ((C : ℂ) • gMat g x - gMat K x).PosSemidef) ∧
      ∀ a q, TendstoUniformlyOn
        (fun m x => iteratedFDeriv ℝ q
          (fun z => pullbackMatrix (k m) (A.chart a) (σ • z)) x)
        (iteratedFDeriv ℝ q (fun z => pullbackMatrix K (A.chart a) (σ • z)))
        atTop (ball 0 (1 / 2)) := by
  classical
  choose G hG hQ using hLocal
  have hValues (a : M.Carrier) (x : Space n) (hx : x ∈ ball 0 (1 / 2)) :
      Tendsto (fun m => pullbackMatrix (k m) (A.chart a) (σ • x)) atTop (𝓝 (G a x)) := by
    have hEval : Continuous (fun D : ContinuousMultilinearMap ℝ
        (fun _ : Fin 0 => Space n) (Matrix (Fin n) (Fin n) ℂ) => D 0) := by fun_prop
    have hh := hEval.continuousAt.tendsto.comp ((hQ a 0).tendsto_at hx)
    change Tendsto (fun m => pullbackMatrix (k m) (A.chart a) (σ • x))
      atTop (𝓝 (G a x)) at hh
    exact hh
  have hExists (x : M.Carrier) : ∃ H : Matrix (Fin n) (Fin n) ℂ,
      Tendsto (fun m => gMat (k m) x) atTop (𝓝 H) := by
    have h0 : (0 : Space n) ∈ ball 0 (1 / 2) := mem_ball_self (by norm_num)
    have hSource : (0 : Space n) ∈ (A.chart x).source :=
      A.closedBall_source x (mem_closedBall_self A.radius_pos.le)
    have hh := native_matrix_limit_from_chart (A.chart x) (A.differentiable x)
      (A.inverse_differentiable x) hSource k (G x 0)
      (by simpa only [smul_zero] using hValues x 0 h0)
    simpa only [A.center x] using hh
  obtain ⟨K, hNative, hOrders, hPullback⟩ :=
    hermitian_field_of_native_matrix_limits g k hell hExists hLower hUpper
  have hEq (a : M.Carrier) (x : Space n) (hx : x ∈ ball 0 (1 / 2)) :
      pullbackMatrix K (A.chart a) (σ • x) = G a x :=
    tendsto_nhds_unique (hPullback (A.chart a) (σ • x)) (hValues a x hx)
  have hSmall (a : M.Carrier) : ContDiffOn ℝ ∞
      (fun z => pullbackMatrix K (A.chart a) z) (ball 0 (σ / 2)) := by
    have hInv : ContDiffOn ℝ ∞ (fun z : Space n => σ⁻¹ • z) (ball 0 (σ / 2)) :=
      (σ⁻¹ • ContinuousLinearMap.id ℝ (Space n)).contDiff.contDiffOn
    have hMap : MapsTo (fun z : Space n => σ⁻¹ • z) (ball 0 (σ / 2)) (ball 0 (1 / 2)) := by
      intro z hz
      rw [mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hσ)]
      have hzN : ‖z‖ < σ / 2 := by simpa only [mem_ball, dist_zero_right] using hz
      calc
        _ < σ⁻¹ * (σ / 2) := mul_lt_mul_of_pos_left hzN (inv_pos.mpr hσ)
        _ = 1 / 2 := by field_simp [hσ.ne']
    apply ((hG a).comp hInv hMap).congr
    intro z hz
    have hh := hEq a (σ⁻¹ • z) (hMap hz)
    simpa only [Function.comp_apply, smul_smul, mul_inv_cancel₀ hσ.ne', one_smul] using hh
  have hMetric : MetricSmooth K := by
    apply metricSmooth_of_bounded_atlas_coefficients g K hg A
      (r := σ / 2) (by positivity) (by linarith)
    intro a i j
    exact (frobeniusComplexEntryCLM i j).contDiff.comp_contDiffOn (hSmall a)
  refine ⟨K, hMetric, hNative, hOrders, ?_⟩
  intro a q
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [(Metric.tendstoUniformlyOn_iff.mp (hQ a q)) ε hε] with m hm
  intro x hx
  have he : (fun z => pullbackMatrix K (A.chart a) (σ • z)) =ᶠ[𝓝 x] G a := by
    filter_upwards [isOpen_ball.mem_nhds hx] with z hz using hEq a z hz
  rw [(he.iteratedFDeriv ℝ q).eq_of_nhds]
  exact hm x hx

end Yau.NodeProofs.F01Aux
