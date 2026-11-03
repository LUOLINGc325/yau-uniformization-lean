import Yau.LeafProofs.L19BochnerIdentity
import Yau.LeafProofs.L19OrthonormalTrace

/-! The genuine coordinate Bochner identity gives the exact complex
curvature-dimension inequality with coefficient `1 / n`. -/

noncomputable section

open MeasureTheory Filter
open scoped Topology ContDiff Manifold Matrix ComplexOrder

namespace Yau.LeafProofs.L19Aux

open L18Aux

variable {n : ℕ} {M : ComplexManifold n}

theorem chartRealLaplacian_eventuallyEq (h : HermitianField M) (a : M.Carrier)
    {f k : ComplexVector n → ℝ} {z : ComplexVector n} (heq : f =ᶠ[𝓝 z] k) :
    chartRealLaplacian h a f z = chartRealLaplacian h a k z := by
  have hfirst (i : RIdx n) : rDeriv f z i = rDeriv k z i :=
    congrArg (fun D : ComplexVector n →L[ℝ] ℝ => D (realVec i)) heq.fderiv_eq
  have hsecond (i j : RIdx n) : rDeriv (fun w => rDeriv f w j) z i =
      rDeriv (fun w => rDeriv k w j) z i := by
    have heqD : (fun w => rDeriv f w j) =ᶠ[𝓝 z] (fun w => rDeriv k w j) :=
      (heq.fderiv (𝕜 := ℝ)).mono (fun _ hD =>
        congrArg (fun D : ComplexVector n →L[ℝ] ℝ => D (realVec j)) hD)
    exact congrArg (fun D : ComplexVector n →L[ℝ] ℝ => D (realVec i)) heqD.fderiv_eq
  simp only [chartRealLaplacian, chartCovHessian, hfirst, hsecond]

theorem chartGradientPair_eventuallyEq_right (h : HermitianField M) (a : M.Carrier)
    (f : ComplexVector n → ℝ) {k q : ComplexVector n → ℝ} {z : ComplexVector n}
    (heq : k =ᶠ[𝓝 z] q) :
    chartGradientPair h a f k z = chartGradientPair h a f q z := by
  unfold chartGradientPair rDeriv
  rw [heq.fderiv_eq]

theorem chartGradientPair_const_mul_right (h : HermitianField M) (a : M.Carrier)
    (f : ComplexVector n → ℝ) {k : ComplexVector n → ℝ} {z : ComplexVector n}
    (hk : DifferentiableAt ℝ k z) (c : ℝ) :
    chartGradientPair h a f (fun w => c * k w) z = c * chartGradientPair h a f k z := by
  have hvec : (fun i => rDeriv (fun w => c * k w) z i) =
      c • (fun i => rDeriv k z i) := by
    funext i
    exact rDeriv_const_mul hk c i
  unfold chartGradientPair
  rw [hvec]
  simp only [map_smul, smul_eq_mul]

theorem smoothFn_gradNormSq (g : SmoothMetric M) {f : M.Carrier → ℝ}
    (hf : SmoothFn f) : SmoothFn (gradNormSq g.form f) := by
  have heq : gradNormSq g.form f =
      (fun y => (1 / 2 : ℝ) * scalarGradientPair g.form f f y) := by
    funext y
    rw [scalarGradientPair_eq_twice_gradNormSq g.form hf]
    ring
  rw [heq]
  exact smoothFn_mul (smoothFn_const _) (smoothFn_scalarGradientPair g hf hf)

/-- The trace inequality is instantiated with a complete physical
orthonormal frame of the actual tangent inner product. -/
theorem chartCovHessian_trace_sq_le_dimension (g : SmoothMetric M) (x : M.Carrier)
    {f : ComplexVector n → ℝ} (hf : ContDiffAt ℝ 2 f (chartPt x x)) :
    chartRealLaplacian g.form x f (chartPt x x) ^ 2 ≤
      (2 * (n : ℝ)) * Matrix.trace
        ((realMetricFn g.form x (chartPt x x))⁻¹ * chartCovHessian g.form x f (chartPt x x) *
        (realMetricFn g.form x (chartPt x x))⁻¹ * chartCovHessian g.form x f (chartPt x x)) := by
  let := L12Aux.underlyingRealTangentNormedAddCommGroup g.form x
  let := L12Aux.underlyingRealTangentInnerProductSpace g.form x
  let e := centeredRealFrameBasis x
  let b := L12Aux.realInitialOrthonormalFrame g x
  have hGram : (e.toMatrix b.toBasis)ᵀ * realMetricFn g.form x (chartPt x x) *
      e.toMatrix b.toBasis = 1 := by
    rw [← centeredRealFrameBasis_gram g.form x]
    exact gram_change_to_orthonormal e b
  have hCS := metric_hessian_trace_sq_le
    (realMetricFn g.form x (chartPt x x)) (chartCovHessian g.form x f (chartPt x x))
    (e.toMatrix b.toBasis) (b.toBasis.toMatrix e)
    (L12Aux.realMetricFn_posDef g.form x (chartPt x x) (mem_extChartAt_target x)).det_pos.ne'
    (e.toMatrix_mul_toMatrix_flip b.toBasis) hGram (chartCovHessian_symm _ _ hf)
  have htrace : chartRealLaplacian g.form x f (chartPt x x) =
      Matrix.trace ((realMetricFn g.form x (chartPt x x))⁻¹ *
        chartCovHessian g.form x f (chartPt x x)) := by
    rw [chartRealLaplacian_eq_inverseMetric_trace _ _ hf, realBilinMatrix_covHessian _ _ hf]
  rw [htrace]
  simpa only [Fintype.card_fin, Nat.cast_mul, Nat.cast_ofNat] using hCS

/-- Converting the genuine real Bochner formula to the project's complex
normalization gives exactly twice the intrinsic CD left-hand side. -/
theorem complex_bochner_identity (g : SmoothMetric M) (hK : IsKahler g)
    {f : M.Carrier → ℝ} (hf : SmoothFn f) (x : M.Carrier) :
    2 * (laplacian g.form (gradNormSq g.form f) x -
        scalarGradientPair g.form f (laplacian g.form f) x) =
      Matrix.trace ((realMetricFn g.form x (chartPt x x))⁻¹ *
        chartCovHessian g.form x (inChart x f) (chartPt x x) *
        (realMetricFn g.form x (chartPt x x))⁻¹ *
        chartCovHessian g.form x (inChart x f) (chartPt x x)) +
      (L12Aux.realRicciMatrix g.form x (chartPt x x)).toBilin'
        ((realMetricFn g.form x (chartPt x x))⁻¹ *ᵥ (fun i => rDeriv (inChart x f) (chartPt x x) i))
        ((realMetricFn g.form x (chartPt x x))⁻¹ *ᵥ (fun i => rDeriv (inChart x f) (chartPt x x) i)) := by
  have hz : chartPt x x ∈ chartTarget x := mem_extChartAt_target x
  have hO := isOpen_extChartAt_target (I := ComplexModel n) x
  have hval : chartInv x (chartPt x x) = x :=
    (extChartAt (ComplexModel n) x).left_inv (mem_extChartAt_source x)
  have hP := smoothFn_scalarGradientPair g hf hf
  have hL := smoothFn_laplacian g hf
  have hQ := smoothFn_gradNormSq g hf
  have hPE : chartGradientPair g.form x (inChart x f) (inChart x f) =ᶠ[𝓝 (chartPt x x)]
      inChart x (scalarGradientPair g.form f f) := by
    filter_upwards [hO.mem_nhds hz] with z hz
    exact (scalarGradientPair_eq_chart g.form hf hf x hz).symm
  have hEnergy : chartRealLaplacian g.form x
      (chartGradientPair g.form x (inChart x f) (inChart x f)) (chartPt x x) =
      4 * laplacian g.form (gradNormSq g.form f) x := by
    rw [chartRealLaplacian_eventuallyEq g.form x hPE,
      kahler_realLaplacian_on g hK hP x hz, hval]
    have heq : scalarGradientPair g.form f f = (fun y => 2 * gradNormSq g.form f y) :=
      funext (scalarGradientPair_eq_twice_gradNormSq g.form hf)
    have hD : deriv (fun t : ℝ => 2 * t) = fun _ => 2 := by
      funext t
      simpa only [id_eq, mul_one] using ((hasDerivAt_id t).const_mul 2).deriv
    rw [heq, laplacian_scalar_comp g.form hQ (fun t : ℝ => 2 * t) x
      (contDiffAt_const.mul contDiffAt_id), hD]
    simp only [deriv_const, mul_zero, zero_mul, add_zero]
    ring
  have hDR : chartRealLaplacian g.form x (inChart x f) =ᶠ[𝓝 (chartPt x x)]
      (fun w => 2 * inChart x (laplacian g.form f) w) := by
    filter_upwards [hO.mem_nhds hz] with z hz
    exact kahler_realLaplacian_on g hK hf x hz
  have hPair : chartGradientPair g.form x (inChart x f)
      (chartRealLaplacian g.form x (inChart x f)) (chartPt x x) =
      2 * scalarGradientPair g.form f (laplacian g.form f) x := by
    rw [chartGradientPair_eventuallyEq_right g.form x _ hDR,
      chartGradientPair_const_mul_right g.form x _
        ((contDiffAt_inChart hL x hz).differentiableAt (by simp))]
    rfl
  have hb := chart_bochner_identity g x (hf x) hz
  rw [hEnergy, hPair] at hb
  linarith

/-- Exact complex curvature-dimension inequality, with every geometric
input the original metric, Kähler condition and pointwise Ricci positivity. -/
theorem complexCD_inequality (g : SmoothMetric M) (hK : IsKahler g)
    (hRic : ∀ x, (ricci g.form x).PosSemidef)
    {f : M.Carrier → ℝ} (hf : SmoothFn f) (x : M.Carrier) :
    laplacian g.form (gradNormSq g.form f) x -
        scalarGradientPair g.form f (laplacian g.form f) x ≥
      laplacian g.form f x ^ 2 / (n : ℝ) := by
  have hn : (0 : ℝ) < n := by exact_mod_cast L12Aux.complexDimension_pos M
  have hz : chartPt x x ∈ chartTarget x := mem_extChartAt_target x
  have hval : chartInv x (chartPt x x) = x :=
    (extChartAt (ComplexModel n) x).left_inv (mem_extChartAt_source x)
  have hCS := chartCovHessian_trace_sq_le_dimension g x
    ((contDiffAt_inChart hf x hz).of_le (by simp))
  rw [kahler_realLaplacian_on g hK hf x hz, hval] at hCS
  have hRicTerm : 0 ≤ (L12Aux.realRicciMatrix g.form x (chartPt x x)).toBilin'
      ((realMetricFn g.form x (chartPt x x))⁻¹ *ᵥ (fun i => rDeriv (inChart x f) (chartPt x x) i))
      ((realMetricFn g.form x (chartPt x x))⁻¹ *ᵥ (fun i => rDeriv (inChart x f) (chartPt x x) i)) := by
    simpa only [Matrix.toBilin'_apply', star_trivial] using
      (L12Aux.realRicciMatrix_posSemidef g hK x (hRic x)).dotProduct_mulVec_nonneg
        ((realMetricFn g.form x (chartPt x x))⁻¹ *ᵥ
          (fun i => rDeriv (inChart x f) (chartPt x x) i))
  have hB := complex_bochner_identity g hK hf x
  have hBn := congrArg (fun t : ℝ => (n : ℝ) * t) hB
  apply (div_le_iff₀ hn).2
  nlinarith [mul_nonneg hn.le hRicTerm]

end Yau.LeafProofs.L19Aux
