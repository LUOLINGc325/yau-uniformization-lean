import Yau.Proofs.P06FiberPolynomialForm

noncomputable section
open MeasureTheory Filter
open scoped Manifold Topology ContDiff Matrix ComplexOrder
namespace Yau.NodeProofs.P06Aux.FiberPoly
open Yau Yau.LeafProofs G04Aux L12Aux
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {M : ComplexManifold n}

theorem relativeEndomorphism_chart_raw (h : HermitianField M) (A : RealForm M 2)
    (h11 : RealOneOne A) (c : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget c) :
    P06Weitzenbock.relativeEndomorphism h A c z =
      G01Aux.rawReal ((hMat h c z)⁻¹ * chartHermitianMatrix A c z) := by
  rw [P06Weitzenbock.relativeEndomorphism,
    G01Aux.realMetricFn_inverse_eq h c z hz, chartHermitianMatrix_raw A h11 c hz]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  norm_num only [show (1 / 2 : ℝ) * (-2) = -1 by norm_num, neg_one_smul]
  rw [Matrix.mul_assoc, Matrix.mul_assoc, jMatrix_sq]
  simp only [Matrix.mul_neg, Matrix.mul_one, neg_neg]
  rw [← G01Aux.rawReal_mul]

/-- Naturality of the reconstructed real form under polynomial functional calculus. -/
theorem polynomialForm_relative (h : HermitianField M) (A : RealForm M 2)
    (h11 : RealOneOne A) (p : Polynomial ℝ) (c : M.Carrier)
    {z : ComplexVector n} (hz : z ∈ chartTarget c) :
    P06Weitzenbock.relativeEndomorphism h (polynomialForm h A h11 p) c z =
      Polynomial.aeval (P06Weitzenbock.relativeEndomorphism h A c z) p := by
  rw [relativeEndomorphism_chart_raw h _ (polynomialForm_oneOne h A h11 p) c hz,
    chartHermitianMatrix_polynomialForm h A h11 p c hz,
    ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _
      ((L12Aux.hMat_posDef h c z hz).isUnit.map Matrix.detMonoidHom), Matrix.one_mul,
    rawReal_aeval, relativeEndomorphism_chart_raw h A h11 c hz]

/-- The requested formula holds in every genuine chart. -/
theorem polynomialForm_chart (h : HermitianField M) (A : RealForm M 2)
    (h11 : RealOneOne A) (p : Polynomial ℝ) (c : M.Carrier)
    {z : ComplexVector n} (hz : z ∈ chartTarget c) :
    chartFormMatrix (polynomialForm h A h11 p) c z =
      -(realMetricFn h c z * Polynomial.aeval
        (P06Weitzenbock.relativeEndomorphism h A c z) p * jMatrix n) := by
  rw [← polynomialForm_relative h A h11 p c hz, P06Weitzenbock.relativeEndomorphism]
  have hG : IsUnit (realMetricFn h c z).det :=
    isUnit_iff_ne_zero.mpr (realMetricFn_posDef h c z hz).det_pos.ne'
  have he : realMetricFn h c z *
      ((realMetricFn h c z)⁻¹ * chartFormMatrix (polynomialForm h A h11 p) c z * jMatrix n) *
      jMatrix n = -chartFormMatrix (polynomialForm h A h11 p) c z := by
    calc
      _ = (realMetricFn h c z * (realMetricFn h c z)⁻¹) *
          chartFormMatrix (polynomialForm h A h11 p) c z * (jMatrix n * jMatrix n) := by
        noncomm_ring
      _ = _ := by
        rw [Matrix.mul_nonsing_inv _ hG, jMatrix_sq]
        simp only [Matrix.one_mul, Matrix.mul_neg, Matrix.mul_one]
  rw [he, neg_neg]

/-- Smoothness is deduced from the all-chart formula and the original smooth input. -/
theorem polynomialForm_smooth (g : SmoothMetric M) (A : RealForm M 2)
    (hA : SmoothRealForm A) (h11 : RealOneOne A) (p : Polynomial ℝ) :
    SmoothRealForm (polynomialForm g.form A h11 p) := by
  have hs := metricSmooth_of_smoothMetric g
  intro c I
  have hS : ∀ i j, ContDiffOn ℝ ∞
      (fun w => P06Weitzenbock.relativeEndomorphism g.form A c w i j) (chartTarget c) :=
    entries_contDiffOn_mul
      (entries_contDiffOn_mul (L23Aux.realMetricFn_inverse_contDiffOn g.form hs c)
        (fun i j => hA c ![i,j]))
      (fun i j => contDiffOn_const)
  have hP := entries_contDiffOn_mul
    (entries_contDiffOn_mul (hs c) (entries_contDiffOn_aeval hS p))
    (fun i j => (contDiffOn_const : ContDiffOn ℝ ∞
      (fun _ : ComplexVector n => jMatrix n i j) (chartTarget c)))
  apply (hP (I 0) (I 1)).neg.congr
  intro z hz
  rw [formComponents_degree_two, polynomialForm_chart g.form A h11 p c hz]
  rfl

/-- The exact actual covariant chain rule, with no matrix-gradient hypothesis. -/
theorem polynomialForm_covariant_chain (g : SmoothMetric M) (hK : IsKahler g)
    (A : RealForm M 2) (hA : SmoothRealForm A) (h11 : RealOneOne A)
    (p : Polynomial ℝ) (c : M.Carrier) {z : ComplexVector n}
    (hz : z ∈ chartTarget c) (a : RIdx n) :
    (realMetricFn g.form c z)⁻¹ *
      P06Weitzenbock.covariantTwoMatrix g.form (polynomialForm g.form A h11 p) c z a *
      jMatrix n =
    Clip.polynomialVariation p (P06Weitzenbock.relativeEndomorphism g.form A c z)
      ((realMetricFn g.form c z)⁻¹ * P06Weitzenbock.covariantTwoMatrix g.form A c z a * jMatrix n) := by
  have hs := metricSmooth_of_smoothMetric g
  rw [← P06Weitzenbock.relativeEndomorphism_covariant_derivative g.form hs hK
    (polynomialForm g.form A h11 p) (polynomialForm_smooth g A hA h11 p) c hz a]
  have he : P06Weitzenbock.relativeEndomorphism g.form (polynomialForm g.form A h11 p) c
      =ᶠ[𝓝 z] (fun w => Polynomial.aeval (P06Weitzenbock.relativeEndomorphism g.form A c w) p) := by
    filter_upwards [(isOpen_extChartAt_target (I := ComplexModel n) c).mem_nhds hz] with w hw
    exact polynomialForm_relative g.form A h11 p c hw
  simp only [matrixDirectionalDerivative_congr he, polynomialForm_relative g.form A h11 p c hz]
  exact relative_polynomial_covariant_derivative g hK A hA c hz a p

/-- A polynomial vanishing at zero creates no new support. -/
theorem polynomialForm_zero_of_zero (h : HermitianField M) (A : RealForm M 2)
    (h11 : RealOneOne A) (p : Polynomial ℝ) (hp : p.eval 0 = 0)
    (x : M.Carrier) (hx : A x = 0) : polynomialForm h A h11 p x = 0 := by
  have hM : formHermitianMatrix A x = 0 := by
    ext a b
    simp [formHermitianMatrix, hx]
  have hp0 : p.coeff 0 = 0 := by simpa only [Polynomial.coeff_zero_eq_eval_zero] using hp
  have hF : fiberMatrix h A p x = 0 := by
    rw [fiberMatrix, hM, Matrix.mul_zero,
      ← Polynomial.coeff_zero_eq_aeval_zero', hp0, map_zero, Matrix.mul_zero]
  ext V
  change 2 * (matrixPairing (fiberMatrix h A p x) _ _).im = 0
  rw [hF]
  simp [matrixPairing]

theorem polynomialForm_support_subset (h : HermitianField M) (A : RealForm M 2)
    (h11 : RealOneOne A) (p : Polynomial ℝ) (hp : p.eval 0 = 0) :
    {x | polynomialForm h A h11 p x ≠ 0} ⊆ {x | A x ≠ 0} := by
  intro x hx hzero
  exact hx (polynomialForm_zero_of_zero h A h11 p hp x hzero)

theorem polynomialForm_compactlySupported (h : HermitianField M) (A : RealForm M 2)
    (h11 : RealOneOne A) (p : Polynomial ℝ) (hp : p.eval 0 = 0)
    (hcA : CompactlySupportedRealForm A) :
    CompactlySupportedRealForm (polynomialForm h A h11 p) :=
  hcA.of_isClosed_subset isClosed_closure
    (closure_mono (polynomialForm_support_subset h A h11 p hp))

theorem polynomialForm_l2 (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (A : RealForm M 2)
    (hA : SmoothRealForm A) (h11 : RealOneOne A) (p : Polynomial ℝ)
    (hp : p.eval 0 = 0) (hcA : CompactlySupportedRealForm A) :
    L2RealForm g.form μ (polynomialForm g.form A h11 p) :=
  L03.smooth_compactlySupported_l2RealForm g μ hμ _
    (polynomialForm_smooth g A hA h11 p)
    (polynomialForm_compactlySupported g.form A h11 p hp hcA)

end Yau.NodeProofs.P06Aux.FiberPoly
