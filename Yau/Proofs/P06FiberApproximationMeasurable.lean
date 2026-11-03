import Yau.Proofs.P06FiberApproximationL2

noncomputable section
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace ComplexOrder MatrixOrder
namespace Yau.NodeProofs.P06Aux.FiberApprox
open Yau Yau.LeafProofs G04Aux Clip P06ClipBernstein
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {M : ComplexManifold n}

/-- The all-chart polynomial formula preserves the actual local coefficient measurability,
even when the input is only a raw L² form. -/
theorem polynomialForm_coefficients_measurable (g : SmoothMetric M) (μ : Measure M.Carrier)
    (A : RealForm M 2) (hA : L2RealForm g.form μ A) (h11 : RealOneOne A)
    (p : Polynomial ℝ) (c : M.Carrier) (I : Fin 2 → RIdx n) : AEStronglyMeasurable
      (fun y => FiberPoly.polynomialForm g.form A h11 p y (fun r => chartVec c y (realVec (I r))))
      (μ.restrict (chartAt (ComplexVector n) c).source) := by
  letI : SecondCountableTopology (Matrix (RIdx n) (RIdx n) ℝ) :=
    inferInstanceAs (SecondCountableTopology (RIdx n → RIdx n → ℝ))
  letI : TopologicalSpace.PseudoMetrizableSpace (Matrix (RIdx n) (RIdx n) ℝ) :=
    inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (RIdx n → RIdx n → ℝ))
  let ν := μ.restrict (chartAt (ComplexVector n) c).source
  have hsrc : ∀ᵐ y ∂ν, y ∈ (extChartAt (ComplexModel n) c).source := by
    simpa only [ν, extChartAt_source] using
      (ae_restrict_mem (chartAt (ComplexVector n) c).open_source.measurableSet)
  have hAm : AEStronglyMeasurable (fun y => chartFormMatrix A c (chartPt c y)) ν := by
    apply AEMeasurable.aestronglyMeasurable
    apply aemeasurable_pi_iff.mpr
    intro i
    apply aemeasurable_pi_iff.mpr
    intro j
    apply (hA.1 c ![i,j]).aemeasurable.congr
    filter_upwards [hsrc] with y hy
    simpa only [chartFormMatrix, L03.localRealBasis_apply] using
      (L03.formComponents_apply_of_mem_source A c y hy ![i,j]).symm
  have hGc : ContinuousOn (fun y => realMetricFn g.form c (chartPt c y))
      (chartAt (ComplexVector n) c).source := by
    apply (L03.realMetricFn_continuousOn g c).comp (L03.chartPt_continuousOn c)
    intro y hy
    exact (extChartAt (ComplexModel n) c).map_source (by simpa only [extChartAt_source] using hy)
  have hG := hGc.aestronglyMeasurable (chartAt (ComplexVector n) c).open_source.measurableSet (μ := μ)
  have hGi := (L03.realMetricFn_inv_in_chart_continuousOn g c).aestronglyMeasurable
    (chartAt (ComplexVector n) c).open_source.measurableSet (μ := μ)
  have hS := (hGi.mul hAm).mul_const (L12Aux.jMatrix n)
  have hpoly : Continuous (fun S : Matrix (RIdx n) (RIdx n) ℝ => Polynomial.aeval S p) := by
    simp only [FiberPoly.aeval_sum]
    fun_prop
  have hT := ((hG.mul (hpoly.comp_aestronglyMeasurable hS)).mul_const (L12Aux.jMatrix n)).neg
  have hc : Continuous (fun B : Matrix (RIdx n) (RIdx n) ℝ => B (I 0) (I 1)) := by fun_prop
  have hm := hc.comp_aestronglyMeasurable hT
  apply hm.congr
  filter_upwards [hsrc] with y hy
  have hz : chartPt c y ∈ chartTarget c := (extChartAt (ComplexModel n) c).map_source hy
  have hcoeff := L03.formComponents_apply_of_mem_source
    (FiberPoly.polynomialForm g.form A h11 p) c y hy I
  simp only [L03.localRealBasis_apply] at hcoeff
  rw [← hcoeff, formComponents_degree_two,
    FiberPoly.polynomialForm_chart g.form A h11 p c hz]
  rfl

/-- A single sequence of polynomials converges at every real scalar;
the interval grows and the Bernstein error tends to zero. -/
theorem exists_polynomials_tendsto_everywhere (F : ℝ → ℝ) (hF : LipschitzWith 1 F)
    (h0 : F 0 = 0) : ∃ p : ℕ → Polynomial ℝ,
      ∀ r, Tendsto (fun j => (p j).eval r) atTop (𝓝 (F r)) := by
  have hex (j : ℕ) : ∃ N : ℕ, ∀ r ∈ Icc (-((j : ℝ) + 1)) ((j : ℝ) + 1),
      |(zeroFixedBernstein ((j : ℝ) + 1) F N).eval r - F r| ≤ (1 / 2 : ℝ) ^ j := by
    obtain ⟨N, hN⟩ := zeroFixedBernstein_uniform_error
      (show 0 < (j : ℝ) + 1 by positivity) hF h0 (show 0 < (1 / 2 : ℝ) ^ j by positivity)
    exact ⟨N, hN N le_rfl⟩
  choose N hN using hex
  refine ⟨fun j => zeroFixedBernstein ((j : ℝ) + 1) F (N j), ?_⟩
  intro r
  have hlim : Tendsto (fun j : ℕ => (1 / 2 : ℝ) ^ j) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hmem : ∀ᶠ j : ℕ in atTop, r ∈ Icc (-((j : ℝ) + 1)) ((j : ℝ) + 1) := by
    obtain ⟨m, hm⟩ := exists_nat_gt |r|
    filter_upwards [eventually_ge_atTop m] with j hj
    have hmj : (m : ℝ) ≤ j := by exact_mod_cast hj
    exact abs_le.mp (by linarith : |r| ≤ (j : ℝ) + 1)
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hev := (Metric.tendsto_nhds.mp hlim) ε hε
  filter_upwards [hmem, hev] with j hj he
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity : 0 ≤ (1 / 2 : ℝ) ^ j)] at he
  exact (hN j r hj).trans_lt he

/-- Arbitrary pointwise scalar approximation gives actual tangent coefficient limits. -/
theorem polynomialForm_evaluation_tendsto_everywhere (g : HermitianField M)
    (A : RealForm M 2) (h11 : RealOneOne A) (p : ℕ → Polynomial ℝ) (F : ℝ → ℝ)
    (ht : ∀ r, Tendsto (fun j => (p j).eval r) atTop (𝓝 (F r)))
    (x : M.Carrier) (v : Fin 2 → TangentVector M x) :
    Tendsto (fun j => FiberPoly.polynomialForm g A h11 (p j) x v) atTop
      (𝓝 (functionalForm g A F x v)) := by
  have ha := cfc_tendsto_of_eigenvalues _ (whiteHermitian g A h11 x)
    (fun j r => (p j).eval r) F (fun i => ht _)
  simp only [cfc_polynomial _ _ (show IsSelfAdjoint _ from whiteHermitian g A h11 x)] at ha
  have hu : Continuous (metricUnwhiten (gMat g x)) := by
    change Continuous (fun X : Matrix (Fin n) (Fin n) ℂ => metricRoot (gMat g x) * X * metricRoot (gMat g x))
    fun_prop
  have hH : (gMat g x).PosDef := L12Aux.hMat_posDef g x (chartPt x x) (mem_extChartAt_target x)
  have he (j : ℕ) : metricUnwhiten (gMat g x)
      (Polynomial.aeval (metricWhiten (gMat g x) (formHermitianMatrix A x)) (p j)) =
      FiberPoly.fiberMatrix g A (p j) x := by
    have hw := congrArg (metricUnwhiten (gMat g x))
      (metricWhiten_aeval (gMat g x) (formHermitianMatrix A x) hH (p j))
    rw [metricUnwhiten_whiten (gMat g x) _ hH] at hw
    exact hw.symm
  have hm := (hu.tendsto _).comp ha
  simp only [Function.comp_def, he] at hm
  have hc : Continuous (fun B : Matrix (Fin n) (Fin n) ℂ =>
      2 * (matrixPairing B (tangentCoords x x (v 0)) (tangentCoords x x (v 1))).im) := by
    dsimp only [matrixPairing]
    fun_prop
  exact (hc.tendsto _).comp hm

/-- Every zero-fixed scalar contraction has a genuine raw L² functional calculus.
The local coefficient measurability is derived from the original raw L² data. -/
theorem functionalForm_l2_of_l2 (g : SmoothMetric M) (μ : Measure M.Carrier)
    (A : RealForm M 2) (hA : L2RealForm g.form μ A) (h11 : RealOneOne A)
    (F : ℝ → ℝ) (hF : LipschitzWith 1 F) (h0 : F 0 = 0) :
    L2RealForm g.form μ (functionalForm g.form A F) := by
  obtain ⟨p, hp⟩ := exists_polynomials_tendsto_everywhere F hF h0
  refine ⟨?_, ?_⟩
  · intro c I
    apply aestronglyMeasurable_of_tendsto_ae atTop
      (fun j => polynomialForm_coefficients_measurable g μ A hA h11 (p j) c I)
    exact Eventually.of_forall (fun y => polynomialForm_evaluation_tendsto_everywhere
      g.form A h11 p F hp y _)
  · apply lt_of_le_of_lt (lintegral_mono (fun x => ENNReal.ofReal_le_ofReal ?_)) hA.2
    rw [formNormSq_eq_pointFormHS g.form _ (functionalForm_oneOne g.form A F),
      formNormSq_eq_pointFormHS g.form A h11]
    exact pow_le_pow_left₀ (norm_nonneg _) (functionalForm_pointNorm_le g.form A h11 F hF h0 x) 2

end Yau.NodeProofs.P06Aux.FiberApprox
