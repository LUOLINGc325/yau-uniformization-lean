import Yau.Proofs.P06WeakDDbarCurrentTests

noncomputable section
open MeasureTheory Filter
open scoped Manifold Topology ContDiff Matrix ComplexOrder

namespace Yau.NodeProofs.P06Aux.WeakCurrent
open Yau Yau.LeafProofs Yau.LeafProofs.L03 Yau.NodeProofs.G04Aux
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {M : ComplexManifold n}

theorem chartHermitianMatrix_omega (g : HermitianField M) (c : M.Carrier)
    (z : ComplexVector n) : chartHermitianMatrix (omegaForm g) c z = hMat g c z := by
  apply alternatingMatrix_eq_of_represents
  intro u v
  rw [chartForm_apply_two, omegaForm_apply, hMat_matrixPairing]

theorem formTrace_chart_matrix (g : HermitianField M) (B : RealForm M 2)
    (h11 : RealOneOne B) (c : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget c) :
    formTrace g B (chartInv c z) =
      (Matrix.trace ((hMat g c z)⁻¹ * chartHermitianMatrix B c z)).re := by
  rw [formTrace_eq_inner_omega g B h11,
    formInner_chart_oneOne g B _ h11 (omegaForm_oneOne g) c hz, chartHermitianMatrix_omega]
  have hu := (L12Aux.hMat_posDef g c z hz).isUnit.map Matrix.detMonoidHom
  rw [Matrix.mul_assoc ((hMat g c z)⁻¹ * chartHermitianMatrix B c z),
    Matrix.nonsing_inv_mul _ hu, Matrix.mul_one]

theorem weightedChartMatrix_trace (g : HermitianField M) (B : RealForm M 2)
    (h11 : RealOneOne B) (c : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget c) :
    (Matrix.trace (hMat g c z * weightedChartMatrix g B c z)).re =
      Real.sqrt (realMetricFn g c z).det * formTrace g B (chartInv c z) := by
  rw [formTrace_chart_matrix g B h11 c hz]
  simp only [weightedChartMatrix, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  congr 1
  have hu := (L12Aux.hMat_posDef g c z hz).isUnit.map Matrix.detMonoidHom
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu,
    Matrix.one_mul, Matrix.trace_mul_comm]

/-- A compact positive chart test has the true dd pairing, in the original
volume measure, equal to the parent's scalar matrix-test dual. -/
theorem integral_dd_chart_dual (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (f : M.Carrier → ℝ) (hf : SmoothFn f)
    (B : RealForm M 2) (hB : SmoothRealForm B) (hcB : CompactlySupportedRealForm B)
    (h11 : RealOneOne B) (hp : FormLE 0 B) (c : M.Carrier)
    (hBc : closure {y | B y ≠ 0} ⊆ (extChartAt (ComplexModel n) c).source) :
    (∫ y, f y * ddAdjointScalar g.form B y ∂μ) =
      ∫ z, inChart c f z * leviMatrixTestDual (chartMatrixTest g.form B c) z ∂lebesgueC n := by
  have hreg := chartMatrixTest_regular g B hB hcB c hBc
  have hcont := formInner_continuous g (ddRealForm f) B (dd_smooth f hf) hB
  have hs : tsupport (formInner g.form (ddRealForm f) B) ⊆
      (extChartAt (ComplexModel n) c).source := by
    rw [formInner_symm g.form (ddRealForm f) B]
    exact (formInner_support_subset_left g.form B _).trans hBc
  rw [← integral_dd_eq_adjoint g μ hμ f hf B hB hcB,
    L18Aux.integral_chart_volume_of_tsupport g μ hμ c _ hcont.measurable hs]
  have he := integral_leviMatrixTestDual_classical
    (isOpen_extChartAt_target (I := ComplexModel n) c) (inChart c f) (hf c)
    (chartMatrixTest g.form B c)
    (fun z => (chartMatrixTest_nonnegative g.form B h11 hp c z).1)
    (fun a b => (hreg a b).1) (fun a b => (hreg a b).2.1) (fun a b => (hreg a b).2.2)
  rw [he]
  apply integral_congr_ae
  filter_upwards [] with z
  by_cases hz : z ∈ chartTarget c
  · simp only [L18Aux.chartPullbackZero, if_pos hz, chartMatrixTest]
    rw [weightedChartMatrix_dd_pair g.form f hf B h11 c hz]
  · simp only [L18Aux.chartPullbackZero, if_neg hz, chartMatrixTest, Matrix.mul_zero,
      Matrix.trace_zero, Complex.zero_re, mul_zero]

theorem integral_chartMatrixTest_trace (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (B : RealForm M 2)
    (hB : SmoothRealForm B) (hcB : CompactlySupportedRealForm B) (h11 : RealOneOne B)
    (c : M.Carrier)
    (hBc : closure {y | B y ≠ 0} ⊆ (extChartAt (ComplexModel n) c).source) :
    (∫ z, (Matrix.trace (hMat g.form c z * chartMatrixTest g.form B c z)).re ∂lebesgueC n) =
      ∫ y, formTrace g.form B y ∂μ := by
  have hs : tsupport (formTrace g.form B) ⊆ (extChartAt (ComplexModel n) c).source := by
    have he : formTrace g.form B = formInner g.form B (omegaForm g.form) :=
      funext (formTrace_eq_inner_omega g.form B h11)
    rw [he]
    exact (formInner_support_subset_left g.form B _).trans hBc
  have hcont := L18Aux.continuous_of_smoothFn
    (trace_smooth g.form (L12Aux.metricSmooth_of_smoothMetric g) B hB h11)
  rw [L18Aux.integral_chart_volume_of_tsupport g μ hμ c _ hcont.measurable hs]
  apply integral_congr_ae
  filter_upwards [] with z
  by_cases hz : z ∈ chartTarget c
  · simp only [chartMatrixTest, if_pos hz, L18Aux.chartPullbackZero]
    exact weightedChartMatrix_trace g.form B h11 c hz
  · simp only [chartMatrixTest, if_neg hz, L18Aux.chartPullbackZero, Matrix.mul_zero,
      Matrix.trace_zero, Complex.zero_re, mul_zero]

end Yau.NodeProofs.P06Aux.WeakCurrent
