import Yau.Proofs.P06WeakDDbarCurrentChart
import Yau.Proofs.P06OrderAlgebra

/-! Genuine compact positive (1,1) forms obtained from fixed positive chart
matrices.  Their metric pairing retains both inverse factors and the volume
density of the original Riemannian measure. -/
noncomputable section
open MeasureTheory Filter
open scoped Manifold Topology ContDiff Matrix ComplexOrder

namespace Yau.NodeProofs.P06Aux.CurrentSeparation
open Yau Yau.Blueprint Yau.LeafProofs Yau.LeafProofs.L03
open Yau.NodeProofs.G04Aux WeakCurrent
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false

theorem formLE_of_oneOne_J_nonneg (B : RealForm M 2) (h11 : RealOneOne B)
    (hpos : ∀ y (u : TangentVector M y), 0 ≤ B y ![u, Complex.I • u]) :
    FormLE 0 B := by
  intro y
  rw [formHermitianMatrix_zero, sub_zero]
  have hH := (representsSelf B h11).2 y
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hH
  intro v
  apply Complex.nonneg_iff.mpr
  refine ⟨?_, (hH.im_star_dotProduct_mulVec_self v).symm⟩
  let w : ComplexVector n := WithLp.toLp 2 v
  have he := (representsSelf B h11).1 y w (Complex.I • w)
  change B y ![chartVec y y w, chartVec y y (Complex.I • w)] =
    2 * (matrixPairing (formHermitianMatrix B y) w (Complex.I • w)).im at he
  rw [L12Aux.chartVec_complex_smul, matrixPairing_smul_right] at he
  simp only [Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_add] at he
  have hp := hpos y (chartVec y y w)
  rw [matrixPairing_eq_dot] at he
  change B y ![chartVec y y w, Complex.I • chartVec y y w] =
    2 * (star v ⬝ᵥ (formHermitianMatrix B y *ᵥ v)).re at he
  linarith

def chartPositiveTest (c : M.Carrier) (φ : ComplexVector n → ℝ)
    (D : Matrix (Fin n) (Fin n) ℂ) (hD : D.IsHermitian) : RealForm M 2 :=
  chartFormPushforward c (fun z => φ z • modelIotaForm D hD)

theorem chartPositiveTest_apply_source (c : M.Carrier) (φ : ComplexVector n → ℝ)
    (D : Matrix (Fin n) (Fin n) ℂ) (hD : D.IsHermitian)
    (y : M.Carrier) (hy : y ∈ (extChartAt (ComplexModel n) c).source)
    (V : Fin 2 → TangentVector M y) :
    chartPositiveTest c φ D hD y V = φ (chartPt c y) *
      modelIotaForm D hD (fun r => tangentCoords c y (V r)) := by
  simp only [chartPositiveTest, chartFormPushforward, L18Aux.chartPushforwardZero,
    ite_eq_left hy, ContinuousAlternatingMap.compContinuousLinearMap_apply,
    Function.comp_def, ContinuousAlternatingMap.smul_apply, smul_eq_mul,
    tangentCoordsRealContinuousLinearMap_apply]

theorem chartPositiveTest_zero_off_source (c : M.Carrier) (φ : ComplexVector n → ℝ)
    (D : Matrix (Fin n) (Fin n) ℂ) (hD : D.IsHermitian)
    (y : M.Carrier) (hy : y ∉ (extChartAt (ComplexModel n) c).source) :
    chartPositiveTest c φ D hD y = 0 := by
  ext V
  simp only [chartPositiveTest, chartFormPushforward, L18Aux.chartPushforwardZero,
    ite_eq_right hy, ContinuousAlternatingMap.compContinuousLinearMap_apply]
  rfl

theorem chartPositiveTest_oneOne (c : M.Carrier) (φ : ComplexVector n → ℝ)
    (D : Matrix (Fin n) (Fin n) ℂ) (hD : D.IsHermitian) :
    RealOneOne (chartPositiveTest c φ D hD) := by
  intro y u v
  by_cases hy : y ∈ (extChartAt (ComplexModel n) c).source
  · rw [chartPositiveTest_apply_source c φ D hD y hy,
      chartPositiveTest_apply_source c φ D hD y hy]
    have hcoord (w : TangentVector M y) :
        tangentCoords c y (Complex.I • w) = Complex.I • tangentCoords c y w :=
      map_smul (mfderiv (ComplexModel n) (ComplexModel n)
        (extChartAt (ComplexModel n) c) y) Complex.I w
    have he : (fun r : Fin 2 => tangentCoords c y (![Complex.I • u, Complex.I • v] r)) =
        ![Complex.I • tangentCoords c y u, Complex.I • tangentCoords c y v] := by
      funext r
      fin_cases r
      · exact hcoord u
      · exact hcoord v
    have he' : (fun r : Fin 2 => tangentCoords c y (![u, v] r)) =
        ![tangentCoords c y u, tangentCoords c y v] := by
      funext r
      fin_cases r <;> rfl
    rw [he, he', modelIotaForm_J]
  · rw [chartPositiveTest_zero_off_source c φ D hD y hy]
    rfl

theorem chartPositiveTest_nonnegative (c : M.Carrier) (φ : ComplexVector n → ℝ)
    (hφ : ∀ z, 0 ≤ φ z) (D : Matrix (Fin n) (Fin n) ℂ) (hD : D.PosSemidef) :
    FormLE 0 (chartPositiveTest c φ D hD.1) := by
  apply formLE_of_oneOne_J_nonneg _ (chartPositiveTest_oneOne c φ D hD.1)
  intro y u
  by_cases hy : y ∈ (extChartAt (ComplexModel n) c).source
  · rw [chartPositiveTest_apply_source c φ D hD.1 y hy]
    apply mul_nonneg (hφ _)
    rw [modelIotaForm_apply]
    have hcoord : tangentCoords c y (Complex.I • u) = Complex.I • tangentCoords c y u :=
      map_smul (mfderiv (ComplexModel n) (ComplexModel n)
        (extChartAt (ComplexModel n) c) y) Complex.I u
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, hcoord,
      matrixPairing_smul_right, Complex.mul_im, Complex.I_re, Complex.I_im,
      zero_mul, one_mul, zero_add]
    rw [matrixPairing_eq_dot]
    exact mul_nonneg (by norm_num) (Complex.nonneg_iff.mp
      (hD.dotProduct_mulVec_nonneg (WithLp.ofLp (tangentCoords c y u)))).1
  · rw [chartPositiveTest_zero_off_source c φ D hD.1 y hy]
    change (0 : ℝ) ≤ 0
    exact le_rfl

theorem chartPositiveTest_properties (c : M.Carrier) (φ : ComplexVector n → ℝ)
    (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ)
    (hφO : tsupport φ ⊆ chartTarget c)
    (D : Matrix (Fin n) (Fin n) ℂ) (hD : D.IsHermitian) :
    SmoothRealForm (chartPositiveTest c φ D hD) ∧
      CompactlySupportedRealForm (chartPositiveTest c φ D hD) ∧
      closure {y | chartPositiveTest c φ D hD y ≠ 0} ⊆
        (extChartAt (ComplexModel n) c).source := by
  have hP : ContDiff ℝ ∞ (fun z => φ z • modelIotaForm D hD) := hφ.smul contDiff_const
  have hcP : HasCompactSupport (fun z => φ z • modelIotaForm D hD) := hcφ.smul_right
  have hPO : tsupport (fun z => φ z • modelIotaForm D hD) ⊆ chartTarget c :=
    (tsupport_smul_subset_left φ (fun _ => modelIotaForm D hD)).trans hφO
  exact ⟨chartFormPushforward_smooth c _ hP hcP hPO,
    chartFormPushforward_compactlySupported c _ hP hcP hPO,
    chartFormPushforward_source_support c _ hP hcP hPO⟩

theorem alternatingMatrix_modelIotaForm (D : Matrix (Fin n) (Fin n) ℂ)
    (hD : D.IsHermitian) : alternatingMatrix (modelIotaForm D hD) = D := by
  apply alternatingMatrix_eq_of_represents
  intro u v
  exact modelIotaForm_apply D hD ![u, v]

theorem alternatingMatrix_real_smul (a : ℝ)
    (P : (ComplexVector n) [⋀^Fin 2]→L[ℝ] ℝ) :
    alternatingMatrix (a • P) = (a : ℂ) • alternatingMatrix P := by
  ext i j
  apply Complex.ext <;>
    simp [alternatingMatrix, ContinuousAlternatingMap.smul_apply, smul_eq_mul,
      Complex.mul_re, Complex.mul_im] <;> ring

theorem chartHermitianMatrix_chartPositiveTest (c : M.Carrier)
    (φ : ComplexVector n → ℝ) (D : Matrix (Fin n) (Fin n) ℂ) (hD : D.IsHermitian)
    {z : ComplexVector n} (hz : z ∈ chartTarget c) :
    chartHermitianMatrix (chartPositiveTest c φ D hD) c z = (φ z : ℂ) • D := by
  rw [chartHermitianMatrix, chartPositiveTest, chartFormPushforward_to_chart c _ hz,
    alternatingMatrix_real_smul, alternatingMatrix_modelIotaForm]

theorem chartHermitianMatrix_center (A : RealForm M 2) (c : M.Carrier) :
    chartHermitianMatrix A c (chartPt c c) = formHermitianMatrix A c := by
  have he : chartForm A c (chartPt c c) = centeredForm A c := by
    have hi : chartInv c (chartPt c c) = c :=
      (extChartAt (ComplexModel n) c).left_inv (mem_extChartAt_source c)
    exact congrArg (fun y => (A y).compContinuousLinearMap
      (chartRealContinuousLinearMap c y)) hi
  rw [chartHermitianMatrix, he, centeredForm_matrix]

def chartPairDensity (g : HermitianField M) (A : RealForm M 2) (c : M.Carrier)
    (D : Matrix (Fin n) (Fin n) ℂ) (z : ComplexVector n) : ℝ :=
  Real.sqrt (realMetricFn g c z).det *
    (Matrix.trace ((hMat g c z)⁻¹ * chartHermitianMatrix A c z * (hMat g c z)⁻¹ * D)).re

theorem chartPairDensity_continuousOn (g : SmoothMetric M) (A : RealForm M 2)
    (hA : SmoothRealForm A) (c : M.Carrier) (D : Matrix (Fin n) (Fin n) ℂ) :
    ContinuousOn (chartPairDensity g.form A c D) (chartTarget c) := by
  have hi := L18Aux.hMat_inverse_contDiffOn g c
  have hM := chartHermitianMatrix_contDiffOn A hA c
  apply (L18Aux.volumeDensity_contDiffOn g c).continuousOn.mul
  apply Complex.continuous_re.comp_continuousOn
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  apply continuousOn_finsetSum
  intro a _
  apply continuousOn_finsetSum
  intro b _
  apply ContinuousOn.mul _ continuousOn_const
  apply continuousOn_finsetSum
  intro d _
  apply ContinuousOn.mul _ (hi d b).continuousOn
  apply continuousOn_finsetSum
  intro e _
  exact (hi a e).continuousOn.mul (hM e d).continuousOn

theorem integral_chartPositiveTest (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (A : RealForm M 2)
    (hA : SmoothRealForm A) (h11 : RealOneOne A)
    (c : M.Carrier) (φ : ComplexVector n → ℝ)
    (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ)
    (hφO : tsupport φ ⊆ chartTarget c)
    (D : Matrix (Fin n) (Fin n) ℂ) (hD : D.IsHermitian) :
    (∫ y, formInner g.form A (chartPositiveTest c φ D hD) y ∂μ) =
      ∫ z, φ z * chartPairDensity g.form A c D z ∂lebesgueC n := by
  obtain ⟨hB, _, hsB⟩ := chartPositiveTest_properties c φ hφ hcφ hφO D hD
  have hcont := formInner_continuous g A _ hA hB
  have hs : tsupport (formInner g.form A (chartPositiveTest c φ D hD)) ⊆
      (extChartAt (ComplexModel n) c).source := by
    rw [formInner_symm g.form A _]
    exact (formInner_support_subset_left g.form _ A).trans hsB
  rw [L18Aux.integral_chart_volume_of_tsupport g μ hμ c _ hcont.measurable hs]
  apply integral_congr_ae
  filter_upwards [] with z
  by_cases hz : z ∈ chartTarget c
  · simp only [L18Aux.chartPullbackZero, ite_eq_left hz]
    rw [formInner_chart_oneOne g.form A _ h11 (chartPositiveTest_oneOne c φ D hD) c hz,
      chartHermitianMatrix_chartPositiveTest c φ D hD hz,
      Matrix.mul_smul, Matrix.trace_smul]
    simp only [chartPairDensity, smul_eq_mul, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero]
    ring
  · have hφz : φ z = 0 := image_eq_zero_of_notMem_tsupport (fun h => hz (hφO h))
    simp only [L18Aux.chartPullbackZero, ite_eq_right hz, hφz, mul_zero, zero_mul]

end Yau.NodeProofs.P06Aux.CurrentSeparation
