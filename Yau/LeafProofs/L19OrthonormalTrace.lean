import Yau.LeafProofs.L19BochnerRicci
import Yau.LeafProofs.L19EndpointEnergyShape

/-! Pointwise traces in genuine physical orthonormal frames. The frame
matrix may use a different finite index type from the coordinate frame. -/

noncomputable section

open MeasureTheory Filter
open scoped Topology ContDiff Manifold Matrix ComplexOrder InnerProductSpace

namespace Yau.LeafProofs.L19Aux

open L18Aux

section Matrices

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- Completeness and orthonormality of the columns identify the genuine
inverse metric, even when the two bases use different finite indices. -/
theorem inverseMetric_eq_orthonormal_columns (G : Matrix ι ι ℝ)
    (D : Matrix ι κ ℝ) (E : Matrix κ ι ℝ) (hG : G.det ≠ 0)
    (hDE : D * E = 1) (hGram : Dᵀ * G * D = 1) : G⁻¹ = D * Dᵀ := by
  have hGG : G * G⁻¹ = 1 := Matrix.mul_nonsing_inv G (isUnit_iff_ne_zero.mpr hG)
  have hDG : Dᵀ * G = E := by
    calc
      _ = (Dᵀ * G) * (D * E) := by rw [hDE, Matrix.mul_one]
      _ = (Dᵀ * G * D) * E := by simp only [Matrix.mul_assoc]
      _ = E := by rw [hGram, Matrix.one_mul]
  symm
  calc
    D * Dᵀ = D * (Dᵀ * (G * G⁻¹)) := by rw [hGG, Matrix.mul_one]
    _ = D * (Dᵀ * G) * G⁻¹ := by simp only [Matrix.mul_assoc]
    _ = G⁻¹ := by rw [hDG, hDE, Matrix.one_mul]

/-- The weighted coordinate trace equals the ordinary trace after a
genuine complete orthonormal change of frame. -/
theorem inverseMetric_trace_eq_orthonormal_trace (G H : Matrix ι ι ℝ)
    (D : Matrix ι κ ℝ) (E : Matrix κ ι ℝ) (hG : G.det ≠ 0)
    (hDE : D * E = 1) (hGram : Dᵀ * G * D = 1) :
    Matrix.trace (G⁻¹ * H) = Matrix.trace (Dᵀ * H * D) := by
  rw [inverseMetric_eq_orthonormal_columns G D E hG hDE hGram]
  calc
    Matrix.trace (D * Dᵀ * H) = Matrix.trace (D * (Dᵀ * H)) := by rw [Matrix.mul_assoc]
    _ = Matrix.trace (Dᵀ * H * D) := Matrix.trace_mul_comm _ _

theorem inverseMetric_trace_square_eq_orthonormal_trace_square (G H : Matrix ι ι ℝ)
    (D : Matrix ι κ ℝ) (E : Matrix κ ι ℝ) (hG : G.det ≠ 0)
    (hDE : D * E = 1) (hGram : Dᵀ * G * D = 1) :
    Matrix.trace (G⁻¹ * H * G⁻¹ * H) =
      Matrix.trace ((Dᵀ * H * D) * (Dᵀ * H * D)) := by
  rw [inverseMetric_eq_orthonormal_columns G D E hG hDE hGram]
  calc
    _ = Matrix.trace (D * (Dᵀ * H * D * Dᵀ * H)) := by
      congr 1
      simp only [Matrix.mul_assoc]
    _ = Matrix.trace ((Dᵀ * H * D * Dᵀ * H) * D) := Matrix.trace_mul_comm _ _
    _ = _ := by congr 1; simp only [Matrix.mul_assoc]

/-- Cauchy--Schwarz is applied to the symmetric Hessian in a physical
orthonormal frame, never incorrectly to the generally nonsymmetric G⁻¹H. -/
theorem metric_hessian_trace_sq_le (G H : Matrix ι ι ℝ)
    (D : Matrix ι κ ℝ) (E : Matrix κ ι ℝ) (hG : G.det ≠ 0)
    (hDE : D * E = 1) (hGram : Dᵀ * G * D = 1) (hH : H.IsSymm) :
    Matrix.trace (G⁻¹ * H) ^ 2 ≤
      (Fintype.card κ : ℝ) * Matrix.trace (G⁻¹ * H * G⁻¹ * H) := by
  have hhat : (Dᵀ * H * D).IsSymm := by
    change (Dᵀ * H * D)ᵀ = Dᵀ * H * D
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hH]
    simp only [Matrix.mul_assoc]
  rw [inverseMetric_trace_eq_orthonormal_trace G H D E hG hDE hGram,
    inverseMetric_trace_square_eq_orthonormal_trace_square G H D E hG hDE hGram]
  exact L12Aux.trace_sq_le_card_trace_mul_self _ hhat

end Matrices

section Bases

variable {ι κ V : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]

omit [DecidableEq ι] in
theorem gram_change_to_orthonormal (e : Module.Basis ι ℝ V) (b : OrthonormalBasis κ ℝ V) :
    (e.toMatrix b.toBasis)ᵀ * Matrix.gram ℝ e * e.toMatrix b.toBasis = 1 := by
  let D := e.toMatrix b.toBasis
  let E := b.toBasis.toMatrix e
  have hED : E * D = 1 := b.toBasis.toMatrix_mul_toMatrix_flip e
  have hG : Matrix.gram ℝ e = Eᵀ * E := by
    have hE : E = Matrix.of (fun i j => b.repr (e j) i) := by
      ext i j
      exact b.coe_toBasis_repr_apply (e j) i
    rw [hE]
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.gram_eq_conjTranspose_mul b e
  change Dᵀ * Matrix.gram ℝ e * D = 1
  rw [hG]
  calc
    Dᵀ * (Eᵀ * E) * D = (E * D)ᵀ * (E * D) := by
      simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    _ = 1 := by rw [hED, Matrix.transpose_one, Matrix.one_mul]

/-- Any bilinear form has the same physical trace in a complete actual
orthonormal basis and in an arbitrary genuine coordinate basis. -/
theorem basis_inverseGram_trace_eq_orthonormal_sum (e : Module.Basis ι ℝ V)
    (b : OrthonormalBasis κ ℝ V) (B : LinearMap.BilinForm ℝ V) :
    Matrix.trace ((Matrix.gram ℝ e)⁻¹ * LinearMap.BilinForm.toMatrix e B) =
      ∑ i, B (b i) (b i) := by
  have hG : (Matrix.gram ℝ e).det ≠ 0 :=
    Matrix.det_gram_ne_zero_iff_linearIndependent.mpr e.linearIndependent
  have ht := inverseMetric_trace_eq_orthonormal_trace
    (Matrix.gram ℝ e) (LinearMap.BilinForm.toMatrix e B)
    (e.toMatrix b.toBasis) (b.toBasis.toMatrix e) hG
    (e.toMatrix_mul_toMatrix_flip b.toBasis) (gram_change_to_orthonormal e b)
  rw [LinearMap.BilinForm.toMatrix_mul_basis_toMatrix] at ht
  simpa only [Matrix.trace, Matrix.diag_apply, LinearMap.BilinForm.toMatrix_apply,
    OrthonormalBasis.coe_toBasis] using ht

end Bases

variable {n : ℕ} {M : ComplexManifold n}

theorem realFrameCLM_eq_centeredRealFrame (x : M.Carrier) (v : ComplexVector n) :
    L12Aux.realFrameCLM x x v = centeredRealFrameEquiv x v := by
  have hz : chartPt x x ∈ chartTarget x := mem_extChartAt_target x
  have hval : chartInv x (chartPt x x) = x :=
    (extChartAt (ComplexModel n) x).left_inv (mem_extChartAt_source x)
  have hcoord := L12Aux.realCoordinateField_eq_realChartVec x (chartPt x x) v hz
  have hreal := L12Aux.realTangentEquiv_realChartVec x (chartPt x x) v hz
  rw [hval] at hcoord hreal
  rw [L12Aux.realFrameCLM_apply x x (mem_chart_source _ _), hcoord,
    centeredRealFrameEquiv_apply]
  apply (L12Aux.realTangentEquiv x).injective
  rw [ContinuousLinearEquiv.apply_symm_apply]
  exact hreal

theorem realTangentCoords_centeredRealFrameBasis (x : M.Carrier) (i : RIdx n) :
    L12Aux.realTangentCoords x x (centeredRealFrameBasis x i) = realVec i := by
  rw [centeredRealFrameBasis_apply, ← centeredRealFrameEquiv_apply,
    ← realFrameCLM_eq_centeredRealFrame,
    L12Aux.realTangentCoords_realFrameCLM x x (mem_chart_source _ _)]

/-- Any actual physical orthonormal frame computes the same inverse-metric
trace of an arbitrary continuous bilinear chart tensor. -/
theorem chartBilinear_inverseMetric_trace_eq_orthonormal
    {κ : Type*} [Fintype κ] [DecidableEq κ] (h : HermitianField M) (x : M.Carrier)
    (B₀ : ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ℝ)
    (b : letI := L12Aux.underlyingRealTangentNormedAddCommGroup h x
      letI := L12Aux.underlyingRealTangentInnerProductSpace h x
      OrthonormalBasis κ ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) x)) :
    Matrix.trace ((realMetricFn h x (chartPt x x))⁻¹ * realBilinMatrix B₀) =
      ∑ i, B₀ (L12Aux.realTangentCoords x x (b i))
        (L12Aux.realTangentCoords x x (b i)) := by
  letI := L12Aux.underlyingRealTangentNormedAddCommGroup h x
  letI := L12Aux.underlyingRealTangentInnerProductSpace h x
  let e := centeredRealFrameBasis x
  let B : LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) x) :=
    LinearMap.BilinForm.comp B₀.toLinearMap₁₂ (L12Aux.realTangentCoords x x).toLinearMap
      (L12Aux.realTangentCoords x x).toLinearMap
  have ht := basis_inverseGram_trace_eq_orthonormal_sum e b B
  have hmatrix : LinearMap.BilinForm.toMatrix e B = realBilinMatrix B₀ := by
    ext i j
    simp only [LinearMap.BilinForm.toMatrix_apply, B, e, LinearMap.BilinForm.comp_apply,
      ContinuousLinearMap.coe_coe, ContinuousLinearMap.toLinearMap₁₂_apply,
      realTangentCoords_centeredRealFrameBasis, realBilinMatrix_apply]
    rfl
  rw [centeredRealFrameBasis_gram h x, hmatrix] at ht
  exact ht

/-- Continuous bilinear packaging of the displayed coordinate covariant
Hessian. It requires no smoothness outside the point where it is used. -/
def chartCovHessianBilin (h : HermitianField M) (a : M.Carrier)
    (f : ComplexVector n → ℝ) (z : ComplexVector n) :
    ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ℝ :=
  fderiv ℝ (fderiv ℝ f) z -
    ((ContinuousLinearMap.compL ℝ (ComplexVector n) (ComplexVector n) ℝ)
      (fderiv ℝ f z)).comp (L12Aux.chartChristoffelBilin h a z)

theorem chartCovHessianBilin_apply (h : HermitianField M) (a : M.Carrier)
    (f : ComplexVector n → ℝ) (z u v : ComplexVector n) :
    chartCovHessianBilin h a f z u v = fderiv ℝ (fderiv ℝ f) z u v -
      fderiv ℝ f z (L12Aux.chartChristoffelBilin h a z u v) := rfl

theorem realBilinMatrix_covHessian (h : HermitianField M) (a : M.Carrier)
    {f : ComplexVector n → ℝ} {z : ComplexVector n} (hf : ContDiffAt ℝ 2 f z) :
    realBilinMatrix (chartCovHessianBilin h a f z) = chartCovHessian h a f z := by
  ext i j
  rw [realBilinMatrix_apply, chartCovHessianBilin_apply, L12Aux.chartChristoffelBilin_basis]
  simp only [map_sum, map_smul, smul_eq_mul, chartCovHessian]
  rw [rDeriv_rDeriv_eq_hessian hf]
  rfl

theorem chartRealLaplacian_eq_inverseMetric_trace (h : HermitianField M) (a : M.Carrier)
    {f : ComplexVector n → ℝ} {z : ComplexVector n} (hf : ContDiffAt ℝ 2 f z) :
    chartRealLaplacian h a f z = Matrix.trace
      ((realMetricFn h a z)⁻¹ * realBilinMatrix (chartCovHessianBilin h a f z)) := by
  rw [realBilinMatrix_covHessian h a hf]
  simp only [chartRealLaplacian, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [(chartCovHessian_symm h a hf).apply i j]

/-- The local C² scalar operator is the physical orthonormal trace of its
actual covariant Hessian, without a global SmoothFn premise. -/
theorem chartRealLaplacian_eq_orthonormal_covHessian
    {κ : Type*} [Fintype κ] [DecidableEq κ] (h : HermitianField M) (x : M.Carrier)
    {f : ComplexVector n → ℝ} (hf : ContDiffAt ℝ 2 f (chartPt x x))
    (b : letI := L12Aux.underlyingRealTangentNormedAddCommGroup h x
      letI := L12Aux.underlyingRealTangentInnerProductSpace h x
      OrthonormalBasis κ ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) x)) :
    chartRealLaplacian h x f (chartPt x x) =
      ∑ i, (fderiv ℝ (fderiv ℝ f) (chartPt x x)
          (L12Aux.realTangentCoords x x (b i)) (L12Aux.realTangentCoords x x (b i)) -
        fderiv ℝ f (chartPt x x) (L12Aux.chartChristoffelBilin h x (chartPt x x)
          (L12Aux.realTangentCoords x x (b i)) (L12Aux.realTangentCoords x x (b i)))) := by
  rw [chartRealLaplacian_eq_inverseMetric_trace h x hf,
    chartBilinear_inverseMetric_trace_eq_orthonormal h x _ b]
  rfl

/-- The local physical energy is the sum of squared directional
differentials in any actual physical orthonormal basis. -/
theorem chartGradientPair_self_eq_orthonormal_sum
    {κ : Type*} [Fintype κ] [DecidableEq κ] (h : HermitianField M) (x : M.Carrier)
    (f : ComplexVector n → ℝ)
    (b : letI := L12Aux.underlyingRealTangentNormedAddCommGroup h x
      letI := L12Aux.underlyingRealTangentInnerProductSpace h x
      OrthonormalBasis κ ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) x)) :
    chartGradientPair h x f f (chartPt x x) =
      ∑ i, (fderiv ℝ f (chartPt x x) (L12Aux.realTangentCoords x x (b i))) ^ 2 := by
  let B₀ := (fderiv ℝ f (chartPt x x)).smulRight (fderiv ℝ f (chartPt x x))
  have htrace : chartGradientPair h x f f (chartPt x x) =
      Matrix.trace ((realMetricFn h x (chartPt x x))⁻¹ * realBilinMatrix B₀) := by
    rw [chartGradientPair_eq_sum]
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [realBilinMatrix_apply]
    simp only [B₀, ContinuousLinearMap.smulRight_apply, smul_apply,
      smul_eq_mul, rDeriv]
    ring
  rw [htrace, chartBilinear_inverseMetric_trace_eq_orthonormal h x B₀ b]
  simp only [B₀, ContinuousLinearMap.smulRight_apply, smul_apply,
    smul_eq_mul, pow_two]

end Yau.LeafProofs.L19Aux
