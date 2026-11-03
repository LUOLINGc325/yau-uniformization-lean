import spec.CHAIN.LeafObligations
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Dual.Basis
import Yau.LeafProofs.L18

/-!
Metric-independence seed for L14, migrated verbatim from L07-028.
The weighted estimate and the complete L14/L07 roots remain unproved.
-/

noncomputable section

open scoped Manifold Topology ContDiff ComplexOrder ENNReal Matrix InnerProductSpace
open MeasureTheory Bundle Module

namespace Yau.LeafProofs

section HermitianAlgebra

variable {V : Type*} [AddCommGroup V] [Module ℂ V]
variable (h : HermitianInnerProduct V)

theorem hermitian_sum_left {ι : Type*} (s : Finset ι) (u : ι → V) (v : V) :
    h.toFun (∑ i ∈ s, u i) v = ∑ i ∈ s, h.toFun (u i) v := by
  classical
  have hz : h.toFun 0 v = 0 := by
    simpa using h.map_smul_left 0 (0 : V) v
  induction s using Finset.induction_on with
  | empty => simp [hz]
  | @insert i s hi ih => simp [hi, h.map_add_left, ih]

theorem hermitian_sum_right {ι : Type*} (s : Finset ι) (u : V) (v : ι → V) :
    h.toFun u (∑ i ∈ s, v i) = ∑ i ∈ s, h.toFun u (v i) := by
  classical
  have hz : h.toFun u 0 = 0 := by
    simpa using h.map_smul_right 0 u (0 : V)
  induction s using Finset.induction_on with
  | empty => simp [hz]
  | @insert i s hi ih => simp [hi, h.map_add_right, ih]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def hermitianGram (b : Basis ι ℂ V) : Matrix ι ι ℂ :=
  fun i j => h.toFun (b i) (b j)

theorem hermitian_coordinates (b : Basis ι ℂ V) (u v : V) :
    (∑ i, ∑ j, star (b.repr u i) * hermitianGram h b i j * b.repr v j) =
      h.toFun u v := by
  conv_rhs => rw [← b.sum_repr u, ← b.sum_repr v]
  simp only [hermitian_sum_left, hermitian_sum_right, h.map_smul_left,
    h.map_smul_right, hermitianGram, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem hermitianGram_changeBasis (b c : Basis ι ℂ V) :
    hermitianGram h c = (b.toMatrix c)ᴴ * hermitianGram h b * b.toMatrix c := by
  ext i j
  change h.toFun (c i) (c j) = _
  rw [← hermitian_coordinates h b]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Basis.toMatrix_apply,
    Finset.sum_mul]
  rw [Finset.sum_comm]

theorem hermitianGram_det_changeBasis (b c : Basis ι ℂ V) :
    (hermitianGram h c).det =
      star (b.toMatrix c).det * (hermitianGram h b).det * (b.toMatrix c).det := by
  rw [hermitianGram_changeBasis h b c, Matrix.det_mul, Matrix.det_mul,
    Matrix.det_conjTranspose]

theorem hermitianGram_isHermitian (b : Basis ι ℂ V) :
    (hermitianGram h b).IsHermitian := by
  ext i j
  exact (h.conjugate_symmetric (b i) (b j)).symm

theorem hermitianGram_posDef (b : Basis ι ℂ V) : (hermitianGram h b).PosDef := by
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  refine ⟨hermitianGram_isHermitian h b, ?_⟩
  intro v hv
  let u : V := ∑ i, v i • b i
  have hcoord : ∀ i, b.repr u i = v i := by
    intro i
    change b.repr (∑ j, v j • b j) i = v i
    rw [b.repr_sum_self]
  have hu : u ≠ 0 := by
    intro hu
    apply hv
    funext i
    simpa [hu] using (hcoord i).symm
  have heq : star v ⬝ᵥ (hermitianGram h b *ᵥ v) = h.toFun u u := by
    rw [← hermitian_coordinates h b u u]
    simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum, hcoord,
      mul_assoc]
  rw [heq, Complex.pos_iff]
  exact ⟨hermitianNormSq_pos h hu, (h.self_adjoint u).symm⟩

end HermitianAlgebra

section BundleFrames

open BundleDbar

variable {n r : ℕ} {M : ComplexManifold n}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

theorem chartInv_chartPt_of_mem (a x : M.Carrier)
    (hx : x ∈ (chartAt (ComplexVector n) a).source) :
    chartInv a (chartPt a x) = x := by
  apply (extChartAt (ComplexModel n) a).left_inv
  simpa only [extChartAt_source] using hx

end BundleFrames

section MetricIndependenceAlgebra

def matrixCoefficientPairing {n r : ℕ} (H : Matrix (Fin r) (Fin r) ℂ)
    (F U : Fin n → Fin r → ℂ) : ℂ :=
  ∑ i, ∑ α, ∑ β, star (F i α) * H α β * U i β

theorem coefficient_contraction_assoc {n r : ℕ}
    (B : Matrix (Fin n) (Fin n) ℂ) (H : Matrix (Fin r) (Fin r) ℂ)
    (F V : Fin n → Fin r → ℂ) :
    (∑ i, ∑ j, ∑ α, ∑ β, star (F i α) * H α β * B i j * V j β) =
      matrixCoefficientPairing H F (B * Matrix.of V) := by
  unfold matrixCoefficientPairing
  simp only [Matrix.mul_apply, Matrix.of_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro α _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro β _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem matrix_isHermitian_det_im {r : ℕ} (A : Matrix (Fin r) (Fin r) ℂ)
    (hA : A.IsHermitian) : A.det.im = 0 := by
  have hs : star A.det = A.det := by rw [← Matrix.det_conjTranspose, hA.eq]
  have hi := congrArg Complex.im hs
  simp only [Complex.star_def, Complex.conj_im] at hi
  linarith

end MetricIndependenceAlgebra

section BundleMetricIndependence

open BundleDbar

variable {n r : ℕ} {M : ComplexManifold n}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

theorem coefficientInner_eq_pairing (g : HermitianField M) (h : Metric E) (x : M.Carrier)
    (F V : Fin n → Fin r → ℂ) :
    coefficientInner (r := r) E g h x F V =
      (gMat g x)⁻¹.det * matrixCoefficientPairing
        (BundleDbar.metricMatrix (r := r) E h x (chartPt x x)) F
        ((gMat g x)⁻¹ * Matrix.of V) := by
  exact congrArg (fun z => (gMat g x)⁻¹.det * z)
    (coefficient_contraction_assoc (gMat g x)⁻¹
      (BundleDbar.metricMatrix (r := r) E h x (chartPt x x)) F V)

theorem inverseCurvatureNormSq_factor (g : HermitianField M) (h : Metric E)
    (φ : M.Carrier → ℝ) (f : NQForm E 1) (x : M.Carrier)
    (hg : (gMat g x).PosDef) :
    inverseCurvatureNormSq (r := r) E g h φ f x =
      ENNReal.ofReal (gMat g x)⁻¹.det.re *
        ⨆ U : Fin n → Fin r → ℂ, ENNReal.ofReal
          (2 * (matrixCoefficientPairing
            (BundleDbar.metricMatrix (r := r) E h x (chartPt x x))
            (fun i α => coefficients (r := r) E f x (chartPt x x) (fun _ => i) α) U).re -
              nakanoQuadratic (weightedCurvature (r := r) E h φ x (chartPt x x)) U) := by
  let B := (gMat g x)⁻¹
  let H := BundleDbar.metricMatrix (r := r) E h x (chartPt x x)
  let F := fun i α => coefficients (r := r) E f x (chartPt x x) (fun _ => i) α
  let R := weightedCurvature (r := r) E h φ x (chartPt x x)
  have hb : B.det.im = 0 := matrix_isHermitian_det_im B hg.inv.isHermitian
  have hd : 0 ≤ B.det.re := (Complex.nonneg_iff.mp hg.inv.posSemidef.det_nonneg).1
  have ht (V : Fin n → Fin r → ℂ) :
      ENNReal.ofReal (2 * (coefficientInner (r := r) E g h x F V).re -
        curvatureEnergy (r := r) E g h φ x V) =
      ENNReal.ofReal B.det.re * ENNReal.ofReal
        (2 * (matrixCoefficientPairing H F (B * Matrix.of V)).re -
          nakanoQuadratic R (B * Matrix.of V)) := by
    rw [coefficientInner_eq_pairing E g h x F V, ← ENNReal.ofReal_mul hd]
    congr 1
    change 2 * (B.det * matrixCoefficientPairing H F (B * Matrix.of V)).re -
      B.det.re * nakanoQuadratic R (B * Matrix.of V) = _
    rw [Complex.mul_re, hb]
    ring
  unfold inverseCurvatureNormSq
  change (⨆ V : Fin n → Fin r → ℂ, ENNReal.ofReal
    (2 * (coefficientInner (r := r) E g h x F V).re - curvatureEnergy (r := r) E g h φ x V)) = _
  simp_rw [ht]
  rw [ENNReal.mul_iSup]
  apply le_antisymm
  · apply iSup_le
    intro V
    exact le_iSup (fun U => ENNReal.ofReal B.det.re * ENNReal.ofReal
      (2 * (matrixCoefficientPairing H F U).re - nakanoQuadratic R U)) (B * Matrix.of V)
  · apply iSup_le
    intro U
    refine le_iSup_of_le (gMat g x * Matrix.of U) ?_
    have hi : B * (gMat g x * Matrix.of U) = Matrix.of U := by
      rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (hg.isUnit.map Matrix.detMonoidHom),
        Matrix.one_mul]
    change ENNReal.ofReal B.det.re * ENNReal.ofReal
      (2 * (matrixCoefficientPairing H F U).re - nakanoQuadratic R U) ≤
        ENNReal.ofReal B.det.re * ENNReal.ofReal
          (2 * (matrixCoefficientPairing H F (B * (gMat g x * Matrix.of U))).re -
            nakanoQuadratic R (B * (gMat g x * Matrix.of U)))
    rw [hi]
    exact le_rfl

end BundleMetricIndependence

section TangentMetricAlgebra

def hermitianPullback {V W : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (h : HermitianInnerProduct V)
    (L : W →ₗ[ℂ] V) (hi : Function.Injective L) : HermitianInnerProduct W where
  toFun u v := h.toFun (L u) (L v)
  map_add_left u v w := by simp only [map_add, h.map_add_left]
  map_smul_left c u v := by simp only [map_smul, h.map_smul_left]
  map_add_right u v w := by simp only [map_add, h.map_add_right]
  map_smul_right c u v := by simp only [map_smul, h.map_smul_right]
  conjugate_symmetric u v := h.conjugate_symmetric (L u) (L v)
  self_adjoint u := h.self_adjoint (L u)
  positive_definite u := by
    have hz : L u = 0 ↔ u = 0 :=
      ⟨fun hh => hi (hh.trans L.map_zero.symm), fun hh => hh ▸ L.map_zero⟩
    exact ⟨(h.positive_definite (L u)).1, (h.positive_definite (L u)).2.trans hz⟩

variable {n : ℕ} {M : ComplexManifold n}

theorem inverse_chart_derivative_isInvertible (a : M.Carrier) (z : ComplexVector n)
    (hz : z ∈ chartTarget a) :
    (mfderiv (ComplexModel n) (ComplexModel n) (extChartAt (ComplexModel n) a).symm z).IsInvertible := by
  simpa only [(ComplexModel n).range_eq_univ, mfderivWithin_univ] using
    (isInvertible_mfderivWithin_extChartAt_symm (I := ComplexModel n) hz)

theorem hMat_posDef (g : HermitianField M) (a : M.Carrier) (z : ComplexVector n)
    (hz : z ∈ chartTarget a) : (hMat g a z).PosDef := by
  let L : ComplexVector n →L[ℂ] TangentVector M (chartInv a z) :=
    mfderiv (ComplexModel n) (ComplexModel n) (extChartAt (ComplexModel n) a).symm
      (chartPt a (chartInv a z))
  have hLI : L.IsInvertible := inverse_chart_derivative_isInvertible a _
    ((extChartAt (ComplexModel n) a).map_source ((extChartAt (ComplexModel n) a).map_target hz))
  have hi : Function.Injective L := by
    obtain ⟨e, he⟩ := hLI
    rw [← he]
    exact e.injective
  let h := hermitianPullback (g (chartInv a z)) L.toLinearMap hi
  have heq : hMat g a z = hermitianGram h (EuclideanSpace.basisFun (Fin n) ℂ).toBasis := by
    ext i j
    simp only [hMat, hermitianGram, h, hermitianPullback, OrthonormalBasis.coe_toBasis,
      EuclideanSpace.basisFun_apply]
    rfl
  rw [heq]
  exact hermitianGram_posDef _ _

theorem gMat_posDef (g : HermitianField M) (x : M.Carrier) : (gMat g x).PosDef :=
  hMat_posDef g x (chartPt x x) (mem_extChartAt_target x)

end TangentMetricAlgebra

section Realification

theorem realMetricFn_sqrt_det {n : ℕ} {M : ComplexManifold n}
    (g : HermitianField M) (a : M.Carrier) (z : ComplexVector n)
    (hz : z ∈ chartTarget a) :
    Real.sqrt (realMetricFn g a z).det = (2 : ℝ) ^ n * (hMat g a z).det.re :=
  L18Aux.paperVolumeNormalization g a z hz

end Realification

section BundleMetricFactors

open BundleDbar

variable {n r : ℕ} {M : ComplexManifold n}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

def topCoefficientNormSq (h : Metric E) (u : NQForm E 0) (x : M.Carrier) : ℝ :=
  (∑ α, ∑ β, star (coefficients (r := r) E u x (chartPt x x) Fin.elim0 α) *
    BundleDbar.metricMatrix (r := r) E h x (chartPt x x) α β *
      coefficients (r := r) E u x (chartPt x x) Fin.elim0 β).re

def inverseCurvatureCoefficientSup (h : Metric E) (φ : M.Carrier → ℝ)
    (f : NQForm E 1) (x : M.Carrier) : ℝ≥0∞ :=
  ⨆ U : Fin n → Fin r → ℂ, ENNReal.ofReal
    (2 * (matrixCoefficientPairing
      (BundleDbar.metricMatrix (r := r) E h x (chartPt x x))
      (fun i α => coefficients (r := r) E f x (chartPt x x) (fun _ => i) α) U).re -
        nakanoQuadratic (weightedCurvature (r := r) E h φ x (chartPt x x)) U)

theorem formNormSq_top_factor (g : HermitianField M) (h : Metric E)
    (u : NQForm E 0) (x : M.Carrier) :
    BundleDbar.formNormSq (r := r) E g h u x =
      (gMat g x)⁻¹.det.re * topCoefficientNormSq (r := r) E h u x := by
  have hi : (default : Fin 0 → Fin n) = Fin.elim0 := Subsingleton.elim _ _
  simp [BundleDbar.formNormSq, topCoefficientNormSq, Fintype.sum_unique, hi]

theorem inverseCurvatureNormSq_factor_of_metric (g : HermitianField M) (h : Metric E)
    (φ : M.Carrier → ℝ) (f : NQForm E 1) (x : M.Carrier) :
    inverseCurvatureNormSq (r := r) E g h φ f x =
      ENNReal.ofReal (gMat g x)⁻¹.det.re * inverseCurvatureCoefficientSup (r := r) E h φ f x :=
  inverseCurvatureNormSq_factor E g h φ f x (gMat_posDef g x)

end BundleMetricFactors

section MetricDensity

variable {V : Type*} [AddCommGroup V] [Module ℂ V]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem hermitianGram_det_changeBasis_re (h : HermitianInnerProduct V)
    (b c : Basis ι ℂ V) :
    (hermitianGram h c).det.re =
      Complex.normSq (b.toMatrix c).det * (hermitianGram h b).det.re := by
  rw [hermitianGram_det_changeBasis]
  simp only [Complex.mul_re, Complex.mul_im, Complex.star_def,
    Complex.conj_re, Complex.conj_im, Complex.normSq_apply]
  ring

theorem hermitianGram_det_ratio (h₁ h₂ : HermitianInnerProduct V)
    (b c : Basis ι ℂ V) :
    (hermitianGram h₁ c).det.re / (hermitianGram h₂ c).det.re =
      (hermitianGram h₁ b).det.re / (hermitianGram h₂ b).det.re := by
  rw [hermitianGram_det_changeBasis_re h₁ b c, hermitianGram_det_changeBasis_re h₂ b c]
  exact mul_div_mul_left _ _ (by
    apply mt Complex.normSq_eq_zero.mp
    exact (b.isUnit_det c).ne_zero)

variable {n : ℕ} {M : ComplexManifold n}

def chartFrameMap (a y : M.Carrier) : ComplexVector n →L[ℂ] TangentVector M y :=
  mfderiv (ComplexModel n) (ComplexModel n) (extChartAt (ComplexModel n) a).symm
    (chartPt a y)

theorem chartFrameMap_isInvertible (a y : M.Carrier)
    (hy : y ∈ (extChartAt (ComplexModel n) a).source) :
    (chartFrameMap a y).IsInvertible :=
  inverse_chart_derivative_isInvertible a (chartPt a y)
    ((extChartAt (ComplexModel n) a).map_source hy)

def invertibleContinuousEquiv {W : Type*} [AddCommGroup W] [Module ℂ W] [TopologicalSpace W]
    {W' : Type*} [AddCommGroup W'] [Module ℂ W'] [TopologicalSpace W']
    (L : W →L[ℂ] W') (hL : L.IsInvertible) : W ≃L[ℂ] W' := Classical.choose hL

theorem invertibleContinuousEquiv_apply {W : Type*} [AddCommGroup W] [Module ℂ W] [TopologicalSpace W]
    {W' : Type*} [AddCommGroup W'] [Module ℂ W'] [TopologicalSpace W']
    (L : W →L[ℂ] W') (hL : L.IsInvertible) (v : W) :
    invertibleContinuousEquiv L hL v = L v := by
  have he := congrArg (fun F : W →L[ℂ] W' => F v) (Classical.choose_spec hL)
  exact he

def chartFrameBasis (a y : M.Carrier)
    (hy : y ∈ (extChartAt (ComplexModel n) a).source) :
    Basis (Fin n) ℂ (TangentVector M y) :=
  (EuclideanSpace.basisFun (Fin n) ℂ).toBasis.map
    (invertibleContinuousEquiv (chartFrameMap a y) (chartFrameMap_isInvertible a y hy)).toLinearEquiv

theorem chartFrameBasis_apply (a y : M.Carrier)
    (hy : y ∈ (extChartAt (ComplexModel n) a).source) (i : Fin n) :
    chartFrameBasis a y hy i = chartVec a y (stdVec i) := by
  rw [chartFrameBasis, Basis.map_apply, ContinuousLinearEquiv.coe_toLinearEquiv,
    invertibleContinuousEquiv_apply]
  simp only [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply]
  rfl

def frameGram (g : HermitianField M) (a y : M.Carrier) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => (g y).toFun (chartVec a y (stdVec i)) (chartVec a y (stdVec j))

theorem frameGram_eq_hermitianGram (g : HermitianField M) (a y : M.Carrier)
    (hy : y ∈ (extChartAt (ComplexModel n) a).source) :
    frameGram g a y = hermitianGram (g y) (chartFrameBasis a y hy) := by
  ext i j
  simp only [hermitianGram, chartFrameBasis_apply, frameGram]

theorem gMat_eq_frameGram (g : HermitianField M) (y : M.Carrier) :
    gMat g y = frameGram g y y := by
  change frameGram g y (chartInv y (chartPt y y)) = frameGram g y y
  rw [chartInv_chartPt_of_mem y y (mem_chart_source _ _)]

def metricDensityRatio (g₁ g₂ : HermitianField M) (y : M.Carrier) : ℝ :=
  (gMat g₁ y).det.re / (gMat g₂ y).det.re

theorem metricDensityRatio_eq_frameGram (g₁ g₂ : HermitianField M) (a y : M.Carrier)
    (hy : y ∈ (extChartAt (ComplexModel n) a).source) :
    metricDensityRatio g₁ g₂ y = (frameGram g₁ a y).det.re / (frameGram g₂ a y).det.re := by
  unfold metricDensityRatio
  rw [gMat_eq_frameGram, gMat_eq_frameGram,
    frameGram_eq_hermitianGram _ y y (mem_extChartAt_source y),
    frameGram_eq_hermitianGram _ y y (mem_extChartAt_source y),
    frameGram_eq_hermitianGram _ a y hy, frameGram_eq_hermitianGram _ a y hy]
  exact (hermitianGram_det_ratio (g₁ y) (g₂ y)
    (chartFrameBasis a y hy) (chartFrameBasis y y (mem_extChartAt_source y)))

theorem metricDensityRatio_inChart (g₁ g₂ : HermitianField M) (a : M.Carrier)
    (z : ComplexVector n) (hz : z ∈ chartTarget a) :
    metricDensityRatio g₁ g₂ (chartInv a z) = (hMat g₁ a z).det.re / (hMat g₂ a z).det.re :=
  metricDensityRatio_eq_frameGram g₁ g₂ a (chartInv a z)
    ((extChartAt (ComplexModel n) a).map_target hz)

theorem metricDensityRatio_pos (g₁ g₂ : HermitianField M) (y : M.Carrier) :
    0 < metricDensityRatio g₁ g₂ y :=
  div_pos (Complex.pos_iff.mp (gMat_posDef g₁ y).det_pos).1
    (Complex.pos_iff.mp (gMat_posDef g₂ y).det_pos).1

theorem metricDensityRatio_eq_sqrt_det (g₁ g₂ : HermitianField M)
    (a : M.Carrier) (z : ComplexVector n) (hz : z ∈ chartTarget a) :
    metricDensityRatio g₁ g₂ (chartInv a z) =
      Real.sqrt (realMetricFn g₁ a z).det / Real.sqrt (realMetricFn g₂ a z).det := by
  rw [metricDensityRatio_inChart _ _ _ _ hz,
    realMetricFn_sqrt_det _ _ _ hz, realMetricFn_sqrt_det _ _ _ hz]
  exact (mul_div_mul_left _ _ (pow_ne_zero n (by norm_num : (2 : ℝ) ≠ 0))).symm

theorem metricDensityRatio_continuousOn (g₁ g₂ : HermitianField M)
    (hg₁ : MetricSmooth g₁) (hg₂ : MetricSmooth g₂) (a : M.Carrier) :
    ContinuousOn (metricDensityRatio g₁ g₂) (extChartAt (ComplexModel n) a).source := by
  have hden : ∀ z ∈ chartTarget a, Real.sqrt (realMetricFn g₂ a z).det ≠ 0 := by
    intro z hz
    rw [realMetricFn_sqrt_det _ _ _ hz]
    exact mul_ne_zero (pow_ne_zero n (by norm_num)) (ne_of_gt (L18Aux.hMat_det_re_pos g₂ a hz))
  have hc : ContinuousOn (fun z =>
      Real.sqrt (realMetricFn g₁ a z).det / Real.sqrt (realMetricFn g₂ a z).det)
      (chartTarget a) :=
    (L18Aux.contDiffOn_matrix_det (hg₁ a)).continuousOn.sqrt.div
      (L18Aux.contDiffOn_matrix_det (hg₂ a)).continuousOn.sqrt hden
  have hh := hc.comp (continuousOn_extChartAt (I := ComplexModel n) a)
    (fun y hy => (extChartAt (ComplexModel n) a).map_source hy)
  apply hh.congr
  intro y hy
  have he := metricDensityRatio_eq_sqrt_det g₁ g₂ a (chartPt a y)
    ((extChartAt (ComplexModel n) a).map_source hy)
  rw [chartInv_chartPt_of_mem a y (by simpa only [extChartAt_source] using hy)] at he
  exact he

theorem metricDensityRatio_continuous (g₁ g₂ : HermitianField M)
    (hg₁ : MetricSmooth g₁) (hg₂ : MetricSmooth g₂) :
    Continuous (metricDensityRatio g₁ g₂) := by
  apply continuous_of_cover_nhds (s := fun a : M.Carrier =>
    (extChartAt (ComplexModel n) a).source)
  · intro y
    exact ⟨y, (isOpen_extChartAt_source (I := ComplexModel n) y).mem_nhds (mem_extChartAt_source y)⟩
  · exact metricDensityRatio_continuousOn g₁ g₂ hg₁ hg₂

def chartInvExtension (a : M.Carrier) (z : ComplexVector n) : M.Carrier :=
  @ite _ (z ∈ chartTarget a) (Classical.propDecidable _) (chartInv a z) a

theorem chartInvExtension_measurable (a : M.Carrier) :
    Measurable (chartInvExtension a) := by
  classical
  change Measurable ((chartTarget a).piecewise (chartInv a) (fun _ => a))
  exact (continuousOn_extChartAt_symm (I := ComplexModel n) a).measurable_piecewise
    (continuousOn_const (c := a)) (isOpen_extChartAt_target (I := ComplexModel n) a).measurableSet

theorem chart_image_eq_extension_preimage (a : M.Carrier) (s : Set M.Carrier) :
    chartPt a '' (s ∩ (extChartAt (ComplexModel n) a).source) =
      chartInvExtension a ⁻¹' s ∩ chartTarget a := by
  ext z
  constructor
  · rintro ⟨y, ⟨hys, hy⟩, rfl⟩
    have hz : chartPt a y ∈ chartTarget a := (extChartAt (ComplexModel n) a).map_source hy
    refine ⟨?_, hz⟩
    simpa only [Set.mem_preimage, chartInvExtension, if_pos hz,
      chartInv_chartPt_of_mem a y (by simpa only [extChartAt_source] using hy)] using hys
  · rintro ⟨hzs, hz⟩
    refine ⟨chartInv a z, ⟨?_, (extChartAt (ComplexModel n) a).map_target hz⟩, ?_⟩
    · simpa only [Set.mem_preimage, chartInvExtension, if_pos hz] using hzs
    · exact (extChartAt (ComplexModel n) a).right_inv hz

theorem riemannianVolume_restrict_eq_map (g : HermitianField M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g μ) (a : M.Carrier) :
    μ.restrict (extChartAt (ComplexModel n) a).source =
      Measure.map (chartInvExtension a)
        (((lebesgueC n).restrict (chartTarget a)).withDensity
          (fun z => ENNReal.ofReal (Real.sqrt (realMetricFn g a z).det))) := by
  apply Measure.ext
  intro s hs
  rw [Measure.restrict_apply hs, Measure.map_apply (chartInvExtension_measurable a) hs,
    withDensity_apply _ ((chartInvExtension_measurable a) hs), Measure.restrict_restrict]
  · rw [hμ a (s ∩ (extChartAt (ComplexModel n) a).source)
      (hs.inter (isOpen_extChartAt_source (I := ComplexModel n) a).measurableSet)
      (by simpa only [extChartAt_source] using (Set.inter_subset_right :
        s ∩ (extChartAt (ComplexModel n) a).source ⊆ (extChartAt (ComplexModel n) a).source)),
      chart_image_eq_extension_preimage]
  · exact (chartInvExtension_measurable a) hs

theorem metricDensityRatio_mul_volumeDensity (g₁ g₂ : HermitianField M)
    (a : M.Carrier) (z : ComplexVector n) (hz : z ∈ chartTarget a) :
    ENNReal.ofReal (Real.sqrt (realMetricFn g₂ a z).det) *
      ENNReal.ofReal (metricDensityRatio g₁ g₂ (chartInv a z)) =
        ENNReal.ofReal (Real.sqrt (realMetricFn g₁ a z).det) := by
  rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg _), metricDensityRatio_eq_sqrt_det _ _ _ _ hz]
  congr 1
  have hd : Real.sqrt (realMetricFn g₂ a z).det ≠ 0 := by
    rw [realMetricFn_sqrt_det _ _ _ hz]
    exact mul_ne_zero (pow_ne_zero n (by norm_num)) (ne_of_gt (L18Aux.hMat_det_re_pos g₂ a hz))
  exact mul_div_cancel₀ _ hd

theorem riemannianVolume_restrict_withDensity (g₁ g₂ : HermitianField M)
    (μ₁ μ₂ : Measure M.Carrier) (hμ₁ : IsRiemannianVolume g₁ μ₁)
    (hμ₂ : IsRiemannianVolume g₂ μ₂) (hg₁ : MetricSmooth g₁) (hg₂ : MetricSmooth g₂)
    (a : M.Carrier) :
    μ₁.restrict (extChartAt (ComplexModel n) a).source =
      (μ₂.restrict (extChartAt (ComplexModel n) a).source).withDensity
        (fun y => ENNReal.ofReal (metricDensityRatio g₁ g₂ y)) := by
  have hr : Measurable (fun y => ENNReal.ofReal (metricDensityRatio g₁ g₂ y)) :=
    (ENNReal.continuous_ofReal.comp (metricDensityRatio_continuous g₁ g₂ hg₁ hg₂)).measurable
  have hd (g : HermitianField M) (hg : MetricSmooth g) :
      AEMeasurable (fun z => ENNReal.ofReal (Real.sqrt (realMetricFn g a z).det))
        ((lebesgueC n).restrict (chartTarget a)) :=
    (ENNReal.continuous_ofReal.comp_continuousOn
      (L18Aux.contDiffOn_matrix_det (hg a)).continuousOn.sqrt).aemeasurable
      (isOpen_extChartAt_target (I := ComplexModel n) a).measurableSet
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_withDensity_eq_lintegral_mul _ hr hf,
    riemannianVolume_restrict_eq_map g₁ μ₁ hμ₁ a,
    riemannianVolume_restrict_eq_map g₂ μ₂ hμ₂ a,
    lintegral_map hf (chartInvExtension_measurable a),
    lintegral_map (hr.mul hf) (chartInvExtension_measurable a),
    lintegral_withDensity_eq_lintegral_mul₀ (hd g₁ hg₁)
      (g := fun z => f (chartInvExtension a z))
      (by exact (hf.comp (chartInvExtension_measurable a)).aemeasurable),
    lintegral_withDensity_eq_lintegral_mul₀ (hd g₂ hg₂)
      (g := fun z => ((fun y => ENNReal.ofReal (metricDensityRatio g₁ g₂ y)) * f)
        (chartInvExtension a z))
      (by exact ((hr.mul hf).comp (chartInvExtension_measurable a)).aemeasurable)]
  apply setLIntegral_congr_fun (isOpen_extChartAt_target (I := ComplexModel n) a).measurableSet
  intro z hz
  have hz' : z ∈ chartTarget a := hz
  simp only [Pi.mul_apply, chartInvExtension, if_pos hz']
  rw [← mul_assoc, metricDensityRatio_mul_volumeDensity _ _ _ _ hz]

theorem riemannianVolume_withDensity (g₁ g₂ : HermitianField M)
    (μ₁ μ₂ : Measure M.Carrier) (hμ₁ : IsRiemannianVolume g₁ μ₁)
    (hμ₂ : IsRiemannianVolume g₂ μ₂) (hg₁ : MetricSmooth g₁) (hg₂ : MetricSmooth g₂) :
    μ₁ = μ₂.withDensity (fun y => ENNReal.ofReal (metricDensityRatio g₁ g₂ y)) := by
  obtain ⟨S, hSc, hS⟩ := isLindelof_univ.elim_countable_subcover
    (fun a : M.Carrier => (extChartAt (ComplexModel n) a).source)
    (fun a => isOpen_extChartAt_source a) (by
      intro y _
      exact Set.mem_iUnion.mpr ⟨y, mem_extChartAt_source y⟩)
  apply Measure.ext_of_biUnion_eq_univ hSc (Set.eq_univ_of_univ_subset hS)
  intro a _
  rw [restrict_withDensity (isOpen_extChartAt_source (I := ComplexModel n) a).measurableSet]
  exact riemannianVolume_restrict_withDensity g₁ g₂ μ₁ μ₂ hμ₁ hμ₂ hg₁ hg₂ a

theorem gMat_inv_det_re (g : HermitianField M) (y : M.Carrier) :
    (gMat g y)⁻¹.det.re = ((gMat g y).det.re)⁻¹ := by
  have hi := matrix_isHermitian_det_im (gMat g y) (gMat_posDef g y).isHermitian
  have he : (gMat g y).det = ((gMat g y).det.re : ℂ) := by
    apply Complex.ext
    · rfl
    · simpa only [Complex.ofReal_im] using hi
  rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv, he, ← Complex.ofReal_inv, Complex.ofReal_re]
  simp only [Complex.ofReal_re]

theorem metricDensityRatio_inv_det_cancel (g₁ g₂ : HermitianField M) (y : M.Carrier) :
    ENNReal.ofReal (metricDensityRatio g₁ g₂ y) * ENNReal.ofReal (gMat g₁ y)⁻¹.det.re =
      ENNReal.ofReal (gMat g₂ y)⁻¹.det.re := by
  rw [← ENNReal.ofReal_mul (metricDensityRatio_pos g₁ g₂ y).le,
    gMat_inv_det_re, gMat_inv_det_re]
  congr 1
  unfold metricDensityRatio
  have hp : (gMat g₁ y).det.re ≠ 0 := ne_of_gt (Complex.pos_iff.mp (gMat_posDef g₁ y).det_pos).1
  field_simp

theorem riemannianVolume_lintegral_inv_det (g₁ g₂ : HermitianField M)
    (μ₁ μ₂ : Measure M.Carrier) (hμ₁ : IsRiemannianVolume g₁ μ₁)
    (hμ₂ : IsRiemannianVolume g₂ μ₂) (hg₁ : MetricSmooth g₁) (hg₂ : MetricSmooth g₂)
    (F : M.Carrier → ℝ≥0∞) :
    (∫⁻ y, ENNReal.ofReal (gMat g₁ y)⁻¹.det.re * F y ∂μ₁) =
      ∫⁻ y, ENNReal.ofReal (gMat g₂ y)⁻¹.det.re * F y ∂μ₂ := by
  have hr : Measurable (fun y => ENNReal.ofReal (metricDensityRatio g₁ g₂ y)) :=
    (ENNReal.continuous_ofReal.comp (metricDensityRatio_continuous g₁ g₂ hg₁ hg₂)).measurable
  rw [riemannianVolume_withDensity g₁ g₂ μ₁ μ₂ hμ₁ hμ₂ hg₁ hg₂,
    lintegral_withDensity_eq_lintegral_mul_non_measurable μ₂
      (f := fun y => ENNReal.ofReal (metricDensityRatio g₁ g₂ y)) hr
      (Filter.Eventually.of_forall (fun y => ENNReal.ofReal_lt_top))]
  apply lintegral_congr
  intro y
  exact (mul_assoc _ _ _).symm.trans
    (congrArg (fun z => z * F y) (metricDensityRatio_inv_det_cancel g₁ g₂ y))

end MetricDensity

section TopDegreeMetricIndependence

open BundleDbar

variable {n r : ℕ} {M : ComplexManifold n}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

theorem weightedNormSq_top_metric_independent (g₁ g₂ : HermitianField M)
    (μ₁ μ₂ : Measure M.Carrier) (hμ₁ : IsRiemannianVolume g₁ μ₁)
    (hμ₂ : IsRiemannianVolume g₂ μ₂) (hg₁ : MetricSmooth g₁) (hg₂ : MetricSmooth g₂)
    (h : Metric E) (φ : M.Carrier → ℝ) (u : NQForm E 0) :
    weightedNormSq (r := r) E g₁ h μ₁ φ u = weightedNormSq (r := r) E g₂ h μ₂ φ u := by
  have ht (g : HermitianField M) (x : M.Carrier) :
      ENNReal.ofReal (BundleDbar.formNormSq (r := r) E g h u x * Real.exp (-φ x)) =
        ENNReal.ofReal (gMat g x)⁻¹.det.re *
          ENNReal.ofReal (topCoefficientNormSq (r := r) E h u x * Real.exp (-φ x)) := by
    rw [formNormSq_top_factor E, mul_assoc]
    exact ENNReal.ofReal_mul (Complex.nonneg_iff.mp (gMat_posDef g x).inv.posSemidef.det_nonneg).1
  unfold weightedNormSq
  simp_rw [ht]
  exact riemannianVolume_lintegral_inv_det g₁ g₂ μ₁ μ₂ hμ₁ hμ₂ hg₁ hg₂ _

theorem inverseCurvatureIntegral_metric_independent (g₁ g₂ : HermitianField M)
    (μ₁ μ₂ : Measure M.Carrier) (hμ₁ : IsRiemannianVolume g₁ μ₁)
    (hμ₂ : IsRiemannianVolume g₂ μ₂) (hg₁ : MetricSmooth g₁) (hg₂ : MetricSmooth g₂)
    (h : Metric E) (φ : M.Carrier → ℝ) (f : NQForm E 1) :
    inverseCurvatureIntegral (r := r) E g₁ h μ₁ φ f =
      inverseCurvatureIntegral (r := r) E g₂ h μ₂ φ f := by
  unfold inverseCurvatureIntegral
  simp_rw [inverseCurvatureNormSq_factor_of_metric E, mul_assoc]
  exact riemannianVolume_lintegral_inv_det g₁ g₂ μ₁ μ₂ hμ₁ hμ₂ hg₁ hg₂ _

theorem topDegreeMetricIndependence : LeafCandidates.TopDegreeMetricIndependence (r := r) E := by
  intro g₁ g₂ μ₁ μ₂ h φ hμ₁ hμ₂ hg₁ hg₂ _ _ _ _
  constructor
  · intro u _
    exact weightedNormSq_top_metric_independent E g₁ g₂ μ₁ μ₂ hμ₁ hμ₂ hg₁ hg₂ h φ u
  · intro f _
    exact inverseCurvatureIntegral_metric_independent E g₁ g₂ μ₁ μ₂ hμ₁ hμ₂ hg₁ hg₂ h φ f

end TopDegreeMetricIndependence

end Yau.LeafProofs

namespace Yau.LeafProofs.L14Aux

open BundleDbar

/-- The real quadratic optimization used in the variational inverse norm. -/
theorem quadratic_dual_bound {a b c : ℝ}
    (h : ∀ t : ℝ, 2 * t * b - t ^ 2 * a ≤ c) : b ^ 2 ≤ c * a := by
  have hd := discrim_le_zero (a := a) (b := -2 * b) (c := c) (fun t => by
    have ht := h t
    nlinarith)
  unfold discrim at hd
  nlinarith

/-- Complex phases, including the zero-energy case, are accounted for in
the variational characterization of the inverse quadratic form. -/
theorem complex_dual_bound {z : ℂ} {a c : ℝ} (ha : 0 ≤ a)
    (h : ∀ w : ℂ, 2 * (w * z).re - Complex.normSq w * a ≤ c) :
    Complex.normSq z ≤ c * a := by
  have hc : 0 ≤ c := by simpa using h 0
  have hs : 0 ≤ Complex.normSq z := Complex.normSq_nonneg z
  have hq : Complex.normSq z ^ 2 ≤ c * (Complex.normSq z * a) := by
    apply quadratic_dual_bound
    intro t
    have ht := h ((t : ℂ) * star z)
    have hp : (((t : ℂ) * star z) * z).re = t * Complex.normSq z := by
      simp [Complex.mul_re, Complex.mul_im, Complex.normSq_apply]
      ring
    have hn : Complex.normSq ((t : ℂ) * star z) = t ^ 2 * Complex.normSq z := by
      simp [Complex.normSq_mul, Complex.normSq_conj, Complex.normSq_ofReal, pow_two]
    rw [hp, hn] at ht
    nlinarith
  rcases eq_or_lt_of_le hs with hz | hz
  · rw [← hz]
    exact mul_nonneg hc ha
  · apply (mul_le_mul_iff_right₀ hz).mp
    nlinarith [hq]

theorem matrixCoefficientPairing_smul_right {n r : ℕ}
    (H : Matrix (Fin r) (Fin r) ℂ) (F V : Fin n → Fin r → ℂ) (c : ℂ) :
    matrixCoefficientPairing H F (c • V) = c * matrixCoefficientPairing H F V := by
  simp only [matrixCoefficientPairing, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  congr 1
  funext i
  congr 1
  funext α
  congr 1
  funext β
  ring

theorem nakanoQuadratic_smul {n r : ℕ}
    (R : Fin n → Fin n → Matrix (Fin r) (Fin r) ℂ)
    (V : Fin n → Fin r → ℂ) (c : ℂ) :
    nakanoQuadratic R (c • V) = Complex.normSq c * nakanoQuadratic R V := by
  have he : (∑ i, ∑ j, ∑ α : Fin r, ∑ β : Fin r,
      R i j α β * star ((c • V) j α) * (c • V) i β) =
      (Complex.normSq c : ℂ) *
        ∑ i, ∑ j, ∑ α : Fin r, ∑ β : Fin r,
          R i j α β * star (V j α) * V i β := by
    simp only [Pi.smul_apply, smul_eq_mul, star_mul, Finset.mul_sum,
      Complex.normSq_eq_conj_mul_self, Complex.star_def]
    congr 1
    funext i
    congr 1
    funext j
    congr 1
    funext α
    congr 1
    funext β
    ring
  unfold nakanoQuadratic
  rw [he]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

/-- The finite-dimensional variational supremum can be computed on a
countable dense family. In particular, its supremum is measurable. -/
theorem iSup_eq_denseSeq {V : Type*} [TopologicalSpace V] [TopologicalSpace.SeparableSpace V]
    [Nonempty V] (f : V → ℝ≥0∞) (hf : Continuous f) :
    (⨆ v, f v) = ⨆ k : ℕ, f (TopologicalSpace.denseSeq V k) := by
  apply le_antisymm
  · apply iSup_le
    intro v
    refine (TopologicalSpace.denseRange_denseSeq V).induction_on
      (p := fun v => f v ≤ ⨆ k : ℕ, f (TopologicalSpace.denseSeq V k))
      v (isClosed_le hf continuous_const) ?_
    intro k
    exact le_iSup (fun k : ℕ => f (TopologicalSpace.denseSeq V k)) k
  · apply iSup_le
    intro k
    exact le_iSup f (TopologicalSpace.denseSeq V k)

theorem aemeasurable_variationalSup {X V : Type*} [MeasurableSpace X]
    [TopologicalSpace V] [TopologicalSpace.SeparableSpace V] [Nonempty V] (μ : Measure X)
    (L : X → V → ℝ) (hcontinuous : ∀ x, Continuous (L x))
    (hmeasurable : ∀ v, AEMeasurable (fun x => L x v) μ) :
    AEMeasurable (fun x => ⨆ v, ENNReal.ofReal (L x v)) μ := by
  have he : (fun x => ⨆ v, ENNReal.ofReal (L x v)) =
      fun x => ⨆ k : ℕ, ENNReal.ofReal (L x (TopologicalSpace.denseSeq V k)) := by
    funext x
    exact iSup_eq_denseSeq _ (ENNReal.continuous_ofReal.comp (hcontinuous x))
  rw [he]
  apply AEMeasurable.iSup
  intro k
  exact ENNReal.continuous_ofReal.measurable.comp_aemeasurable (hmeasurable _)

theorem matrixCoefficientPairing_continuous {n r : ℕ}
    (H : Matrix (Fin r) (Fin r) ℂ) (F : Fin n → Fin r → ℂ) :
    Continuous (fun V : Fin n → Fin r → ℂ => matrixCoefficientPairing H F V) := by
  unfold matrixCoefficientPairing
  fun_prop

theorem nakanoQuadratic_continuous {n r : ℕ}
    (R : Fin n → Fin n → Matrix (Fin r) (Fin r) ℂ) :
    Continuous (nakanoQuadratic R) := by
  unfold nakanoQuadratic
  fun_prop

theorem matrixCoefficientPairing_aemeasurable {X : Type*} [MeasurableSpace X]
    {n r : ℕ} (μ : Measure X) (H : X → Matrix (Fin r) (Fin r) ℂ)
    (F : X → Fin n → Fin r → ℂ)
    (hH : ∀ α β, AEMeasurable (fun x => H x α β) μ)
    (hF : ∀ i α, AEMeasurable (fun x => F x i α) μ)
    (V : Fin n → Fin r → ℂ) :
    AEMeasurable (fun x => matrixCoefficientPairing (H x) (F x) V) μ := by
  unfold matrixCoefficientPairing
  apply Finset.aemeasurable_fun_sum
  intro i _
  apply Finset.aemeasurable_fun_sum
  intro α _
  apply Finset.aemeasurable_fun_sum
  intro β _
  exact (((continuous_star.measurable.comp_aemeasurable (hF i α)).mul (hH α β)).mul_const _)

theorem nakanoQuadratic_aemeasurable {X : Type*} [MeasurableSpace X]
    {n r : ℕ} (μ : Measure X)
    (R : X → Fin n → Fin n → Matrix (Fin r) (Fin r) ℂ)
    (hR : ∀ i j α β, AEMeasurable (fun x => R x i j α β) μ)
    (V : Fin n → Fin r → ℂ) :
    AEMeasurable (fun x => nakanoQuadratic (R x) V) μ := by
  unfold nakanoQuadratic
  apply Complex.measurable_re.comp_aemeasurable
  apply Finset.aemeasurable_fun_sum
  intro i _
  apply Finset.aemeasurable_fun_sum
  intro j _
  apply Finset.aemeasurable_fun_sum
  intro α _
  apply Finset.aemeasurable_fun_sum
  intro β _
  exact ((hR i j α β).mul_const _).mul_const _

theorem coefficientInverseSup_aemeasurable {X : Type*} [MeasurableSpace X]
    {n r : ℕ} (μ : Measure X) (H : X → Matrix (Fin r) (Fin r) ℂ)
    (F : X → Fin n → Fin r → ℂ)
    (R : X → Fin n → Fin n → Matrix (Fin r) (Fin r) ℂ)
    (hH : ∀ α β, AEMeasurable (fun x => H x α β) μ)
    (hF : ∀ i α, AEMeasurable (fun x => F x i α) μ)
    (hR : ∀ i j α β, AEMeasurable (fun x => R x i j α β) μ) :
    AEMeasurable (fun x => ⨆ V : Fin n → Fin r → ℂ,
      ENNReal.ofReal (2 * (matrixCoefficientPairing (H x) (F x) V).re -
        nakanoQuadratic (R x) V)) μ := by
  apply aemeasurable_variationalSup
  · intro x
    exact (continuous_const.mul
      (Complex.continuous_re.comp (matrixCoefficientPairing_continuous (H x) (F x)))).sub
        (nakanoQuadratic_continuous (R x))
  · intro V
    exact (aemeasurable_const.mul
      (Complex.measurable_re.comp_aemeasurable
        (matrixCoefficientPairing_aemeasurable μ H F hH hF V))).sub
          (nakanoQuadratic_aemeasurable μ R hR V)

theorem complex_young_of_normSq_le_mul {z : ℂ} {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hz : Complex.normSq z ≤ a * b) (c : ℂ) :
    2 * (c * z).re - Complex.normSq c * b ≤ a := by
  have hn : Complex.normSq (c * z) ≤ a * (Complex.normSq c * b) := by
    rw [Complex.normSq_mul]
    nlinarith [mul_nonneg (Complex.normSq_nonneg c) (sub_nonneg.mpr hz)]
  have hre := Complex.re_sq_le_normSq (c * z)
  have ham := two_mul_le_add_of_sq_le_mul ha
    (mul_nonneg (Complex.normSq_nonneg c) hb)
    (show (c * z).re ^ 2 ≤ a * (Complex.normSq c * b) by nlinarith)
  linarith

/-- A dual-curvature bound gives an integrable pairing even when the source
itself has no global unweighted L² norm. -/
theorem integrable_of_normSq_le_mul {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (p : X → ℂ) (a b : X → ℝ)
    (hp : AEStronglyMeasurable p μ) (hia : Integrable a μ) (hib : Integrable b μ)
    (ha : ∀ᵐ x ∂μ, 0 ≤ a x) (hb : ∀ᵐ x ∂μ, 0 ≤ b x)
    (hbound : ∀ᵐ x ∂μ, Complex.normSq (p x) ≤ a x * b x) : Integrable p μ := by
  apply (hia.add hib).mono' hp
  filter_upwards [ha, hb, hbound] with x hax hbx hx
  have ham := two_mul_le_add_of_sq_le_mul hax hbx
    (show ‖p x‖ ^ 2 ≤ a x * b x by rwa [← Complex.normSq_eq_norm_sq])
  change ‖p x‖ ≤ a x + b x
  nlinarith [norm_nonneg (p x)]

/-- Integrated inverse-curvature Cauchy–Schwarz, obtained by integrating
the quadratic variational inequality and optimizing its complex phase. -/
theorem integral_normSq_le_mul {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (p : X → ℂ) (a b : X → ℝ)
    (hp : AEStronglyMeasurable p μ) (hia : Integrable a μ) (hib : Integrable b μ)
    (ha : ∀ᵐ x ∂μ, 0 ≤ a x) (hb : ∀ᵐ x ∂μ, 0 ≤ b x)
    (hbound : ∀ᵐ x ∂μ, Complex.normSq (p x) ≤ a x * b x) :
    Complex.normSq (∫ x, p x ∂μ) ≤ (∫ x, a x ∂μ) * (∫ x, b x ∂μ) := by
  have hpi := integrable_of_normSq_le_mul μ p a b hp hia hib ha hb hbound
  apply complex_dual_bound (integral_nonneg_of_ae hb)
  intro c
  have hic : Integrable (fun x => (c * p x).re) μ := (hpi.const_mul c).re
  have hleft : Integrable (fun x => 2 * (c * p x).re - Complex.normSq c * b x) μ :=
    (hic.const_mul 2).sub (hib.const_mul (Complex.normSq c))
  have hi := integral_mono_ae hleft hia (show ∀ᵐ x ∂μ,
      2 * (c * p x).re - Complex.normSq c * b x ≤ a x from by
    filter_upwards [ha, hb, hbound] with x hax hbx hx
    exact complex_young_of_normSq_le_mul hax hbx hx c)
  rw [integral_sub (hic.const_mul 2) (hib.const_mul (Complex.normSq c)),
    integral_const_mul, integral_const_mul] at hi
  have hre : (∫ x, (c * p x).re ∂μ) = (c * ∫ x, p x ∂μ).re := by
    simpa only [RCLike.re_eq_complex_re, integral_const_mul] using
      integral_re (𝕜 := ℂ) (hpi.const_mul c)
  rw [hre] at hi
  exact hi

variable {n r : ℕ} {M : ComplexManifold n}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

theorem coefficientInner_smul_right (g : HermitianField M) (h : Metric E)
    (x : M.Carrier) (F V : Fin n → Fin r → ℂ) (c : ℂ) :
    coefficientInner (r := r) E g h x F (c • V) =
      c * coefficientInner (r := r) E g h x F V := by
  unfold coefficientInner
  rw [mul_left_comm c]
  congr 1
  simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  congr 1
  funext i
  congr 1
  funext j
  congr 1
  funext α
  congr 1
  funext β
  ring

theorem curvatureEnergy_smul (g : HermitianField M) (h : Metric E)
    (φ : M.Carrier → ℝ) (x : M.Carrier) (V : Fin n → Fin r → ℂ) (c : ℂ) :
    curvatureEnergy (r := r) E g h φ x (c • V) =
      Complex.normSq c * curvatureEnergy (r := r) E g h φ x V := by
  have hm : (fun i α => ∑ j, (gMat g x)⁻¹ i j * (c • V) j α) =
      c • (fun i α => ∑ j, (gMat g x)⁻¹ i j * V j α) := by
    ext i α
    simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  unfold curvatureEnergy
  rw [hm, nakanoQuadratic_smul]
  ring

theorem curvatureEnergy_nonneg (g : HermitianField M) (h : Metric E)
    (φ : M.Carrier → ℝ) (hN : WeightedNakanoNonnegative (r := r) E h φ)
    (x : M.Carrier) (V : Fin n → Fin r → ℂ) :
    0 ≤ curvatureEnergy (r := r) E g h φ x V := by
  apply mul_nonneg
  · exact (Complex.nonneg_iff.mp (gMat_posDef g x).inv.posSemidef.det_nonneg).1
  · apply hN x (chartPt x x)
    refine ⟨mem_extChartAt_target x, ?_⟩
    change chartInv x (chartPt x x) ∈ (localTriv (r := r) E x).baseSet
    rw [chartInv_chartPt_of_mem x x (mem_chart_source _ _)]
    exact FiberBundle.mem_baseSet_trivializationAt' x

/-- Every test coefficient array is bounded by the exact variational supremum. -/
theorem inverseCurvatureNormSq_test_le (g : HermitianField M) (h : Metric E)
    (φ : M.Carrier → ℝ) (f : NQForm E 1) (x : M.Carrier)
    (V : Fin n → Fin r → ℂ) :
    ENNReal.ofReal (2 * (coefficientInner (r := r) E g h x
      (fun i α => coefficients (r := r) E f x (chartPt x x) (fun _ => i) α) V).re -
      curvatureEnergy (r := r) E g h φ x V) ≤
        inverseCurvatureNormSq (r := r) E g h φ f x := by
  unfold inverseCurvatureNormSq
  exact le_iSup (fun W : Fin n → Fin r → ℂ =>
    ENNReal.ofReal (2 * (coefficientInner (r := r) E g h x
      (fun i α => coefficients (r := r) E f x (chartPt x x) (fun _ => i) α) W).re -
      curvatureEnergy (r := r) E g h φ x W)) V

/-- The squared form of Demailly's (3.1) for the frozen variational inverse,
with no strict-positivity or invertibility assumption on curvature. -/
theorem inverseCurvatureNormSq_cauchySchwarz (g : HermitianField M) (h : Metric E)
    (φ : M.Carrier → ℝ) (hN : WeightedNakanoNonnegative (r := r) E h φ)
    (f : NQForm E 1) (x : M.Carrier)
    (hfinite : inverseCurvatureNormSq (r := r) E g h φ f x < ⊤)
    (V : Fin n → Fin r → ℂ) :
    Complex.normSq (coefficientInner (r := r) E g h x
      (fun i α => coefficients (r := r) E f x (chartPt x x) (fun _ => i) α) V) ≤
      (inverseCurvatureNormSq (r := r) E g h φ f x).toReal *
        curvatureEnergy (r := r) E g h φ x V := by
  apply complex_dual_bound (curvatureEnergy_nonneg E g h φ hN x V)
  intro c
  have ht := (ENNReal.ofReal_le_iff_le_toReal hfinite.ne).mp
    (inverseCurvatureNormSq_test_le E g h φ f x (c • V))
  rw [coefficientInner_smul_right, curvatureEnergy_smul] at ht
  exact ht

/-- The variational inverse is the least constant in the pointwise inverse
curvature Cauchy–Schwarz estimate, including semipositive curvature. -/
theorem inverseCurvatureNormSq_le_iff (g : HermitianField M) (h : Metric E)
    (φ : M.Carrier → ℝ) (hN : WeightedNakanoNonnegative (r := r) E h φ)
    (f : NQForm E 1) (x : M.Carrier) {C : ℝ} (hC : 0 ≤ C) :
    inverseCurvatureNormSq (r := r) E g h φ f x ≤ ENNReal.ofReal C ↔
      ∀ V : Fin n → Fin r → ℂ,
        Complex.normSq (coefficientInner (r := r) E g h x
          (fun i α => coefficients (r := r) E f x (chartPt x x) (fun _ => i) α) V) ≤
            C * curvatureEnergy (r := r) E g h φ x V := by
  constructor
  · intro hle V
    have hfinite := lt_of_le_of_lt hle ENNReal.ofReal_lt_top
    have ht := inverseCurvatureNormSq_cauchySchwarz E g h φ hN f x hfinite V
    have hreal : (inverseCurvatureNormSq (r := r) E g h φ f x).toReal ≤ C := by
      simpa only [ENNReal.toReal_ofReal hC] using
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
    exact ht.trans (mul_le_mul_of_nonneg_right hreal
      (curvatureEnergy_nonneg E g h φ hN x V))
  · intro hbound
    apply iSup_le
    intro V
    apply ENNReal.ofReal_le_ofReal
    have ht := hbound V
    have hre := Complex.re_sq_le_normSq (coefficientInner (r := r) E g h x
      (fun i α => coefficients (r := r) E f x (chartPt x x) (fun _ => i) α) V)
    have ham := two_mul_le_add_of_sq_le_mul hC (curvatureEnergy_nonneg E g h φ hN x V)
      (show (coefficientInner (r := r) E g h x
        (fun i α => coefficients (r := r) E f x (chartPt x x) (fun _ => i) α) V).re ^ 2 ≤
          C * curvatureEnergy (r := r) E g h φ x V by nlinarith)
    linarith

theorem coefficientInner_eq_zero_of_curvatureEnergy_eq_zero
    (g : HermitianField M) (h : Metric E) (φ : M.Carrier → ℝ)
    (hN : WeightedNakanoNonnegative (r := r) E h φ) (f : NQForm E 1)
    (x : M.Carrier) (hfinite : inverseCurvatureNormSq (r := r) E g h φ f x < ⊤)
    (V : Fin n → Fin r → ℂ) (hzero : curvatureEnergy (r := r) E g h φ x V = 0) :
    coefficientInner (r := r) E g h x
      (fun i α => coefficients (r := r) E f x (chartPt x x) (fun _ => i) α) V = 0 := by
  apply Complex.normSq_eq_zero.mp
  have ht := inverseCurvatureNormSq_cauchySchwarz E g h φ hN f x hfinite V
  rw [hzero, mul_zero] at ht
  exact le_antisymm ht (Complex.normSq_nonneg _)

/-- A nonzero source pairing on a curvature null direction gives infinite
inverse norm; a singular curvature inverse is never set to zero. -/
theorem inverseCurvatureNormSq_eq_top_of_kernel_pairing
    (g : HermitianField M) (h : Metric E) (φ : M.Carrier → ℝ)
    (hN : WeightedNakanoNonnegative (r := r) E h φ) (f : NQForm E 1)
    (x : M.Carrier) (V : Fin n → Fin r → ℂ)
    (hzero : curvatureEnergy (r := r) E g h φ x V = 0)
    (hpair : coefficientInner (r := r) E g h x
      (fun i α => coefficients (r := r) E f x (chartPt x x) (fun _ => i) α) V ≠ 0) :
    inverseCurvatureNormSq (r := r) E g h φ f x = ⊤ := by
  by_contra hfinite
  exact hpair (coefficientInner_eq_zero_of_curvatureEnergy_eq_zero E g h φ hN f x
    (lt_top_iff_ne_top.mpr hfinite) V hzero)

def sourceCoefficientPairing (g : HermitianField M) (h : Metric E)
    (f : NQForm E 1) (V : M.Carrier → Fin n → Fin r → ℂ) (x : M.Carrier) : ℂ :=
  coefficientInner (r := r) E g h x
    (fun i α => coefficients (r := r) E f x (chartPt x x) (fun _ => i) α) (V x)

def weightedSourcePairing (g : HermitianField M) (h : Metric E)
    (φ : M.Carrier → ℝ) (f : NQForm E 1)
    (V : M.Carrier → Fin n → Fin r → ℂ) (x : M.Carrier) : ℂ :=
  sourceCoefficientPairing (r := r) E g h f V x * (Real.exp (-φ x) : ℂ)

def weightedCurvatureEnergy (g : HermitianField M) (h : Metric E)
    (φ : M.Carrier → ℝ) (V : M.Carrier → Fin n → Fin r → ℂ) (x : M.Carrier) : ℝ :=
  curvatureEnergy (r := r) E g h φ x (V x) * Real.exp (-φ x)

/-- The exact weighted dual estimate. Measurability and integrability of
test pairings are explicit local-chart bridge obligations, rather than
assumptions that the source has a global unweighted L² norm. -/
theorem weightedSourcePairing_estimate (g : HermitianField M) (μ : Measure M.Carrier)
    (h : Metric E) (φ : M.Carrier → ℝ)
    (hN : WeightedNakanoNonnegative (r := r) E h φ) (f : NQForm E 1)
    (V : M.Carrier → Fin n → Fin r → ℂ)
    (hA : AEMeasurable (fun x => inverseCurvatureNormSq (r := r) E g h φ f x *
      ENNReal.ofReal (Real.exp (-φ x))) μ)
    (hP : AEStronglyMeasurable (weightedSourcePairing (r := r) E g h φ f V) μ)
    (hQ : Integrable (weightedCurvatureEnergy (r := r) E g h φ V) μ)
    (hfinite : inverseCurvatureIntegral (r := r) E g h μ φ f < ⊤) :
    Integrable (weightedSourcePairing (r := r) E g h φ f V) μ ∧
      Complex.normSq (∫ x, weightedSourcePairing (r := r) E g h φ f V x ∂μ) ≤
        (inverseCurvatureIntegral (r := r) E g h μ φ f).toReal *
          ∫ x, weightedCurvatureEnergy (r := r) E g h φ V x ∂μ := by
  let A : M.Carrier → ℝ≥0∞ := fun x => inverseCurvatureNormSq (r := r) E g h φ f x *
    ENNReal.ofReal (Real.exp (-φ x))
  have hAfinite : ∫⁻ x, A x ∂μ < ⊤ := hfinite
  have hAE : ∀ᵐ x ∂μ, A x < ⊤ := ae_lt_top' hA hAfinite.ne
  have hia : Integrable (fun x => (A x).toReal) μ :=
    integrable_toReal_of_lintegral_ne_top hA hAfinite.ne
  have ha : ∀ᵐ x ∂μ, 0 ≤ (A x).toReal := Filter.Eventually.of_forall fun _ =>
    ENNReal.toReal_nonneg
  have hb : ∀ᵐ x ∂μ, 0 ≤ weightedCurvatureEnergy (r := r) E g h φ V x :=
    Filter.Eventually.of_forall fun x => mul_nonneg
      (curvatureEnergy_nonneg E g h φ hN x (V x)) (Real.exp_pos _).le
  have hbound : ∀ᵐ x ∂μ,
      Complex.normSq (weightedSourcePairing (r := r) E g h φ f V x) ≤
        (A x).toReal * weightedCurvatureEnergy (r := r) E g h φ V x := by
    filter_upwards [hAE] with x hx
    have hifinite : inverseCurvatureNormSq (r := r) E g h φ f x < ⊤ := by
      apply lt_top_iff_ne_top.mpr
      intro hi
      have hw : ENNReal.ofReal (Real.exp (-φ x)) ≠ 0 :=
        ne_of_gt (ENNReal.ofReal_pos.mpr (Real.exp_pos _))
      change inverseCurvatureNormSq (r := r) E g h φ f x *
        ENNReal.ofReal (Real.exp (-φ x)) < ⊤ at hx
      rw [hi, ENNReal.top_mul hw] at hx
      exact lt_irrefl _ hx
    have hp := inverseCurvatureNormSq_cauchySchwarz E g h φ hN f x hifinite (V x)
    unfold weightedSourcePairing sourceCoefficientPairing weightedCurvatureEnergy
    rw [Complex.normSq_mul, Complex.normSq_ofReal]
    change Complex.normSq (coefficientInner (r := r) E g h x
      (fun i α => coefficients (r := r) E f x (chartPt x x) (fun _ => i) α) (V x)) *
        (Real.exp (-φ x) * Real.exp (-φ x)) ≤
          (inverseCurvatureNormSq (r := r) E g h φ f x *
            ENNReal.ofReal (Real.exp (-φ x))).toReal *
              (curvatureEnergy (r := r) E g h φ x (V x) * Real.exp (-φ x))
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le]
    nlinarith [mul_nonneg (sub_nonneg.mpr hp) (sq_nonneg (Real.exp (-φ x)))]
  refine ⟨integrable_of_normSq_le_mul μ _ _ _ hP hia hQ ha hb hbound, ?_⟩
  have ht := integral_normSq_le_mul μ _ _ _ hP hia hQ ha hb hbound
  rw [integral_toReal hA hAE] at ht
  exact ht

theorem localDomain_isOpen (a : M.Carrier) :
    IsOpen (localDomain (r := r) E a) := by
  exact (continuousOn_extChartAt_symm (I := ComplexModel n) a).isOpen_inter_preimage
    (isOpen_extChartAt_target a) (localTriv (r := r) E a).open_baseSet

theorem metricMatrix_posDef (h : Metric E) (a : M.Carrier) (z : ComplexVector n)
    (hz : z ∈ localDomain (r := r) E a) :
    (BundleDbar.metricMatrix (r := r) E h a z).PosDef := by
  let b : Basis (Fin r) ℂ (E (chartInv a z)) :=
    (EuclideanSpace.basisFun (Fin r) ℂ).toBasis.map
      ((localTriv (r := r) E a).continuousLinearEquivAt ℂ (chartInv a z) hz.2).symm.toLinearEquiv
  have hb (i : Fin r) : b i =
      (localTriv (r := r) E a).symmL ℂ (chartInv a z) (stdVec i) := by
    simp only [b, Basis.map_apply, OrthonormalBasis.coe_toBasis,
      EuclideanSpace.basisFun_apply, ContinuousLinearEquiv.coe_toLinearEquiv]
    exact congrFun ((localTriv (r := r) E a).symm_continuousLinearEquivAt_eq hz.2) _
  have he : BundleDbar.metricMatrix (r := r) E h a z =
      hermitianGram (h (chartInv a z)) b := by
    ext i j
    simp only [BundleDbar.metricMatrix, hermitianGram, hb]
  rw [he]
  exact hermitianGram_posDef _ _

theorem wirt_contDiffOn {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    {s : Set X} (hs : IsOpen s) (f : X → ℂ) (hf : ContDiffOn ℝ ∞ f s) (v : X) :
    ContDiffOn ℝ ∞ (fun z => wirt f z v) s := by
  have hd : ContDiffOn ℝ ∞ (fderiv ℝ f) s := hf.fderiv_of_isOpen hs (by simp)
  unfold wirt
  exact contDiffOn_const.mul ((hd.clm_apply contDiffOn_const).sub
    (contDiffOn_const.mul (hd.clm_apply contDiffOn_const)))

theorem wirtBar_contDiffOn {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    {s : Set X} (hs : IsOpen s) (f : X → ℂ) (hf : ContDiffOn ℝ ∞ f s) (v : X) :
    ContDiffOn ℝ ∞ (fun z => wirtBar f z v) s := by
  have hd : ContDiffOn ℝ ∞ (fderiv ℝ f) s := hf.fderiv_of_isOpen hs (by simp)
  unfold wirtBar
  exact contDiffOn_const.mul ((hd.clm_apply contDiffOn_const).add
    (contDiffOn_const.mul (hd.clm_apply contDiffOn_const)))

theorem chernConnectionMatrix_contDiffOn {s : Set (ComplexVector n)} (hs : IsOpen s)
    (H : ComplexVector n → Matrix (Fin r) (Fin r) ℂ)
    (hH : ∀ α β, ContDiffOn ℝ ∞ (fun z => H z α β) s)
    (hdet : ∀ z ∈ s, (H z).det ≠ 0) (i : Fin n) (α β : Fin r) :
    ContDiffOn ℝ ∞ (fun z => chernConnectionMatrix H z i α β) s := by
  simp only [chernConnectionMatrix, Matrix.mul_apply, Matrix.of_apply]
  apply ContDiffOn.sum
  intro γ _
  exact (L18Aux.contDiffOn_matrix_inv hH hdet α γ).mul
    (wirt_contDiffOn hs _ (hH γ β) (stdVec i))

theorem curvatureMatrix_contDiffOn {s : Set (ComplexVector n)} (hs : IsOpen s)
    (H : ComplexVector n → Matrix (Fin r) (Fin r) ℂ)
    (hH : ∀ α β, ContDiffOn ℝ ∞ (fun z => H z α β) s)
    (hdet : ∀ z ∈ s, (H z).det ≠ 0) (i j : Fin n) (α β : Fin r) :
    ContDiffOn ℝ ∞ (fun z => curvatureMatrix H z i j α β) s := by
  simp only [curvatureMatrix, Matrix.neg_apply, Matrix.mul_apply, Matrix.of_apply]
  apply ContDiffOn.neg
  apply ContDiffOn.sum
  intro γ _
  exact (hH α γ).mul (wirtBar_contDiffOn hs _
    (chernConnectionMatrix_contDiffOn hs H hH hdet i γ β) (stdVec j))

theorem curvature_contDiffOn (h : Metric E)
    (hh : BundleDbar.SmoothMetric (r := r) E h) (a : M.Carrier)
    (i j : Fin n) (α β : Fin r) :
    ContDiffOn ℝ ∞ (fun z => curvature (r := r) E h a z i j α β)
      (localDomain (r := r) E a) := by
  apply curvatureMatrix_contDiffOn (localDomain_isOpen E a) _ (hh a)
  intro z hz
  exact ((metricMatrix_posDef E h a z hz).isUnit.map Matrix.detMonoidHom).ne_zero

theorem leviC_contDiffOn (φ : M.Carrier → ℝ) (hφ : SmoothFn φ)
    (a : M.Carrier) (i j : Fin n) :
    ContDiffOn ℝ ∞ (fun z => leviC (inChart a φ) z i j) (chartTarget a) := by
  have hf : ContDiffOn ℝ ∞ (fun z => Complex.ofReal (inChart a φ z)) (chartTarget a) :=
    (hφ a).continuousLinearMap_comp Complex.ofRealCLM
  exact wirt_contDiffOn (isOpen_extChartAt_target a) _
    (wirtBar_contDiffOn (isOpen_extChartAt_target a) _ hf (stdVec i)) (stdVec j)

theorem weightedCurvature_contDiffOn (h : Metric E)
    (hh : BundleDbar.SmoothMetric (r := r) E h)
    (φ : M.Carrier → ℝ) (hφ : SmoothFn φ) (a : M.Carrier)
    (i j : Fin n) (α β : Fin r) :
    ContDiffOn ℝ ∞ (fun z => weightedCurvature (r := r) E h φ a z i j α β)
      (localDomain (r := r) E a) := by
  exact (curvature_contDiffOn E h hh a i j α β).add
    (((leviC_contDiffOn φ hφ a j i).mono Set.inter_subset_left).mul (hh a α β))

def chartInverseCurvatureCoefficientSup (h : Metric E) (φ : M.Carrier → ℝ)
    (f : NQForm E 1) (a : M.Carrier) (z : ComplexVector n) : ℝ≥0∞ :=
  ⨆ V : Fin n → Fin r → ℂ, ENNReal.ofReal
    (2 * (matrixCoefficientPairing (BundleDbar.metricMatrix (r := r) E h a z)
      (fun i α => coefficients (r := r) E f a z (fun _ => i) α) V).re -
        nakanoQuadratic (weightedCurvature (r := r) E h φ a z) V)

theorem chartInverseCurvatureCoefficientSup_center (h : Metric E)
    (φ : M.Carrier → ℝ) (f : NQForm E 1) (x : M.Carrier) :
    chartInverseCurvatureCoefficientSup (r := r) E h φ f x (chartPt x x) =
      inverseCurvatureCoefficientSup (r := r) E h φ f x := rfl

/-- Local-L² source coefficients and the original smooth metric/weight
hypotheses suffice for measurability of the actual chart inverse supremum. -/
theorem chartInverseCurvatureCoefficientSup_aemeasurable
    (h : Metric E) (hh : BundleDbar.SmoothMetric (r := r) E h)
    (φ : M.Carrier → ℝ) (hφ : SmoothFn φ) (f : NQForm E 1)
    (hf : LocallyL2 (r := r) E f) (a : M.Carrier) :
    AEMeasurable (chartInverseCurvatureCoefficientSup (r := r) E h φ f a)
      ((lebesgueC n).restrict (localDomain (r := r) E a)) := by
  apply coefficientInverseSup_aemeasurable
  · intro α β
    exact ((hh a α β).continuousOn.aestronglyMeasurable
      (localDomain_isOpen E a).measurableSet).aemeasurable
  · intro i α
    exact (hf a (fun _ => i) α).1.aemeasurable
  · intro i j α β
    exact ((weightedCurvature_contDiffOn E h hh φ hφ a i j α β).continuousOn.aestronglyMeasurable
      (localDomain_isOpen E a).measurableSet).aemeasurable

theorem lintegral_norm_sq_lt_top_of_memLp {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {f : X → ℂ} (hf : MemLp f 2 μ) :
    (∫⁻ x, ENNReal.ofReal (‖f x‖ ^ 2) ∂μ) < ⊤ := by
  exact (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun x =>
    sq_nonneg ‖f x‖)).mp
      ((memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf).2

theorem locallyL2_coefficients_memLp {q : ℕ} (u : NQForm E q)
    (hu : LocallyL2 (r := r) E u) (a : M.Carrier)
    (I : Fin q → Fin n) (α : Fin r) (K : Set (ComplexVector n))
    (hK : IsCompact K) (hsub : K ⊆ localDomain (r := r) E a) :
    MemLp (fun z => coefficients (r := r) E u a z I α) 2 ((lebesgueC n).restrict K) := by
  have hm := (hu a I α).1.mono_measure (Measure.restrict_mono hsub le_rfl)
  apply (memLp_two_iff_integrable_sq_norm hm).mpr
  refine ⟨(hm.norm.aemeasurable.pow_const 2).aestronglyMeasurable, ?_⟩
  exact (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun z =>
    sq_nonneg ‖coefficients (r := r) E u a z I α‖)).mpr ((hu a I α).2 K hK hsub)

def multiplyForm {q : ℕ} (η : M.Carrier → ℂ) (u : NQForm E q) : NQForm E q := fun x =>
  ⟨η x • (u x).1, by
    intro v i c
    change η x • (u x).1 (Function.update v i (c • v i)) =
      star c • (η x • (u x).1 v)
    rw [(u x).2 v i c, smul_smul, smul_smul, mul_comm (η x)]⟩

theorem coefficients_multiplyForm {q : ℕ} (η : M.Carrier → ℂ)
    (u : NQForm E q) (a : M.Carrier) (z : ComplexVector n)
    (I : Fin q → Fin n) (α : Fin r) :
    coefficients (r := r) E (multiplyForm E η u) a z I α =
      η (chartInv a z) * coefficients (r := r) E u a z I α := by
  simp only [coefficients, multiplyForm, AlternatingMap.smul_apply, map_smul,
    PiLp.smul_apply, smul_eq_mul]

/-- Continuous scalar cutoffs preserve the original local-L² condition.
The compact coefficient norms are genuine Bochner `MemLp` norms. -/
theorem locallyL2_multiplyForm {q : ℕ} (η : M.Carrier → ℂ)
    (hη : ∀ a, ContinuousOn (inChart a η) (localDomain (r := r) E a))
    (u : NQForm E q) (hu : LocallyL2 (r := r) E u) :
    LocallyL2 (r := r) E (multiplyForm E η u) := by
  intro a I α
  have hmη : AEStronglyMeasurable (inChart a η)
      ((lebesgueC n).restrict (localDomain (r := r) E a)) :=
    (hη a).aestronglyMeasurable (localDomain_isOpen E a).measurableSet
  refine ⟨?_, ?_⟩
  · simp only [coefficients_multiplyForm]
    exact hmη.mul (hu a I α).1
  · intro K hK hsub
    have hmηK := hmη.mono_measure (Measure.restrict_mono hsub le_rfl)
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn ((hη a).mono hsub)
    have hηLp : MemLp (inChart a η) ⊤ ((lebesgueC n).restrict K) :=
      memLp_top_of_bound hmηK C ((ae_restrict_mem hK.measurableSet).mono fun z hz => hC z hz)
    have huLp := locallyL2_coefficients_memLp E u hu a I α K hK hsub
    have hprod : MemLp (fun z => inChart a η z * coefficients (r := r) E u a z I α)
        2 ((lebesgueC n).restrict K) := hηLp.mul huLp
    simpa only [coefficients_multiplyForm, inChart] using lintegral_norm_sq_lt_top_of_memLp hprod

theorem topCoefficientNormSq_nonneg (h : Metric E) (u : NQForm E 0) (x : M.Carrier) :
    0 ≤ topCoefficientNormSq (r := r) E h u x := by
  have hx : chartPt x x ∈ localDomain (r := r) E x := by
    refine ⟨mem_extChartAt_target x, ?_⟩
    change chartInv x (chartPt x x) ∈ (localTriv (r := r) E x).baseSet
    rw [chartInv_chartPt_of_mem x x (mem_chart_source _ _)]
    exact FiberBundle.mem_baseSet_trivializationAt' x
  have hn := (metricMatrix_posDef E h x (chartPt x x) hx).posSemidef.dotProduct_mulVec_nonneg
    (fun α => coefficients (r := r) E u x (chartPt x x) Fin.elim0 α)
  unfold topCoefficientNormSq
  simpa only [dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum, mul_assoc] using
    (Complex.nonneg_iff.mp hn).1

theorem formNormSq_top_nonneg (g : HermitianField M) (h : Metric E)
    (u : NQForm E 0) (x : M.Carrier) :
    0 ≤ BundleDbar.formNormSq (r := r) E g h u x := by
  rw [formNormSq_top_factor]
  exact mul_nonneg (Complex.nonneg_iff.mp (gMat_posDef g x).inv.posSemidef.det_nonneg).1
    (topCoefficientNormSq_nonneg E h u x)

section TopFormFrameAlgebra

variable {V W ι κ : Type*} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W] [Fintype ι] [DecidableEq ι]
theorem alternating_apply_basis_change (d : Basis κ ℂ W) (b c : Basis ι ℂ V)
    (A : V [⋀^ι]→ₗ[ℂ] W) : A c = (b.toMatrix c).det • A b := by
  apply d.ext_elem
  intro α
  have ht := congrArg (fun f : V [⋀^ι]→ₗ[ℂ] ℂ => f c)
    (((d.coord α).compAlternatingMap A).eq_smul_basis_det b)
  simpa only [LinearMap.compAlternatingMap_apply, AlternatingMap.smul_apply,
    Basis.det_apply, Basis.coord_apply, map_smul, Finsupp.smul_apply,
    smul_eq_mul, mul_comm] using ht

theorem alternating_hermitian_ratio_basis_independent
    (d : Basis κ ℂ W) (hV : Yau.HermitianInnerProduct V) (hW : Yau.HermitianInnerProduct W)
    (b c : Basis ι ℂ V) (A B : V [⋀^ι]→ₗ[ℂ] W) :
    (hW.toFun (A c) (B c)).re / (hermitianGram hV c).det.re =
      (hW.toFun (A b) (B b)).re / (hermitianGram hV b).det.re := by
  rw [alternating_apply_basis_change d b c A, alternating_apply_basis_change d b c B,
    hW.map_smul_left, hW.map_smul_right]
  have he (z w : ℂ) : (star z * (w * z)).re = Complex.normSq z * w.re := by
    simp only [Complex.mul_re, Complex.mul_im, Complex.star_def,
      Complex.conj_re, Complex.conj_im, Complex.normSq_apply]
    ring
  rw [he, hermitianGram_det_changeBasis_re hV b c]
  exact mul_div_mul_left _ _ (by
    apply mt Complex.normSq_eq_zero.mp
    exact (b.isUnit_det c).ne_zero)

end TopFormFrameAlgebra

def bundleFrameBasis (a x : M.Carrier) (hx : x ∈ (localTriv (r := r) E a).baseSet) :
    Basis (Fin r) ℂ (E x) :=
  (EuclideanSpace.basisFun (Fin r) ℂ).toBasis.map
    ((localTriv (r := r) E a).continuousLinearEquivAt ℂ x hx).symm.toLinearEquiv

theorem bundleFrameBasis_apply (a x : M.Carrier)
    (hx : x ∈ (localTriv (r := r) E a).baseSet) (i : Fin r) :
    bundleFrameBasis (r := r) E a x hx i =
      (localTriv (r := r) E a).symmL ℂ x (stdVec i) := by
  simp only [bundleFrameBasis, Basis.map_apply, OrthonormalBasis.coe_toBasis,
    EuclideanSpace.basisFun_apply, ContinuousLinearEquiv.coe_toLinearEquiv]
  exact congrFun ((localTriv (r := r) E a).symm_continuousLinearEquivAt_eq hx) _

theorem bundleFrameBasis_repr (a x : M.Carrier)
    (hx : x ∈ (localTriv (r := r) E a).baseSet) (v : E x) (i : Fin r) :
    (bundleFrameBasis (r := r) E a x hx).repr v i =
      (localTriv (r := r) E a).continuousLinearMapAt ℂ x v i := by
  simp only [bundleFrameBasis, Basis.map_repr, LinearEquiv.symm_symm,
    LinearEquiv.trans_apply, OrthonormalBasis.coe_toBasis_repr_apply,
    ContinuousLinearEquiv.coe_toLinearEquiv, EuclideanSpace.basisFun_repr]
  change ((localTriv (r := r) E a).continuousLinearEquivAt ℂ x hx v) i = _
  exact congrArg (fun f : E x → ComplexVector r => f v i)
    ((localTriv (r := r) E a).coe_continuousLinearEquivAt_eq (R := ℂ) hx)

theorem metricMatrix_pairing (h : Metric E) (a : M.Carrier) (z : ComplexVector n)
    (hz : z ∈ localDomain (r := r) E a) (v w : E (chartInv a z)) :
    (∑ α, ∑ β,
      star ((localTriv (r := r) E a).continuousLinearMapAt ℂ (chartInv a z) v α) *
        BundleDbar.metricMatrix (r := r) E h a z α β *
          (localTriv (r := r) E a).continuousLinearMapAt ℂ (chartInv a z) w β) =
      (h (chartInv a z)).toFun v w := by
  let b := bundleFrameBasis (r := r) E a (chartInv a z) hz.2
  have he : BundleDbar.metricMatrix (r := r) E h a z = hermitianGram (h (chartInv a z)) b := by
    ext i j
    simp only [BundleDbar.metricMatrix, hermitianGram, b, bundleFrameBasis_apply]
  rw [he]
  simpa only [b, bundleFrameBasis_repr] using hermitian_coordinates (h (chartInv a z)) b v w

def topFormValue (u : NQForm E 0) (a x : M.Carrier) : E x :=
  (u x).1 Fin.elim0 (fun k => chartVec a x (stdVec k))

theorem coefficients_topFormValue (u : NQForm E 0) (a : M.Carrier) (z : ComplexVector n)
    (α : Fin r) :
    coefficients (r := r) E u a z Fin.elim0 α =
      (localTriv (r := r) E a).continuousLinearMapAt ℂ (chartInv a z)
        (topFormValue E u a (chartInv a z)) α := by
  unfold coefficients topFormValue
  have hi : (fun k : Fin 0 => chartVec a (chartInv a z) (stdVec (Fin.elim0 k))) =
      Fin.elim0 := Subsingleton.elim _ _
  rw [hi]

theorem topCoefficientNormSq_eq_value (h : Metric E) (u : NQForm E 0) (x : M.Carrier) :
    topCoefficientNormSq (r := r) E h u x =
      ((h x).toFun (topFormValue E u x x) (topFormValue E u x x)).re := by
  have hx : chartPt x x ∈ localDomain (r := r) E x := by
    refine ⟨mem_extChartAt_target x, ?_⟩
    change chartInv x (chartPt x x) ∈ (localTriv (r := r) E x).baseSet
    rw [chartInv_chartPt_of_mem x x (mem_chart_source _ _)]
    exact FiberBundle.mem_baseSet_trivializationAt' x
  unfold topCoefficientNormSq
  simp_rw [coefficients_topFormValue]
  rw [metricMatrix_pairing E h x (chartPt x x) hx,
    chartInv_chartPt_of_mem x x (mem_chart_source _ _)]

theorem formNormSq_top_in_fixed_chart (g : HermitianField M) (h : Metric E)
    (u : NQForm E 0) (a x : M.Carrier)
    (hx : x ∈ (extChartAt (ComplexModel n) a).source) :
    BundleDbar.formNormSq (r := r) E g h u x =
      ((h x).toFun (topFormValue E u a x) (topFormValue E u a x)).re /
        (frameGram g a x).det.re := by
  have hv (b : M.Carrier) (hb : x ∈ (extChartAt (ComplexModel n) b).source) :
      (u x).1 Fin.elim0 (chartFrameBasis b x hb) = topFormValue E u b x := by
    unfold topFormValue
    congr 1
    funext i
    exact chartFrameBasis_apply b x hb i
  rw [formNormSq_top_factor, topCoefficientNormSq_eq_value,
    gMat_inv_det_re, gMat_eq_frameGram,
    frameGram_eq_hermitianGram g x x (mem_extChartAt_source x)]
  have ht := alternating_hermitian_ratio_basis_independent
    (bundleFrameBasis (r := r) E x x (FiberBundle.mem_baseSet_trivializationAt' x))
    (g x) (h x) (chartFrameBasis a x hx) (chartFrameBasis x x (mem_extChartAt_source x))
    ((u x).1 Fin.elim0) ((u x).1 Fin.elim0)
  rw [hv a hx, hv x (mem_extChartAt_source x),
    ← frameGram_eq_hermitianGram g a x hx] at ht
  simpa only [div_eq_mul_inv, mul_comm] using ht

theorem formNormSq_top_inChart (g : HermitianField M) (h : Metric E)
    (u : NQForm E 0) (a : M.Carrier) (z : ComplexVector n)
    (hz : z ∈ localDomain (r := r) E a) :
    BundleDbar.formNormSq (r := r) E g h u (chartInv a z) =
      ((hMat g a z).det.re)⁻¹ *
        (∑ α, ∑ β, star (coefficients (r := r) E u a z Fin.elim0 α) *
          BundleDbar.metricMatrix (r := r) E h a z α β *
            coefficients (r := r) E u a z Fin.elim0 β).re := by
  rw [formNormSq_top_in_fixed_chart E g h u a (chartInv a z)
    ((extChartAt (ComplexModel n) a).map_target hz.1)]
  have hn : (∑ α, ∑ β, star (coefficients (r := r) E u a z Fin.elim0 α) *
      BundleDbar.metricMatrix (r := r) E h a z α β *
        coefficients (r := r) E u a z Fin.elim0 β).re =
      ((h (chartInv a z)).toFun (topFormValue E u a (chartInv a z))
        (topFormValue E u a (chartInv a z))).re := by
    simp_rw [coefficients_topFormValue]
    exact congrArg Complex.re (metricMatrix_pairing E h a z hz _ _)
  rw [hn]
  change _ / (hMat g a z).det.re = _
  rw [div_eq_mul_inv, mul_comm]

theorem formNormSq_top_inChart_aemeasurable (g : Yau.SmoothMetric M)
    (h : Metric E) (hh : BundleDbar.SmoothMetric (r := r) E h)
    (u : NQForm E 0) (hu : LocallyL2 (r := r) E u) (a : M.Carrier) :
    AEMeasurable (fun z => BundleDbar.formNormSq (r := r) E g.form h u (chartInv a z))
      ((lebesgueC n).restrict (localDomain (r := r) E a)) := by
  have hd : ContinuousOn (fun z => (hMat g.form a z).det.re) (chartTarget a) :=
    Complex.continuous_re.comp_continuousOn
      (L18Aux.contDiffOn_matrix_det (L18Aux.hMat_contDiffOn g a)).continuousOn
  have hdi := (hd.inv₀ fun z hz => ne_of_gt (L18Aux.hMat_det_re_pos g.form a hz)).mono
    (show localDomain (r := r) E a ⊆ chartTarget a from Set.inter_subset_left)
  have hdm : AEMeasurable (fun z => ((hMat g.form a z).det.re)⁻¹)
      ((lebesgueC n).restrict (localDomain (r := r) E a)) :=
    (hdi.aestronglyMeasurable (L14Aux.localDomain_isOpen E a).measurableSet).aemeasurable
  have hnm : AEMeasurable (fun z =>
      (∑ α, ∑ β, star (coefficients (r := r) E u a z Fin.elim0 α) *
        BundleDbar.metricMatrix (r := r) E h a z α β *
          coefficients (r := r) E u a z Fin.elim0 β).re)
      ((lebesgueC n).restrict (localDomain (r := r) E a)) := by
    apply Complex.measurable_re.comp_aemeasurable
    apply Finset.aemeasurable_fun_sum
    intro α _
    apply Finset.aemeasurable_fun_sum
    intro β _
    have hα := (hu a Fin.elim0 α).1.aemeasurable
    have hβ := (hu a Fin.elim0 β).1.aemeasurable
    have hH := ((hh a α β).continuousOn.aestronglyMeasurable
      (L14Aux.localDomain_isOpen E a).measurableSet (μ := lebesgueC n)).aemeasurable
    exact ((continuous_star.measurable.comp_aemeasurable hα).mul hH).mul hβ
  have he : (fun z => BundleDbar.formNormSq (r := r) E g.form h u (chartInv a z)) =ᵐ[
      (lebesgueC n).restrict (localDomain (r := r) E a)]
      fun z => ((hMat g.form a z).det.re)⁻¹ *
        (∑ α, ∑ β, star (coefficients (r := r) E u a z Fin.elim0 α) *
          BundleDbar.metricMatrix (r := r) E h a z α β *
            coefficients (r := r) E u a z Fin.elim0 β).re :=
    (MeasureTheory.ae_restrict_mem (L14Aux.localDomain_isOpen E a).measurableSet).mono
      fun z hz => formNormSq_top_inChart E g.form h u a z hz
  exact (hdm.mul hnm).congr he.symm

def chartPtExtension (a : M.Carrier) (x : M.Carrier) : ComplexVector n :=
  @ite _ (x ∈ (extChartAt (ComplexModel n) a).source) (Classical.propDecidable _) (chartPt a x) 0

theorem chartPtExtension_measurable (a : M.Carrier) : Measurable (chartPtExtension a) := by
  classical
  change Measurable (((extChartAt (ComplexModel n) a).source).piecewise (chartPt a) (fun _ => 0))
  exact (continuousOn_extChartAt (I := ComplexModel n) a).measurable_piecewise
    (continuousOn_const (c := (0 : ComplexVector n))) (isOpen_extChartAt_source a).measurableSet

def bundleChartSource (a : M.Carrier) : Set M.Carrier :=
  (extChartAt (ComplexModel n) a).source ∩ (localTriv (r := r) E a).baseSet

theorem bundleChartSource_isOpen (a : M.Carrier) : IsOpen (bundleChartSource (r := r) E a) :=
  (isOpen_extChartAt_source a).inter (localTriv (r := r) E a).open_baseSet

theorem chartPt_image_bundleChartSource (a : M.Carrier) (s : Set (ComplexVector n)) :
    chartPt a '' (chartPtExtension a ⁻¹' s ∩ bundleChartSource (r := r) E a) =
      s ∩ localDomain (r := r) E a := by
  ext z
  constructor
  · rintro ⟨x, ⟨hxs, hx, hxb⟩, rfl⟩
    have hz := (extChartAt (ComplexModel n) a).map_source hx
    refine ⟨?_, hz, ?_⟩
    · simpa only [Set.mem_preimage, chartPtExtension, if_pos hx] using hxs
    · change chartInv a (chartPt a x) ∈ (localTriv (r := r) E a).baseSet
      rwa [chartInv_chartPt_of_mem a x (by simpa only [extChartAt_source] using hx)]
  · rintro ⟨hzs, hzt, hzb⟩
    have hx : chartInv a z ∈ (extChartAt (ComplexModel n) a).source :=
      (extChartAt (ComplexModel n) a).map_target hzt
    refine ⟨chartInv a z, ⟨?_, hx, hzb⟩, ?_⟩
    · change chartPtExtension a (chartInv a z) ∈ s
      rw [chartPtExtension, if_pos hx]
      have hzid : chartPt a (chartInv a z) = z := (extChartAt (ComplexModel n) a).right_inv hzt
      rw [hzid]
      exact hzs
    · exact (extChartAt (ComplexModel n) a).right_inv hzt

theorem map_chartPtExtension_volume (g : HermitianField M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g μ) (a : M.Carrier) :
    (μ.restrict (bundleChartSource (r := r) E a)).map (chartPtExtension a) =
      ((lebesgueC n).restrict (localDomain (r := r) E a)).withDensity
        (fun z => ENNReal.ofReal (Real.sqrt (realMetricFn g a z).det)) := by
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply (chartPtExtension_measurable a) hs,
    Measure.restrict_apply ((chartPtExtension_measurable a) hs), withDensity_apply _ hs,
    Measure.restrict_restrict hs]
  rw [hμ a _ (((chartPtExtension_measurable a) hs).inter (bundleChartSource_isOpen (r := r) E a).measurableSet)
    (by
      intro x hx
      simpa only [extChartAt_source] using hx.2.1), chartPt_image_bundleChartSource]

theorem chartPtExtension_quasiMeasurePreserving (g : HermitianField M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g μ) (a : M.Carrier) :
    QuasiMeasurePreserving (chartPtExtension a) (μ.restrict (bundleChartSource (r := r) E a))
      ((lebesgueC n).restrict (localDomain (r := r) E a)) := by
  refine ⟨chartPtExtension_measurable a, ?_⟩
  rw [map_chartPtExtension_volume (r := r) E g μ hμ a]
  exact withDensity_absolutelyContinuous _ _

theorem aemeasurable_on_bundleChartSource (g : HermitianField M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g μ) (a : M.Carrier) (F : M.Carrier → ℝ)
    (hF : AEMeasurable (fun z => F (chartInv a z))
      ((lebesgueC n).restrict (localDomain (r := r) E a))) :
    AEMeasurable F (μ.restrict (bundleChartSource (r := r) E a)) := by
  have ht := hF.comp_quasiMeasurePreserving (chartPtExtension_quasiMeasurePreserving (r := r) E g μ hμ a)
  apply ht.congr
  filter_upwards [ae_restrict_mem (bundleChartSource_isOpen (r := r) E a).measurableSet] with x hx
  change F (chartInv a (chartPtExtension a x)) = F x
  rw [chartPtExtension, if_pos hx.1,
    chartInv_chartPt_of_mem a x (by simpa only [extChartAt_source] using hx.1)]

theorem formNormSq_top_aemeasurable (g : Yau.SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (h : Metric E)
    (hh : BundleDbar.SmoothMetric (r := r) E h) (u : NQForm E 0)
    (hu : LocallyL2 (r := r) E u) :
    AEMeasurable (BundleDbar.formNormSq (r := r) E g.form h u) μ := by
  obtain ⟨v, hv⟩ := isLindelof_univ.indexed_countable_subcover (bundleChartSource (r := r) E)
    (bundleChartSource_isOpen (r := r) E) (by
      intro y _
      exact Set.mem_iUnion.mpr ⟨y, mem_extChartAt_source y, FiberBundle.mem_baseSet_trivializationAt' y⟩)
  have hcover : (⋃ j, bundleChartSource (r := r) E (v j)) = Set.univ := Set.eq_univ_of_univ_subset hv
  have hm := AEMeasurable.iUnion (fun j => aemeasurable_on_bundleChartSource (r := r) E g.form μ hμ (v j)
    _ (L14Aux.formNormSq_top_inChart_aemeasurable E g h hh u hu (v j)))
  simpa only [hcover, Measure.restrict_univ] using hm
/-- The frozen finite weighted norm of a top form is a genuine Bochner
integral; both measurability and nonnegativity have been proved from charts. -/
theorem weightedTopNorm_integrable (g : Yau.SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (h : Metric E)
    (hh : BundleDbar.SmoothMetric (r := r) E h) (φ : M.Carrier → ℝ) (hφ : SmoothFn φ)
    (u : NQForm E 0) (hu : WeightedL2 (r := r) E g.form h μ φ u) :
    Integrable (fun x => BundleDbar.formNormSq (r := r) E g.form h u x * Real.exp (-φ x)) μ := by
  have hw : Measurable (fun x => Real.exp (-φ x)) :=
    (Real.continuous_exp.comp (L18Aux.continuous_of_smoothFn hφ).neg).measurable
  have hm := (formNormSq_top_aemeasurable E g μ hμ h hh u hu.1).mul hw.aemeasurable
  have hn : ∀ᵐ x ∂μ, 0 ≤ BundleDbar.formNormSq (r := r) E g.form h u x * Real.exp (-φ x) :=
    Filter.Eventually.of_forall fun x => mul_nonneg (formNormSq_top_nonneg E g.form h u x)
      (Real.exp_pos _).le
  refine ⟨hm.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal hn).mpr ?_⟩
  exact hu.2

theorem weightedNormSq_top_eq_ofReal_integral (g : Yau.SmoothMetric M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ) (h : Metric E)
    (hh : BundleDbar.SmoothMetric (r := r) E h) (φ : M.Carrier → ℝ) (hφ : SmoothFn φ)
    (u : NQForm E 0) (hu : WeightedL2 (r := r) E g.form h μ φ u) :
    weightedNormSq (r := r) E g.form h μ φ u =
      ENNReal.ofReal (∫ x, BundleDbar.formNormSq (r := r) E g.form h u x *
        Real.exp (-φ x) ∂μ) := by
  exact (ofReal_integral_eq_lintegral_ofReal
    (weightedTopNorm_integrable E g μ hμ h hh φ hφ u hu)
    (Filter.Eventually.of_forall fun x => mul_nonneg (formNormSq_top_nonneg E g.form h u x)
      (Real.exp_pos _).le)).symm

theorem chartInvExtension_quasiMeasurePreserving (g : Yau.SmoothMetric M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ) (a : M.Carrier) :
    QuasiMeasurePreserving (chartInvExtension a)
      ((lebesgueC n).restrict (localDomain (r := r) E a))
      (μ.restrict (bundleChartSource (r := r) E a)) := by
  let ν := (lebesgueC n).restrict (localDomain (r := r) E a)
  let τ := μ.restrict (bundleChartSource (r := r) E a)
  let d := fun z => ENNReal.ofReal (Real.sqrt (realMetricFn g.form a z).det)
  have hd : AEMeasurable d ν := ENNReal.measurable_ofReal.comp_aemeasurable
    (((L18Aux.volumeDensity_continuousOn g a).mono Set.inter_subset_left).aemeasurable
      (L14Aux.localDomain_isOpen E a).measurableSet)
  have hd0 : ∀ᵐ z ∂ν, d z ≠ 0 := by
    filter_upwards [ae_restrict_mem (L14Aux.localDomain_isOpen E a).measurableSet] with z hz
    apply ne_of_gt
    apply ENNReal.ofReal_pos.mpr
    rw [realMetricFn_sqrt_det g.form a z hz.1]
    exact mul_pos (pow_pos (by norm_num) _) (L18Aux.hMat_det_re_pos g.form a hz.1)
  have hforward : ν ≪ τ.map (chartPtExtension a) := by
    rw [show τ.map (chartPtExtension a) = ν.withDensity d from
      map_chartPtExtension_volume (r := r) E g.form μ hμ a]
    exact withDensity_absolutelyContinuous' hd hd0
  have hm : (τ.map (chartPtExtension a)).map (chartInvExtension a) = τ := by
    rw [Measure.map_map (chartInvExtension_measurable a) (chartPtExtension_measurable a)]
    calc
      τ.map (chartInvExtension a ∘ chartPtExtension a) = τ.map id := by
        apply Measure.map_congr
        filter_upwards [ae_restrict_mem (bundleChartSource_isOpen (r := r) E a).measurableSet] with x hx
        change chartInvExtension a (chartPtExtension a x) = x
        have hxt : chartPt a x ∈ chartTarget a := (extChartAt (ComplexModel n) a).map_source hx.1
        rw [chartPtExtension, if_pos hx.1, chartInvExtension, if_pos hxt,
          chartInv_chartPt_of_mem a x (by simpa only [extChartAt_source] using hx.1)]
      _ = τ := Measure.map_id
  refine ⟨chartInvExtension_measurable a, ?_⟩
  have ht := hforward.map (chartInvExtension_measurable a)
  rwa [hm] at ht

theorem coefficients_ae_eq_of_ae_eq {q : ℕ} (g : Yau.SmoothMetric M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (u v : NQForm E q) (heq : ∀ᵐ x ∂μ, u x = v x)
    (a : M.Carrier) (I : Fin q → Fin n) (α : Fin r) :
    (fun z => coefficients (r := r) E u a z I α) =ᵐ[
      (lebesgueC n).restrict (localDomain (r := r) E a)]
      fun z => coefficients (r := r) E v a z I α := by
  have hlocal : ∀ᵐ x ∂μ.restrict (bundleChartSource (r := r) E a), u x = v x :=
    ae_restrict_of_ae heq
  have hz := (chartInvExtension_quasiMeasurePreserving (r := r) E g μ hμ a).ae hlocal
  filter_upwards [hz, ae_restrict_mem (L14Aux.localDomain_isOpen E a).measurableSet] with z huv hzdom
  have huv' : u (chartInv a z) = v (chartInv a z) := by
    change u (chartInvExtension a z) = v (chartInvExtension a z) at huv
    rw [chartInvExtension, if_pos hzdom.1] at huv
    exact huv
  unfold coefficients
  rw [huv']

theorem locallyL2_of_ae_eq {q : ℕ} (g : Yau.SmoothMetric M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (u v : NQForm E q) (hu : LocallyL2 (r := r) E u) (heq : ∀ᵐ x ∂μ, u x = v x) :
    LocallyL2 (r := r) E v := by
  intro a I α
  have hc := coefficients_ae_eq_of_ae_eq E g μ hμ u v heq a I α
  refine ⟨(hu a I α).1.congr hc, ?_⟩
  intro K hK hsub
  have hcK := hc.filter_mono (Measure.restrict_mono hsub le_rfl).absolutelyContinuous.ae_le
  calc
    (∫⁻ z in K, ENNReal.ofReal (‖coefficients (r := r) E v a z I α‖ ^ 2) ∂lebesgueC n) =
        ∫⁻ z in K, ENNReal.ofReal (‖coefficients (r := r) E u a z I α‖ ^ 2) ∂lebesgueC n :=
      lintegral_congr_ae (hcK.mono fun z hz => congrArg (fun w : ℂ => ENNReal.ofReal (‖w‖ ^ 2)) hz.symm)
    _ < ⊤ := (hu a I α).2 K hK hsub


theorem integral_test_mul_eq_of_ae_on {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {s : Set X} (hs : MeasurableSet s) (u v ψ : X → ℂ)
    (huv : u =ᵐ[μ.restrict s] v) (hψ : Function.support ψ ⊆ s) :
    (∫ z, u z * ψ z ∂μ) = ∫ z, v z * ψ z ∂μ := by
  apply integral_congr_ae
  filter_upwards [(ae_restrict_iff' hs).mp huv] with z hz
  by_cases hzs : z ∈ s
  · rw [hz hzs]
  · have hp : ψ z = 0 := by
      by_contra hp
      exact hzs (hψ hp)
    simp only [hp, mul_zero]

theorem support_wirtBar_subset {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (ψ : X → ℂ) (v : X) : Function.support (fun z => wirtBar ψ z v) ⊆ tsupport ψ := by
  intro z hz
  by_contra hn
  have hd : fderiv ℝ ψ z = 0 := fderiv_of_notMem_tsupport (𝕜 := ℝ) hn
  exact hz (by simp only [wirtBar, hd, ContinuousLinearMap.zero_apply, mul_zero, add_zero])

theorem formNormSq_congr_at {q : ℕ} (g : HermitianField M) (h : Metric E)
    (u v : NQForm E q) (x : M.Carrier) (huv : u x = v x) :
    BundleDbar.formNormSq (r := r) E g h u x = BundleDbar.formNormSq (r := r) E g h v x := by
  have huv' : u (chartInv x (chartPt x x)) = v (chartInv x (chartPt x x)) :=
    Eq.mpr (congrArg (fun y => u y = v y) (chartInv_chartPt_of_mem x x (mem_chart_source _ _))) huv
  have hc (I : Fin q → Fin n) : coefficients (r := r) E u x (chartPt x x) I =
      coefficients (r := r) E v x (chartPt x x) I := by
    unfold coefficients
    rw [huv']
  unfold BundleDbar.formNormSq
  simp_rw [hc]

theorem weightedNormSq_congr_ae {q : ℕ} (g : HermitianField M) (h : Metric E)
    (μ : Measure M.Carrier) (φ : M.Carrier → ℝ) (u v : NQForm E q)
    (huv : ∀ᵐ x ∂μ, u x = v x) :
    weightedNormSq (r := r) E g h μ φ u = weightedNormSq (r := r) E g h μ φ v := by
  apply lintegral_congr_ae
  filter_upwards [huv] with x hx
  rw [formNormSq_congr_at E g h u v x hx]

theorem weightedL2_of_ae_eq {q : ℕ} (g : Yau.SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (h : Metric E) (φ : M.Carrier → ℝ)
    (u v : NQForm E q) (hu : WeightedL2 (r := r) E g.form h μ φ u)
    (huv : ∀ᵐ x ∂μ, u x = v x) : WeightedL2 (r := r) E g.form h μ φ v := by
  refine ⟨locallyL2_of_ae_eq E g μ hμ u v hu.1 huv, ?_⟩
  rw [← weightedNormSq_congr_ae E g.form h μ φ u v huv]
  exact hu.2

theorem weakDbar_of_ae_eq {q : ℕ} (g : Yau.SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (u u' : NQForm E q) (f f' : NQForm E (q + 1))
    (hu : ∀ᵐ x ∂μ, u x = u' x) (hf : ∀ᵐ x ∂μ, f x = f' x)
    (hw : WeakDbar (r := r) E u f) : WeakDbar (r := r) E u' f' := by
  refine ⟨locallyL2_of_ae_eq E g μ hμ u u' hw.1 hu,
    locallyL2_of_ae_eq E g μ hμ f f' hw.2.1 hf, ?_⟩
  intro a I α ψ hψ hcompact hsupp
  have hleft := integral_test_mul_eq_of_ae_on (lebesgueC n) (L14Aux.localDomain_isOpen E a).measurableSet
    _ _ ψ (coefficients_ae_eq_of_ae_eq E g μ hμ f f' hf a I α)
    ((subset_tsupport ψ).trans hsupp)
  rw [← hleft, hw.2.2 a I α ψ hψ hcompact hsupp]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [integral_test_mul_eq_of_ae_on (lebesgueC n) (L14Aux.localDomain_isOpen E a).measurableSet
    _ _ (fun z => wirtBar ψ z (stdVec (I k)))
    (coefficients_ae_eq_of_ae_eq E g μ hμ u u' hu a (fun l => I (k.succAbove l)) α)
    ((support_wirtBar_subset ψ (stdVec (I k))).trans hsupp)]

theorem weaklyClosed_of_ae_eq {q : ℕ} (g : Yau.SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (f f' : NQForm E q)
    (hf : ∀ᵐ x ∂μ, f x = f' x) (hw : WeaklyClosed (r := r) E f) :
    WeaklyClosed (r := r) E f' := by
  refine ⟨locallyL2_of_ae_eq E g μ hμ f f' hw.1 hf, ?_⟩
  intro a I α ψ hψ hcompact hsupp
  calc
    _ = ∑ k : Fin (q + 1), (-1 : ℂ) ^ k.val *
        ∫ z, coefficients (r := r) E f a z (fun l => I (k.succAbove l)) α *
          wirtBar ψ z (stdVec (I k)) ∂lebesgueC n := by
      apply Finset.sum_congr rfl
      intro k _
      rw [integral_test_mul_eq_of_ae_on (lebesgueC n) (L14Aux.localDomain_isOpen E a).measurableSet
        _ _ (fun z => wirtBar ψ z (stdVec (I k)))
        (coefficients_ae_eq_of_ae_eq E g μ hμ f f' hf a (fun l => I (k.succAbove l)) α)
        ((support_wirtBar_subset ψ (stdVec (I k))).trans hsupp)]
    _ = 0 := hw.2 a I α ψ hψ hcompact hsupp

theorem maximalDbarGraph_of_ae_eq {q : ℕ} (g : Yau.SmoothMetric M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ) (h : Metric E)
    (φ : M.Carrier → ℝ) (u u' : NQForm E q) (f f' : NQForm E (q + 1))
    (hu : ∀ᵐ x ∂μ, u x = u' x) (hf : ∀ᵐ x ∂μ, f x = f' x)
    (hw : MaximalDbarGraph (r := r) E g.form h μ φ u f) :
    MaximalDbarGraph (r := r) E g.form h μ φ u' f' :=
  ⟨weightedL2_of_ae_eq E g μ hμ h φ u u' hw.1 hu,
    weightedL2_of_ae_eq E g μ hμ h φ f f' hw.2.1 hf,
    weakDbar_of_ae_eq E g μ hμ u u' f f' hu hf hw.2.2⟩

/-- The saturated graph on the frozen a.e. quotient agrees with the
distributional graph for every choice of actual weighted-L² representatives. -/
theorem maximalDbarL2Graph_iff_weakDbar {q : ℕ} (g : Yau.SmoothMetric M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ) (h : Metric E)
    (φ : M.Carrier → ℝ)
    (u : {u : NQForm E q // WeightedL2 (r := r) E g.form h μ φ u})
    (f : {f : NQForm E (q + 1) // WeightedL2 (r := r) E g.form h μ φ f}) :
    MaximalDbarL2Graph (r := r) E g.form h μ φ (Quotient.mk _ u) (Quotient.mk _ f) ↔
      WeakDbar (r := r) E u.1 f.1 := by
  constructor
  · rintro ⟨u₀, f₀, hu, hf, hw⟩
    exact weakDbar_of_ae_eq E g μ hμ u₀.1 u.1 f₀.1 f.1
      (Quotient.eq.mp hu) (Quotient.eq.mp hf) hw
  · intro hw
    exact ⟨u, f, rfl, rfl, hw⟩

def antiComplexSubmodule (x : M.Carrier) (q : ℕ) : Submodule ℂ (MixedTensor E x q) where
  carrier := {A | AntiComplexLinear E A}
  zero_mem' := by
    intro v i c
    simp
  add_mem' := by
    intro A B hA hB v i c
    change A (Function.update v i (c • v i)) + B (Function.update v i (c • v i)) =
      star c • (A v + B v)
    rw [hA, hB, smul_add]
  smul_mem' := by
    intro c A hA v i d
    change c • A (Function.update v i (d • v i)) = star d • (c • A v)
    rw [hA, smul_smul, smul_smul, mul_comm c]

instance nqFormAddCommGroup (q : ℕ) : AddCommGroup (NQForm E q) :=
  @Pi.addCommGroup M.Carrier (fun x => antiComplexSubmodule E x q)
    (fun x => (antiComplexSubmodule E x q).addCommGroup)

instance nqFormModule (q : ℕ) : Module ℂ (NQForm E q) :=
  @Pi.module M.Carrier (fun x => antiComplexSubmodule E x q) ℂ inferInstance
    (fun x => (antiComplexSubmodule E x q).addCommGroup.toAddCommMonoid)
    (fun x => (antiComplexSubmodule E x q).module)

theorem nqForm_zero_apply (q : ℕ) (x : M.Carrier) :
    ((0 : NQForm E q) x).1 = 0 := rfl

theorem nqForm_add_apply {q : ℕ} (u v : NQForm E q) (x : M.Carrier) :
    ((u + v) x).1 = (u x).1 + (v x).1 := rfl

theorem nqForm_smul_apply {q : ℕ} (c : ℂ) (u : NQForm E q) (x : M.Carrier) :
    ((c • u) x).1 = c • (u x).1 := rfl


theorem coefficients_add {q : ℕ} (u v : NQForm E q) (a : M.Carrier)
    (z : ComplexVector n) (I : Fin q → Fin n) (α : Fin r) :
    coefficients (r := r) E (u + v) a z I α =
      coefficients (r := r) E u a z I α + coefficients (r := r) E v a z I α := by
  simp only [coefficients, nqForm_add_apply, AlternatingMap.add_apply, map_add, PiLp.add_apply]

theorem coefficients_zero {q : ℕ} (a : M.Carrier) (z : ComplexVector n)
    (I : Fin q → Fin n) (α : Fin r) :
    coefficients (r := r) E (0 : NQForm E q) a z I α = 0 := by
  simp only [coefficients, nqForm_zero_apply, AlternatingMap.zero_apply, map_zero, PiLp.zero_apply]

theorem coefficients_smul {q : ℕ} (c : ℂ) (u : NQForm E q) (a : M.Carrier)
    (z : ComplexVector n) (I : Fin q → Fin n) (α : Fin r) :
    coefficients (r := r) E (c • u) a z I α = c * coefficients (r := r) E u a z I α := by
  simp only [coefficients, nqForm_smul_apply, AlternatingMap.smul_apply, map_smul,
    PiLp.smul_apply, smul_eq_mul]

theorem locallyL2_zero (q : ℕ) : LocallyL2 (r := r) E (0 : NQForm E q) := by
  intro a I α
  simp only [coefficients_zero]
  refine ⟨aestronglyMeasurable_const, ?_⟩
  intro K hK hsub
  simp

theorem locallyL2_add {q : ℕ} (u v : NQForm E q)
    (hu : LocallyL2 (r := r) E u) (hv : LocallyL2 (r := r) E v) :
    LocallyL2 (r := r) E (u + v) := by
  intro a I α
  refine ⟨?_, ?_⟩
  · simp only [coefficients_add]
    exact (hu a I α).1.add (hv a I α).1
  · intro K hK hsub
    have hp : MemLp (fun z => coefficients (r := r) E u a z I α +
        coefficients (r := r) E v a z I α) 2 ((lebesgueC n).restrict K) :=
      (L14Aux.locallyL2_coefficients_memLp E u hu a I α K hK hsub).add
        (L14Aux.locallyL2_coefficients_memLp E v hv a I α K hK hsub)
    simpa only [coefficients_add] using L14Aux.lintegral_norm_sq_lt_top_of_memLp hp

theorem locallyL2_smul {q : ℕ} (c : ℂ) (u : NQForm E q)
    (hu : LocallyL2 (r := r) E u) : LocallyL2 (r := r) E (c • u) := by
  intro a I α
  simp only [coefficients_smul]
  refine ⟨(hu a I α).1.const_mul c, ?_⟩
  intro K hK hsub
  exact L14Aux.lintegral_norm_sq_lt_top_of_memLp
    ((L14Aux.locallyL2_coefficients_memLp E u hu a I α K hK hsub).const_mul c)

section HermitianBounds
variable {V : Type*} [AddCommGroup V] [Module ℂ V]
variable (h : HermitianInnerProduct V)
theorem hermitian_neg_left (u v : V) : h.toFun (-u) v = -h.toFun u v := by
  simpa using h.map_smul_left (-1) u v

theorem hermitian_neg_right (u v : V) : h.toFun u (-v) = -h.toFun u v := by
  simpa using h.map_smul_right (-1) u v

theorem hermitian_sub_left (u v w : V) : h.toFun (u - v) w = h.toFun u w - h.toFun v w := by
  simp only [sub_eq_add_neg, h.map_add_left, hermitian_neg_left]

theorem hermitian_sub_right (u v w : V) : h.toFun u (v - w) = h.toFun u v - h.toFun u w := by
  simp only [sub_eq_add_neg, h.map_add_right, hermitian_neg_right]

theorem hermitian_add_self_le (u v : V) :
    (h.toFun (u + v) (u + v)).re ≤ 2 * (h.toFun u u).re + 2 * (h.toFun v v).re := by
  have hp := (h.positive_definite (u - v)).1
  rw [hermitian_sub_left, hermitian_sub_right, hermitian_sub_right] at hp
  rw [h.map_add_left, h.map_add_right, h.map_add_right]
  simp only [Complex.add_re, Complex.sub_re] at *
  linarith
end HermitianBounds

theorem topFormValue_add (u v : NQForm E 0) (a x : M.Carrier) :
    L14Aux.topFormValue E (u + v) a x =
      L14Aux.topFormValue E u a x + L14Aux.topFormValue E v a x := by
  simp only [L14Aux.topFormValue, nqForm_add_apply, AlternatingMap.add_apply]

theorem topFormValue_smul (c : ℂ) (u : NQForm E 0) (a x : M.Carrier) :
    L14Aux.topFormValue E (c • u) a x = c • L14Aux.topFormValue E u a x := by
  simp only [L14Aux.topFormValue, nqForm_smul_apply, AlternatingMap.smul_apply]

theorem formNormSq_top_add_le (g : HermitianField M) (h : Metric E)
    (u v : NQForm E 0) (x : M.Carrier) :
    BundleDbar.formNormSq (r := r) E g h (u + v) x ≤
      2 * BundleDbar.formNormSq (r := r) E g h u x +
        2 * BundleDbar.formNormSq (r := r) E g h v x := by
  simp_rw [formNormSq_top_factor, L14Aux.topCoefficientNormSq_eq_value]
  rw [topFormValue_add]
  have hi := hermitian_add_self_le (h x) (L14Aux.topFormValue E u x x) (L14Aux.topFormValue E v x x)
  have hd : 0 ≤ (gMat g x)⁻¹.det.re :=
    (Complex.nonneg_iff.mp (gMat_posDef g x).inv.posSemidef.det_nonneg).1
  nlinarith [mul_nonneg hd (sub_nonneg.mpr hi)]

theorem formNormSq_top_smul (g : HermitianField M) (h : Metric E)
    (c : ℂ) (u : NQForm E 0) (x : M.Carrier) :
    BundleDbar.formNormSq (r := r) E g h (c • u) x =
      Complex.normSq c * BundleDbar.formNormSq (r := r) E g h u x := by
  simp_rw [formNormSq_top_factor, L14Aux.topCoefficientNormSq_eq_value]
  rw [topFormValue_smul, (h x).map_smul_left, (h x).map_smul_right]
  have he (z w : ℂ) : (star z * (w * z)).re = Complex.normSq z * w.re := by
    simp only [Complex.mul_re, Complex.mul_im, Complex.star_def,
      Complex.conj_re, Complex.conj_im, Complex.normSq_apply]
    ring
  rw [he]
  ring

theorem weightedNormSq_top_smul (g : HermitianField M) (h : Metric E)
    (μ : Measure M.Carrier) (φ : M.Carrier → ℝ) (c : ℂ) (u : NQForm E 0) :
    weightedNormSq (r := r) E g h μ φ (c • u) =
      ENNReal.ofReal (Complex.normSq c) * weightedNormSq (r := r) E g h μ φ u := by
  unfold weightedNormSq
  simp_rw [formNormSq_top_smul, mul_assoc, ENNReal.ofReal_mul (Complex.normSq_nonneg c)]
  exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

theorem weightedL2_top_zero (g : HermitianField M) (h : Metric E)
    (μ : Measure M.Carrier) (φ : M.Carrier → ℝ) :
    WeightedL2 (r := r) E g h μ φ (0 : NQForm E 0) := by
  refine ⟨locallyL2_zero E 0, ?_⟩
  simp [weightedNormSq, BundleDbar.formNormSq, coefficients_zero]

theorem weightedL2_top_smul (g : HermitianField M) (h : Metric E)
    (μ : Measure M.Carrier) (φ : M.Carrier → ℝ) (c : ℂ) (u : NQForm E 0)
    (hu : WeightedL2 (r := r) E g h μ φ u) : WeightedL2 (r := r) E g h μ φ (c • u) := by
  refine ⟨locallyL2_smul E c u hu.1, ?_⟩
  rw [weightedNormSq_top_smul]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hu.2


theorem weightedL2_top_add (g : Yau.SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (h : Metric E)
    (hh : BundleDbar.SmoothMetric (r := r) E h) (φ : M.Carrier → ℝ) (hφ : SmoothFn φ)
    (u v : NQForm E 0) (hu : WeightedL2 (r := r) E g.form h μ φ u)
    (hv : WeightedL2 (r := r) E g.form h μ φ v) :
    WeightedL2 (r := r) E g.form h μ φ (u + v) := by
  have hlocal := locallyL2_add E u v hu.1 hv.1
  have hw : Measurable (fun x => Real.exp (-φ x)) :=
    (Real.continuous_exp.comp (L18Aux.continuous_of_smoothFn hφ).neg).measurable
  have hm : AEStronglyMeasurable (fun x => BundleDbar.formNormSq (r := r) E g.form h (u + v) x *
      Real.exp (-φ x)) μ :=
    ((L14Aux.formNormSq_top_aemeasurable E g μ hμ h hh (u + v) hlocal).mul hw.aemeasurable).aestronglyMeasurable
  have hdom := ((L14Aux.weightedTopNorm_integrable E g μ hμ h hh φ hφ u hu).const_mul 2).add
    ((L14Aux.weightedTopNorm_integrable E g μ hμ h hh φ hφ v hv).const_mul 2)
  have hn : ∀ᵐ x ∂μ, 0 ≤ BundleDbar.formNormSq (r := r) E g.form h (u + v) x * Real.exp (-φ x) :=
    Filter.Eventually.of_forall fun x => mul_nonneg (L14Aux.formNormSq_top_nonneg E g.form h (u + v) x)
      (Real.exp_pos _).le
  have hi : Integrable (fun x => BundleDbar.formNormSq (r := r) E g.form h (u + v) x * Real.exp (-φ x)) μ := by
    apply hdom.mono' hm
    filter_upwards [hn] with x hnx
    change ‖BundleDbar.formNormSq (r := r) E g.form h (u + v) x * Real.exp (-φ x)‖ ≤
      2 * (BundleDbar.formNormSq (r := r) E g.form h u x * Real.exp (-φ x)) +
        2 * (BundleDbar.formNormSq (r := r) E g.form h v x * Real.exp (-φ x))
    rw [Real.norm_of_nonneg hnx]
    have ht := mul_le_mul_of_nonneg_right (formNormSq_top_add_le (r := r) E g.form h u v x)
      (Real.exp_pos (-φ x)).le
    nlinarith
  exact ⟨hlocal, (hasFiniteIntegral_iff_ofReal hn).mp hi.2⟩

def weightedTopFormSubmodule (g : Yau.SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (h : Metric E)
    (hh : BundleDbar.SmoothMetric (r := r) E h) (φ : M.Carrier → ℝ) (hφ : SmoothFn φ) :
    Submodule ℂ (NQForm E 0) where
  carrier := {u | WeightedL2 (r := r) E g.form h μ φ u}
  zero_mem' := weightedL2_top_zero E g.form h μ φ
  add_mem' := fun hu hv => weightedL2_top_add E g μ hμ h hh φ hφ _ _ hu hv
  smul_mem' := fun c u hu => weightedL2_top_smul E g.form h μ φ c u hu

def topFormPairing (g : HermitianField M) (h : Metric E)
    (u v : NQForm E 0) (x : M.Carrier) : ℂ :=
  ((gMat g x)⁻¹.det.re : ℂ) *
    (h x).toFun (topFormValue E u x x) (topFormValue E v x x)

theorem topFormPairing_self_re (g : HermitianField M) (h : Metric E)
    (u : NQForm E 0) (x : M.Carrier) :
    (topFormPairing E g h u u x).re = BundleDbar.formNormSq (r := r) E g h u x := by
  rw [formNormSq_top_factor, topCoefficientNormSq_eq_value]
  simp only [topFormPairing, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]

theorem topFormPairing_add_left (g : HermitianField M) (h : Metric E)
    (u v w : NQForm E 0) (x : M.Carrier) :
    topFormPairing E g h (u + v) w x = topFormPairing E g h u w x + topFormPairing E g h v w x := by
  unfold topFormPairing
  rw [topFormValue_add, (h x).map_add_left, mul_add]

theorem topFormPairing_add_right (g : HermitianField M) (h : Metric E)
    (u v w : NQForm E 0) (x : M.Carrier) :
    topFormPairing E g h u (v + w) x = topFormPairing E g h u v x + topFormPairing E g h u w x := by
  unfold topFormPairing
  rw [topFormValue_add, (h x).map_add_right, mul_add]

theorem topFormPairing_smul_left (g : HermitianField M) (h : Metric E)
    (c : ℂ) (u v : NQForm E 0) (x : M.Carrier) :
    topFormPairing E g h (c • u) v x = star c * topFormPairing E g h u v x := by
  unfold topFormPairing
  rw [topFormValue_smul, (h x).map_smul_left]
  ring

theorem topFormPairing_smul_right (g : HermitianField M) (h : Metric E)
    (c : ℂ) (u v : NQForm E 0) (x : M.Carrier) :
    topFormPairing E g h u (c • v) x = c * topFormPairing E g h u v x := by
  unfold topFormPairing
  rw [topFormValue_smul, (h x).map_smul_right]
  ring

theorem topFormPairing_conj_symm (g : HermitianField M) (h : Metric E)
    (u v : NQForm E 0) (x : M.Carrier) :
    star (topFormPairing E g h v u x) = topFormPairing E g h u v x := by
  unfold topFormPairing
  rw [star_mul, show star ((gMat g x)⁻¹.det.re : ℂ) = ((gMat g x)⁻¹.det.re : ℂ) from by simp,
    ← (h x).conjugate_symmetric]
  ring

@[instance_reducible]
def topFormPointPreInner (g : HermitianField M) (h : Metric E) (x : M.Carrier) :
    PreInnerProductSpace.Core ℂ (NQForm E 0) where
  inner u v := topFormPairing E g h u v x
  conj_inner_symm u v := topFormPairing_conj_symm E g h u v x
  re_inner_nonneg u := by
    change 0 ≤ (topFormPairing E g h u u x).re
    simp only [topFormPairing, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    exact mul_nonneg (Complex.nonneg_iff.mp (gMat_posDef g x).inv.posSemidef.det_nonneg).1
      ((h x).positive_definite _).1
  add_left u v w := topFormPairing_add_left E g h u v w x
  smul_left u v c := topFormPairing_smul_left E g h c u v x

theorem topFormPairing_cauchySchwarz (g : HermitianField M) (h : Metric E)
    (u v : NQForm E 0) (x : M.Carrier) :
    Complex.normSq (topFormPairing E g h u v x) ≤
      BundleDbar.formNormSq (r := r) E g h u x * BundleDbar.formNormSq (r := r) E g h v x := by
  letI : PreInnerProductSpace.Core ℂ (NQForm E 0) := topFormPointPreInner E g h x
  have ht := InnerProductSpace.Core.inner_mul_inner_self_le (𝕜 := ℂ) u v
  change ‖topFormPairing E g h u v x‖ * ‖topFormPairing E g h v u x‖ ≤
    (topFormPairing E g h u u x).re * (topFormPairing E g h v v x).re at ht
  rw [topFormPairing_self_re (r := r), topFormPairing_self_re (r := r)] at ht
  have hn : ‖topFormPairing E g h v u x‖ = ‖topFormPairing E g h u v x‖ := by
    simpa only [norm_star] using congrArg norm (topFormPairing_conj_symm E g h u v x)
  rw [hn] at ht
  simpa only [Complex.normSq_eq_norm_sq, pow_two] using ht

theorem topFormPairing_re_in_fixed_chart (g : HermitianField M) (h : Metric E)
    (u v : NQForm E 0) (a x : M.Carrier)
    (hx : x ∈ (extChartAt (ComplexModel n) a).source) :
    (topFormPairing E g h u v x).re =
      ((h x).toFun (topFormValue E u a x) (topFormValue E v a x)).re /
        (frameGram g a x).det.re := by
  have hv (w : NQForm E 0) (b : M.Carrier) (hb : x ∈ (extChartAt (ComplexModel n) b).source) :
      (w x).1 Fin.elim0 (chartFrameBasis b x hb) = topFormValue E w b x := by
    unfold topFormValue
    congr 1
    funext i
    exact chartFrameBasis_apply b x hb i
  simp only [topFormPairing, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [gMat_inv_det_re, gMat_eq_frameGram,
    frameGram_eq_hermitianGram g x x (mem_extChartAt_source x)]
  have ht := alternating_hermitian_ratio_basis_independent
    (Module.Free.chooseBasis ℂ (E x)) (g x) (h x)
    (chartFrameBasis a x hx) (chartFrameBasis x x (mem_extChartAt_source x))
    ((u x).1 Fin.elim0) ((v x).1 Fin.elim0)
  rw [hv u a hx, hv v a hx, hv u x (mem_extChartAt_source x), hv v x (mem_extChartAt_source x),
    ← frameGram_eq_hermitianGram g a x hx] at ht
  simpa only [div_eq_mul_inv, mul_comm] using ht

theorem topFormPairing_re_inChart (g : HermitianField M) (h : Metric E)
    (u v : NQForm E 0) (a : M.Carrier) (z : ComplexVector n)
    (hz : z ∈ localDomain (r := r) E a) :
    (topFormPairing E g h u v (chartInv a z)).re =
      ((hMat g a z).det.re)⁻¹ *
        (∑ α, ∑ β, star (coefficients (r := r) E u a z Fin.elim0 α) *
          BundleDbar.metricMatrix (r := r) E h a z α β *
            coefficients (r := r) E v a z Fin.elim0 β).re := by
  rw [topFormPairing_re_in_fixed_chart E g h u v a (chartInv a z)
    ((extChartAt (ComplexModel n) a).map_target hz.1)]
  have hn : (∑ α, ∑ β, star (coefficients (r := r) E u a z Fin.elim0 α) *
      BundleDbar.metricMatrix (r := r) E h a z α β *
        coefficients (r := r) E v a z Fin.elim0 β).re =
      ((h (chartInv a z)).toFun (topFormValue E u a (chartInv a z))
        (topFormValue E v a (chartInv a z))).re := by
    simp_rw [coefficients_topFormValue]
    exact congrArg Complex.re (metricMatrix_pairing E h a z hz _ _)
  rw [hn]
  change _ / (hMat g a z).det.re = _
  rw [div_eq_mul_inv, mul_comm]

theorem topFormPairing_re_inChart_aemeasurable (g : Yau.SmoothMetric M)
    (h : Metric E) (hh : BundleDbar.SmoothMetric (r := r) E h)
    (u v : NQForm E 0) (hu : LocallyL2 (r := r) E u) (hv : LocallyL2 (r := r) E v)
    (a : M.Carrier) :
    AEMeasurable (fun z => (topFormPairing E g.form h u v (chartInv a z)).re)
      ((lebesgueC n).restrict (localDomain (r := r) E a)) := by
  have hd : ContinuousOn (fun z => (hMat g.form a z).det.re) (chartTarget a) :=
    Complex.continuous_re.comp_continuousOn
      (L18Aux.contDiffOn_matrix_det (L18Aux.hMat_contDiffOn g a)).continuousOn
  have hdi := (hd.inv₀ fun z hz => ne_of_gt (L18Aux.hMat_det_re_pos g.form a hz)).mono
    (show localDomain (r := r) E a ⊆ chartTarget a from Set.inter_subset_left)
  have hdm : AEMeasurable (fun z => ((hMat g.form a z).det.re)⁻¹)
      ((lebesgueC n).restrict (localDomain (r := r) E a)) :=
    (hdi.aestronglyMeasurable (localDomain_isOpen E a).measurableSet).aemeasurable
  have hnm : AEMeasurable (fun z =>
      (∑ α, ∑ β, star (coefficients (r := r) E u a z Fin.elim0 α) *
        BundleDbar.metricMatrix (r := r) E h a z α β *
          coefficients (r := r) E v a z Fin.elim0 β).re)
      ((lebesgueC n).restrict (localDomain (r := r) E a)) := by
    apply Complex.measurable_re.comp_aemeasurable
    apply Finset.aemeasurable_fun_sum
    intro α _
    apply Finset.aemeasurable_fun_sum
    intro β _
    have hα := (hu a Fin.elim0 α).1.aemeasurable
    have hβ := (hv a Fin.elim0 β).1.aemeasurable
    have hH := ((hh a α β).continuousOn.aestronglyMeasurable
      (localDomain_isOpen E a).measurableSet (μ := lebesgueC n)).aemeasurable
    exact ((continuous_star.measurable.comp_aemeasurable hα).mul hH).mul hβ
  have he : (fun z => (topFormPairing E g.form h u v (chartInv a z)).re) =ᵐ[
      (lebesgueC n).restrict (localDomain (r := r) E a)]
      fun z => ((hMat g.form a z).det.re)⁻¹ *
        (∑ α, ∑ β, star (coefficients (r := r) E u a z Fin.elim0 α) *
          BundleDbar.metricMatrix (r := r) E h a z α β *
            coefficients (r := r) E v a z Fin.elim0 β).re :=
    (ae_restrict_mem (localDomain_isOpen E a).measurableSet).mono
      fun z hz => topFormPairing_re_inChart E g.form h u v a z hz
  exact (hdm.mul hnm).congr he.symm

theorem aemeasurable_of_bundleCharts (g : HermitianField M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g μ) (F : M.Carrier → ℝ)
    (hF : ∀ a, AEMeasurable (fun z => F (chartInv a z))
      ((lebesgueC n).restrict (localDomain (r := r) E a))) : AEMeasurable F μ := by
  obtain ⟨v, hv⟩ := isLindelof_univ.indexed_countable_subcover (bundleChartSource (r := r) E)
    (bundleChartSource_isOpen (r := r) E) (by
      intro y _
      exact Set.mem_iUnion.mpr ⟨y, mem_extChartAt_source y, FiberBundle.mem_baseSet_trivializationAt' y⟩)
  have hcover : (⋃ j, bundleChartSource (r := r) E (v j)) = Set.univ := Set.eq_univ_of_univ_subset hv
  have hm := AEMeasurable.iUnion (fun j => aemeasurable_on_bundleChartSource (r := r) E g μ hμ (v j) F (hF (v j)))
  simpa only [hcover, Measure.restrict_univ] using hm

theorem topFormPairing_re_aemeasurable (g : Yau.SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (h : Metric E) (hh : BundleDbar.SmoothMetric (r := r) E h)
    (u v : NQForm E 0) (hu : LocallyL2 (r := r) E u) (hv : LocallyL2 (r := r) E v) :
    AEMeasurable (fun x => (topFormPairing E g.form h u v x).re) μ := by
  exact aemeasurable_of_bundleCharts E g.form μ hμ _
    (fun a => topFormPairing_re_inChart_aemeasurable E g h hh u v hu hv a)

theorem topFormPairing_aemeasurable (g : Yau.SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (h : Metric E) (hh : BundleDbar.SmoothMetric (r := r) E h)
    (u v : NQForm E 0) (hu : LocallyL2 (r := r) E u) (hv : LocallyL2 (r := r) E v) :
    AEMeasurable (topFormPairing E g.form h u v) μ := by
  have hre := topFormPairing_re_aemeasurable E g μ hμ h hh u v hu hv
  have hri := (topFormPairing_re_aemeasurable E g μ hμ h hh u (Complex.I • v) hu
    (locallyL2_smul E Complex.I v hv)).neg
  have he : (fun x => -(topFormPairing E g.form h u (Complex.I • v) x).re) =
      fun x => (topFormPairing E g.form h u v x).im := by
    funext x
    rw [topFormPairing_smul_right, Complex.I_mul_re, neg_neg]
  change AEMeasurable (fun x => -(topFormPairing E g.form h u (Complex.I • v) x).re) μ at hri
  rw [he] at hri
  have hm : AEMeasurable (fun x => ((topFormPairing E g.form h u v x).re : ℂ) +
      ((topFormPairing E g.form h u v x).im : ℂ) * Complex.I) μ :=
    (Complex.continuous_ofReal.measurable.comp_aemeasurable hre).add
      ((Complex.continuous_ofReal.measurable.comp_aemeasurable hri).mul_const Complex.I)
  convert hm using 1
  funext x
  exact (Complex.re_add_im _).symm


def weightedTopPairing (g : HermitianField M) (h : Metric E) (φ : M.Carrier → ℝ)
    (u v : NQForm E 0) (x : M.Carrier) : ℂ :=
  topFormPairing E g h u v x * (Real.exp (-φ x) : ℂ)

theorem weightedTopPairing_self_re (g : HermitianField M) (h : Metric E)
    (φ : M.Carrier → ℝ) (u : NQForm E 0) (x : M.Carrier) :
    (weightedTopPairing E g h φ u u x).re =
      BundleDbar.formNormSq (r := r) E g h u x * Real.exp (-φ x) := by
  simp only [weightedTopPairing, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero]
  rw [topFormPairing_self_re (r := r)]

theorem weightedTopPairing_integrable (g : Yau.SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (h : Metric E)
    (hh : BundleDbar.SmoothMetric (r := r) E h) (φ : M.Carrier → ℝ) (hφ : SmoothFn φ)
    (u v : NQForm E 0) (hu : WeightedL2 (r := r) E g.form h μ φ u)
    (hv : WeightedL2 (r := r) E g.form h μ φ v) :
    Integrable (weightedTopPairing E g.form h φ u v) μ := by
  have hw : AEMeasurable (fun x => (Real.exp (-φ x) : ℂ)) μ :=
    Complex.continuous_ofReal.measurable.comp_aemeasurable
      (Real.continuous_exp.comp (L18Aux.continuous_of_smoothFn hφ).neg).measurable.aemeasurable
  have hm : AEStronglyMeasurable (weightedTopPairing E g.form h φ u v) μ :=
    ((topFormPairing_aemeasurable E g μ hμ h hh u v hu.1 hv.1).mul hw).aestronglyMeasurable
  have ha : ∀ᵐ x ∂μ, 0 ≤ BundleDbar.formNormSq (r := r) E g.form h u x * Real.exp (-φ x) :=
    Filter.Eventually.of_forall fun x => mul_nonneg (formNormSq_top_nonneg E g.form h u x) (Real.exp_pos _).le
  have hb : ∀ᵐ x ∂μ, 0 ≤ BundleDbar.formNormSq (r := r) E g.form h v x * Real.exp (-φ x) :=
    Filter.Eventually.of_forall fun x => mul_nonneg (formNormSq_top_nonneg E g.form h v x) (Real.exp_pos _).le
  have hbound : ∀ᵐ x ∂μ, Complex.normSq (weightedTopPairing E g.form h φ u v x) ≤
      (BundleDbar.formNormSq (r := r) E g.form h u x * Real.exp (-φ x)) *
        (BundleDbar.formNormSq (r := r) E g.form h v x * Real.exp (-φ x)) := by
    apply Filter.Eventually.of_forall
    intro x
    unfold weightedTopPairing
    rw [Complex.normSq_mul, Complex.normSq_ofReal]
    calc
      _ ≤ (BundleDbar.formNormSq (r := r) E g.form h u x * BundleDbar.formNormSq (r := r) E g.form h v x) *
          (Real.exp (-φ x) * Real.exp (-φ x)) :=
        mul_le_mul_of_nonneg_right (topFormPairing_cauchySchwarz (r := r) E g.form h u v x)
          (mul_self_nonneg (Real.exp (-φ x)))
      _ = _ := by ring
  exact integrable_of_normSq_le_mul μ _ _ _ hm
    (weightedTopNorm_integrable E g μ hμ h hh φ hφ u hu)
    (weightedTopNorm_integrable E g μ hμ h hh φ hφ v hv) ha hb hbound

def weightedTopInner (g : HermitianField M) (μ : Measure M.Carrier) (h : Metric E)
    (φ : M.Carrier → ℝ) (u v : NQForm E 0) : ℂ :=
  ∫ x, weightedTopPairing E g h φ u v x ∂μ

@[instance_reducible]
def weightedTopFormPreInner (g : Yau.SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (h : Metric E)
    (hh : BundleDbar.SmoothMetric (r := r) E h) (φ : M.Carrier → ℝ) (hφ : SmoothFn φ) :
    PreInnerProductSpace.Core ℂ (weightedTopFormSubmodule (r := r) E g μ hμ h hh φ hφ) where
  inner u v := weightedTopInner E g.form μ h φ u.1 v.1
  conj_inner_symm u v := by
    change star (∫ x, weightedTopPairing E g.form h φ v.1 u.1 x ∂μ) =
      ∫ x, weightedTopPairing E g.form h φ u.1 v.1 x ∂μ
    calc
      _ = ∫ x, star (weightedTopPairing E g.form h φ v.1 u.1 x) ∂μ := (integral_conj (f := weightedTopPairing E g.form h φ v.1 u.1)).symm
      _ = _ := by
        apply integral_congr_ae
        apply Filter.Eventually.of_forall
        intro x
        change star (topFormPairing E g.form h v.1 u.1 x * (Real.exp (-φ x) : ℂ)) =
          topFormPairing E g.form h u.1 v.1 x * (Real.exp (-φ x) : ℂ)
        rw [star_mul, topFormPairing_conj_symm,
          show star (Real.exp (-φ x) : ℂ) = (Real.exp (-φ x) : ℂ) from by
            simp only [Complex.star_def, Complex.conj_ofReal]]
        ring
  re_inner_nonneg u := by
    change 0 ≤ (∫ x, weightedTopPairing E g.form h φ u.1 u.1 x ∂μ).re
    have hp := weightedTopPairing_integrable E g μ hμ h hh φ hφ u.1 u.1 u.2 u.2
    have hr : (∫ x, (weightedTopPairing E g.form h φ u.1 u.1 x).re ∂μ) =
        (∫ x, weightedTopPairing E g.form h φ u.1 u.1 x ∂μ).re := by
      simpa only [RCLike.re_eq_complex_re] using integral_re (𝕜 := ℂ) hp
    rw [← hr]
    apply integral_nonneg
    intro x
    change 0 ≤ (weightedTopPairing E g.form h φ u.1 u.1 x).re
    rw [weightedTopPairing_self_re (r := r)]
    exact mul_nonneg (formNormSq_top_nonneg E g.form h u.1 x) (Real.exp_pos _).le
  add_left u v w := by
    change weightedTopInner E g.form μ h φ (u.1 + v.1) w.1 =
      weightedTopInner E g.form μ h φ u.1 w.1 + weightedTopInner E g.form μ h φ v.1 w.1
    unfold weightedTopInner
    calc
      _ = ∫ x, weightedTopPairing E g.form h φ u.1 w.1 x + weightedTopPairing E g.form h φ v.1 w.1 x ∂μ := by
        apply integral_congr_ae
        apply Filter.Eventually.of_forall
        intro x
        unfold weightedTopPairing
        rw [topFormPairing_add_left, add_mul]
      _ = _ := integral_add (weightedTopPairing_integrable E g μ hμ h hh φ hφ u.1 w.1 u.2 w.2)
        (weightedTopPairing_integrable E g μ hμ h hh φ hφ v.1 w.1 v.2 w.2)
  smul_left u v c := by
    change weightedTopInner E g.form μ h φ (c • u.1) v.1 = star c * weightedTopInner E g.form μ h φ u.1 v.1
    unfold weightedTopInner
    calc
      _ = ∫ x, star c * weightedTopPairing E g.form h φ u.1 v.1 x ∂μ := by
        apply integral_congr_ae
        apply Filter.Eventually.of_forall
        intro x
        unfold weightedTopPairing
        rw [topFormPairing_smul_left]
        ring
      _ = _ := integral_const_mul _ _

section TopFormZeroAlgebra
variable {V W ι κ : Type*} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W] [Fintype ι] [DecidableEq ι]
theorem alternating_eq_zero_of_apply_basis_eq_zero (d : Basis κ ℂ W) (b : Basis ι ℂ V)
    (A : V [⋀^ι]→ₗ[ℂ] W) (hA : A b = 0) : A = 0 := by
  apply AlternatingMap.ext
  intro w
  apply d.ext_elem
  intro α
  have hf : ((d.coord α).compAlternatingMap A) = 0 :=
    (AlternatingMap.map_basis_eq_zero_iff b _).mp (by
      simp only [LinearMap.compAlternatingMap_apply, hA, map_zero])
  have ht := congrArg (fun f : V [⋀^ι]→ₗ[ℂ] ℂ => f w) hf
  simpa only [LinearMap.compAlternatingMap_apply, Basis.coord_apply, AlternatingMap.zero_apply,
    map_zero, Finsupp.zero_apply] using ht
end TopFormZeroAlgebra

theorem topFormValue_eq_zero_iff (u : NQForm E 0) (a x : M.Carrier)
    (hx : x ∈ (extChartAt (ComplexModel n) a).source) :
    topFormValue E u a x = 0 ↔ u x = (0 : NQForm E 0) x := by
  constructor
  · intro hz
    have hv : (u x).1 Fin.elim0 (chartFrameBasis a x hx) = topFormValue E u a x := by
      unfold topFormValue
      congr 1
      funext i
      exact chartFrameBasis_apply a x hx i
    have hA : (u x).1 Fin.elim0 = 0 :=
      alternating_eq_zero_of_apply_basis_eq_zero (Module.Free.chooseBasis ℂ (E x))
        (chartFrameBasis a x hx) _ (by rw [hv]; exact hz)
    apply Subtype.ext
    rw [nqForm_zero_apply]
    apply AlternatingMap.ext
    intro w
    have hw : w = Fin.elim0 := Subsingleton.elim _ _
    rw [hw, hA]
    rfl
  · intro hu
    unfold topFormValue
    rw [congrArg Subtype.val hu, nqForm_zero_apply]
    simp

theorem formNormSq_top_eq_zero_iff (g : HermitianField M) (h : Metric E)
    (u : NQForm E 0) (x : M.Carrier) :
    BundleDbar.formNormSq (r := r) E g h u x = 0 ↔ u x = (0 : NQForm E 0) x := by
  rw [formNormSq_top_factor, topCoefficientNormSq_eq_value]
  have hd : 0 < (gMat g x)⁻¹.det.re := (Complex.pos_iff.mp (gMat_posDef g x).inv.det_pos).1
  constructor
  · intro hz
    have hv := (mul_eq_zero.mp hz).resolve_left (ne_of_gt hd)
    exact (topFormValue_eq_zero_iff E u x x (mem_extChartAt_source x)).mp
      (((h x).positive_definite _).2.mp hv)
  · intro hu
    have hv := (topFormValue_eq_zero_iff E u x x (mem_extChartAt_source x)).mpr hu
    rw [hv, ((h x).positive_definite 0).2.mpr rfl, mul_zero]

theorem weightedNormSq_top_eq_zero_iff (g : Yau.SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (h : Metric E)
    (hh : BundleDbar.SmoothMetric (r := r) E h) (φ : M.Carrier → ℝ) (hφ : SmoothFn φ)
    (u : NQForm E 0) (hu : LocallyL2 (r := r) E u) :
    weightedNormSq (r := r) E g.form h μ φ u = 0 ↔ ∀ᵐ x ∂μ, u x = (0 : NQForm E 0) x := by
  have hw : Measurable (fun x => Real.exp (-φ x)) :=
    (Real.continuous_exp.comp (L18Aux.continuous_of_smoothFn hφ).neg).measurable
  have hm : AEMeasurable (fun x => ENNReal.ofReal
      (BundleDbar.formNormSq (r := r) E g.form h u x * Real.exp (-φ x))) μ :=
    ENNReal.measurable_ofReal.comp_aemeasurable
      ((formNormSq_top_aemeasurable E g μ hμ h hh u hu).mul hw.aemeasurable)
  unfold weightedNormSq
  rw [lintegral_eq_zero_iff' hm]
  constructor
  · intro hz
    filter_upwards [hz] with x hx
    have hle := ENNReal.ofReal_eq_zero.mp hx
    have hnn := mul_nonneg (formNormSq_top_nonneg (r := r) E g.form h u x) (Real.exp_pos (-φ x)).le
    have hn : BundleDbar.formNormSq (r := r) E g.form h u x = 0 :=
      (mul_eq_zero.mp (le_antisymm hle hnn)).resolve_right (ne_of_gt (Real.exp_pos _))
    exact (formNormSq_top_eq_zero_iff (r := r) E g.form h u x).mp hn
  · intro hz
    filter_upwards [hz] with x hx
    have hn := (formNormSq_top_eq_zero_iff (r := r) E g.form h u x).mpr hx
    simp only [hn, zero_mul, ENNReal.ofReal_zero, Pi.zero_apply]
def WeightedTopSection (g : Yau.SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (h : Metric E)
    (hh : BundleDbar.SmoothMetric (r := r) E h) (φ : M.Carrier → ℝ) (hφ : SmoothFn φ) : Type :=
  weightedTopFormSubmodule (r := r) E g μ hμ h hh φ hφ

variable (g : Yau.SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
  (h : Metric E) (hh : BundleDbar.SmoothMetric (r := r) E h) (φ : M.Carrier → ℝ) (hφ : SmoothFn φ)

instance weightedTopSectionAddCommGroup : AddCommGroup (WeightedTopSection E g μ hμ h hh φ hφ) :=
  (weightedTopFormSubmodule (r := r) E g μ hμ h hh φ hφ).addCommGroup

instance weightedTopSectionModule : Module ℂ (WeightedTopSection E g μ hμ h hh φ hφ) :=
  (weightedTopFormSubmodule (r := r) E g μ hμ h hh φ hφ).module

instance weightedTopSectionSeminormedAddCommGroup :
    SeminormedAddCommGroup (WeightedTopSection E g μ hμ h hh φ hφ) := by
  letI : PreInnerProductSpace.Core ℂ (WeightedTopSection E g μ hμ h hh φ hφ) :=
    weightedTopFormPreInner E g μ hμ h hh φ hφ
  exact InnerProductSpace.Core.toSeminormedAddCommGroup (𝕜 := ℂ)

instance weightedTopSectionInnerProductSpace :
    InnerProductSpace ℂ (WeightedTopSection E g μ hμ h hh φ hφ) :=
  InnerProductSpace.ofCore (weightedTopFormPreInner E g μ hμ h hh φ hφ)

def WeightedTopSection.toForm (u : WeightedTopSection E g μ hμ h hh φ hφ) : NQForm E 0 := u.1

theorem WeightedTopSection.toForm_weightedL2 (u : WeightedTopSection E g μ hμ h hh φ hφ) :
    WeightedL2 (r := r) E g.form h μ φ (u.toForm E g μ hμ h hh φ hφ) := u.2

theorem WeightedTopSection.toForm_sub (u v : WeightedTopSection E g μ hμ h hh φ hφ) :
    (u - v).toForm E g μ hμ h hh φ hφ =
      u.toForm E g μ hμ h hh φ hφ - v.toForm E g μ hμ h hh φ hφ := rfl

theorem weightedTopSection_inner_eq (u v : WeightedTopSection E g μ hμ h hh φ hφ) :
    inner ℂ u v = weightedTopInner E g.form μ h φ
      (u.toForm E g μ hμ h hh φ hφ) (v.toForm E g μ hμ h hh φ hφ) := rfl

theorem weightedTopSection_norm_sq (u : WeightedTopSection E g μ hμ h hh φ hφ) :
    ‖u‖ ^ 2 = (weightedNormSq (r := r) E g.form h μ φ (u.toForm E g μ hμ h hh φ hφ)).toReal := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), weightedTopSection_inner_eq]
  change (weightedTopInner E g.form μ h φ u.1 u.1).re = (weightedNormSq (r := r) E g.form h μ φ u.1).toReal
  have hp := weightedTopPairing_integrable E g μ hμ h hh φ hφ u.1 u.1 u.2 u.2
  have hr : (weightedTopInner E g.form μ h φ u.1 u.1).re =
      ∫ x, BundleDbar.formNormSq (r := r) E g.form h u.1 x * Real.exp (-φ x) ∂μ := by
    calc
      _ = ∫ x, (weightedTopPairing E g.form h φ u.1 u.1 x).re ∂μ := by
        simpa only [weightedTopInner, RCLike.re_eq_complex_re] using (integral_re (𝕜 := ℂ) hp).symm
      _ = _ := integral_congr_ae (Filter.Eventually.of_forall fun x => weightedTopPairing_self_re (r := r) E g.form h φ u.1 x)
  rw [hr, weightedNormSq_top_eq_ofReal_integral E g μ hμ h hh φ hφ u.1 u.2,
    ENNReal.toReal_ofReal (integral_nonneg fun x =>
      mul_nonneg (formNormSq_top_nonneg E g.form h u.1 x) (Real.exp_pos _).le)]

theorem weightedTopSection_norm_eq_zero_iff (u : WeightedTopSection E g μ hμ h hh φ hφ) :
    ‖u‖ = 0 ↔ ∀ᵐ x ∂μ, u.toForm E g μ hμ h hh φ hφ x = (0 : NQForm E 0) x := by
  have hsq := weightedTopSection_norm_sq E g μ hμ h hh φ hφ u
  change ‖u‖ ^ 2 = (weightedNormSq (r := r) E g.form h μ φ u.1).toReal at hsq
  constructor
  · intro hn
    have hreal : (weightedNormSq (r := r) E g.form h μ φ u.1).toReal = 0 := by
      rw [← hsq, hn]
      simp
    have hz : weightedNormSq (r := r) E g.form h μ φ u.1 = 0 := by
      have ht := congrArg ENNReal.ofReal hreal
      rw [ENNReal.ofReal_toReal u.2.2.ne, ENNReal.ofReal_zero] at ht
      exact ht
    exact (weightedNormSq_top_eq_zero_iff E g μ hμ h hh φ hφ u.1 u.2.1).mp hz
  · intro hu
    have hz := (weightedNormSq_top_eq_zero_iff E g μ hμ h hh φ hφ u.1 u.2.1).mpr hu
    have hn : ‖u‖ ^ 2 = 0 := by rw [hsq, hz]; simp
    nlinarith [norm_nonneg u]

theorem nqForm_sub_apply {q : ℕ} (u v : NQForm E q) (x : M.Carrier) :
    ((u - v) x).1 = (u x).1 - (v x).1 := rfl

theorem weightedTopSection_norm_sub_eq_zero_iff (u v : WeightedTopSection E g μ hμ h hh φ hφ) :
    ‖u - v‖ = 0 ↔ ∀ᵐ x ∂μ, u.toForm E g μ hμ h hh φ hφ x = v.toForm E g μ hμ h hh φ hφ x := by
  rw [weightedTopSection_norm_eq_zero_iff]
  apply Filter.eventually_congr
  exact Filter.Eventually.of_forall fun x => by
    simp only [Subtype.ext_iff, WeightedTopSection.toForm_sub, nqForm_sub_apply, nqForm_zero_apply, sub_eq_zero]

/-- Separated completion of the actual finite weighted top forms.
Representing its arbitrary points by tensor sections remains a separate obligation. -/
abbrev WeightedTopHilbert := UniformSpace.Completion (WeightedTopSection E g μ hμ h hh φ hφ)

def realizeWeightedTopSection (u : WeightedTopSection E g μ hμ h hh φ hφ) :
    WeightedTopHilbert E g μ hμ h hh φ hφ := u

theorem realizeWeightedTopSection_inner (u v : WeightedTopSection E g μ hμ h hh φ hφ) :
    inner ℂ (realizeWeightedTopSection E g μ hμ h hh φ hφ u)
      (realizeWeightedTopSection E g μ hμ h hh φ hφ v) =
        weightedTopInner E g.form μ h φ (u.toForm E g μ hμ h hh φ hφ) (v.toForm E g μ hμ h hh φ hφ) :=
  UniformSpace.Completion.inner_coe u v

theorem realizeWeightedTopSection_norm_sq (u : WeightedTopSection E g μ hμ h hh φ hφ) :
    ‖realizeWeightedTopSection E g μ hμ h hh φ hφ u‖ ^ 2 =
      (weightedNormSq (r := r) E g.form h μ φ (u.toForm E g μ hμ h hh φ hφ)).toReal := by
  rw [realizeWeightedTopSection, UniformSpace.Completion.norm_coe, weightedTopSection_norm_sq]

theorem realizeWeightedTopSection_eq_iff_ae (u v : WeightedTopSection E g μ hμ h hh φ hφ) :
    realizeWeightedTopSection E g μ hμ h hh φ hφ u = realizeWeightedTopSection E g μ hμ h hh φ hφ v ↔
      ∀ᵐ x ∂μ, u.toForm E g μ hμ h hh φ hφ x = v.toForm E g μ hμ h hh φ hφ x := by
  calc
    _ ↔ ‖realizeWeightedTopSection E g μ hμ h hh φ hφ u - realizeWeightedTopSection E g μ hμ h hh φ hφ v‖ = 0 := by
      simp only [norm_eq_zero, sub_eq_zero]
    _ ↔ ‖u - v‖ = 0 := by
      change ‖(u : UniformSpace.Completion (WeightedTopSection E g μ hμ h hh φ hφ)) -
        (v : UniformSpace.Completion (WeightedTopSection E g μ hμ h hh φ hφ))‖ = 0 ↔ _
      rw [← UniformSpace.Completion.coe_sub, UniformSpace.Completion.norm_coe]
    _ ↔ _ := weightedTopSection_norm_sub_eq_zero_iff E g μ hμ h hh φ hφ u v

theorem realizeWeightedTopSection_denseRange : DenseRange (realizeWeightedTopSection E g μ hμ h hh φ hφ) :=
  UniformSpace.Completion.denseRange_coe

theorem weightedTopHilbert_complete : CompleteSpace (WeightedTopHilbert E g μ hμ h hh φ hφ) := inferInstance


/-- The original frozen a.e. quotient embeds densely with its actual integral norm. -/
def realizeWeightedTopClass : WeightedL2Space (r := r) E 0 g.form h μ φ →
    WeightedTopHilbert E g μ hμ h hh φ hφ :=
  Quotient.lift
    (fun u : {u : NQForm E 0 // WeightedL2 (r := r) E g.form h μ φ u} =>
      realizeWeightedTopSection E g μ hμ h hh φ hφ u)
    (fun u v huv => (realizeWeightedTopSection_eq_iff_ae E g μ hμ h hh φ hφ u v).mpr huv)

theorem realizeWeightedTopClass_mk
    (u : {u : NQForm E 0 // WeightedL2 (r := r) E g.form h μ φ u}) :
    realizeWeightedTopClass E g μ hμ h hh φ hφ (Quotient.mk _ u) =
      realizeWeightedTopSection E g μ hμ h hh φ hφ u := rfl

theorem realizeWeightedTopClass_injective : Function.Injective (realizeWeightedTopClass E g μ hμ h hh φ hφ) := by
  intro u v
  refine Quotient.inductionOn₂ u v ?_
  intro u₀ v₀ heq
  apply Quotient.sound
  exact (realizeWeightedTopSection_eq_iff_ae E g μ hμ h hh φ hφ u₀ v₀).mp heq

theorem realizeWeightedTopClass_denseRange : DenseRange (realizeWeightedTopClass E g μ hμ h hh φ hφ) := by
  apply (realizeWeightedTopSection_denseRange E g μ hμ h hh φ hφ).mono
  rintro _ ⟨u, rfl⟩
  exact ⟨Quotient.mk _ u, rfl⟩

def weightedTopClassNormSq (g₀ : HermitianField M) (μ₀ : Measure M.Carrier)
    (h₀ : Metric E) (φ₀ : M.Carrier → ℝ) : WeightedL2Space (r := r) E 0 g₀ h₀ μ₀ φ₀ → ℝ≥0∞ :=
  Quotient.lift
    (fun u : {u : NQForm E 0 // WeightedL2 (r := r) E g₀ h₀ μ₀ φ₀ u} =>
      weightedNormSq (r := r) E g₀ h₀ μ₀ φ₀ u.1)
    (fun u v huv => weightedNormSq_congr_ae (r := r) E g₀ h₀ μ₀ φ₀ u.1 v.1 huv)

theorem weightedTopClassNormSq_lt_top (g₀ : HermitianField M) (μ₀ : Measure M.Carrier)
    (h₀ : Metric E) (φ₀ : M.Carrier → ℝ) (u : WeightedL2Space (r := r) E 0 g₀ h₀ μ₀ φ₀) :
    weightedTopClassNormSq E g₀ μ₀ h₀ φ₀ u < ⊤ := by
  refine Quotient.inductionOn u ?_
  intro u₀
  exact u₀.2.2

theorem realizeWeightedTopClass_norm_sq (u : WeightedL2Space (r := r) E 0 g.form h μ φ) :
    ‖realizeWeightedTopClass E g μ hμ h hh φ hφ u‖ ^ 2 =
      (weightedTopClassNormSq E g.form μ h φ u).toReal := by
  refine Quotient.inductionOn u ?_
  intro u₀
  exact realizeWeightedTopSection_norm_sq E g μ hμ h hh φ hφ u₀

end Yau.LeafProofs.L14Aux


namespace Yau.LeafProofs.L14Aux

open BundleDbar

theorem matrix_coefficient_le_inverse_diagonal {r : ℕ}
    (H : Matrix (Fin r) (Fin r) ℂ) (hH : H.PosDef) (v : Fin r → ℂ) (α : Fin r) :
    ‖v α‖ ^ 2 ≤ (H⁻¹ α α).re * (star v ⬝ᵥ H *ᵥ v).re := by
  have hcancel : H⁻¹ *ᵥ (H *ᵥ v) = v := by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (hH.isUnit.map Matrix.detMonoidHom), Matrix.one_mulVec]
  have hx0 : star (Pi.single α (1 : ℂ)) ⬝ᵥ H⁻¹ *ᵥ (H *ᵥ v) = v α := by
    rw [hcancel]
    simp
  have hx1 : star (Pi.single α (1 : ℂ)) ⬝ᵥ H⁻¹ *ᵥ (Pi.single α 1) = H⁻¹ α α := by simp
  have hy1 : star (H *ᵥ v) ⬝ᵥ H⁻¹ *ᵥ (H *ᵥ v) = star v ⬝ᵥ H *ᵥ v := by
    rw [hcancel, Matrix.star_mulVec, hH.isHermitian.eq, ← Matrix.dotProduct_mulVec]
  have hc := hH.inv.star_dotProduct_mulVec_mul_le (Pi.single α 1) (H *ᵥ v)
  rw [hx0, hx1, hy1] at hc
  have hr := (Complex.le_def.mp hc).1
  have hi : (H⁻¹ α α).im = 0 := (Complex.nonneg_iff.mp (hH.inv.posSemidef.diag_nonneg (i := α))).2.symm
  simpa only [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re,
    Complex.normSq_eq_norm_sq, Complex.mul_re, hi, zero_mul, sub_zero] using hr

variable {n r : ℕ} {M : ComplexManifold n}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

def chartTopCoefficientNormSq (h : Metric E) (u : NQForm E 0)
    (a : M.Carrier) (z : ComplexVector n) : ℝ :=
  (∑ α, ∑ β, star (coefficients (r := r) E u a z Fin.elim0 α) *
    BundleDbar.metricMatrix (r := r) E h a z α β *
      coefficients (r := r) E u a z Fin.elim0 β).re

theorem chartTopCoefficientNormSq_eq_value (h : Metric E) (u : NQForm E 0)
    (a : M.Carrier) (z : ComplexVector n) (hz : z ∈ localDomain (r := r) E a) :
    chartTopCoefficientNormSq (r := r) E h u a z =
      ((h (chartInv a z)).toFun (topFormValue E u a (chartInv a z))
        (topFormValue E u a (chartInv a z))).re := by
  unfold chartTopCoefficientNormSq
  simp_rw [coefficients_topFormValue]
  exact congrArg Complex.re (metricMatrix_pairing E h a z hz _ _)

theorem top_coefficient_le_inverse_diagonal (h : Metric E) (u : NQForm E 0)
    (a : M.Carrier) (z : ComplexVector n) (hz : z ∈ localDomain (r := r) E a) (α : Fin r) :
    ‖coefficients (r := r) E u a z Fin.elim0 α‖ ^ 2 ≤
      ((BundleDbar.metricMatrix (r := r) E h a z)⁻¹ α α).re *
        chartTopCoefficientNormSq (r := r) E h u a z := by
  have hc := matrix_coefficient_le_inverse_diagonal _ (metricMatrix_posDef E h a z hz)
    (fun β => coefficients (r := r) E u a z Fin.elim0 β) α
  simpa only [chartTopCoefficientNormSq, dotProduct, Matrix.mulVec, Pi.star_apply,
    Finset.mul_sum, mul_assoc] using hc

theorem compact_top_coefficient_weight_bound (h : Metric E)
    (hh : BundleDbar.SmoothMetric (r := r) E h) (φ : M.Carrier → ℝ) (hφ : SmoothFn φ)
    (a : M.Carrier) (K : Set (ComplexVector n)) (hK : IsCompact K)
    (hsub : K ⊆ localDomain (r := r) E a) (α : Fin r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : NQForm E 0) z, z ∈ K →
      ‖coefficients (r := r) E u a z Fin.elim0 α‖ ^ 2 ≤
        C * (chartTopCoefficientNormSq (r := r) E h u a z * Real.exp (-φ (chartInv a z))) := by
  have hdet : ∀ z ∈ localDomain (r := r) E a,
      (BundleDbar.metricMatrix (r := r) E h a z).det ≠ 0 := fun z hz =>
    ((metricMatrix_posDef E h a z hz).isUnit.map Matrix.detMonoidHom).ne_zero
  have hi : ContinuousOn (fun z => ((BundleDbar.metricMatrix (r := r) E h a z)⁻¹ α α).re)
      (localDomain (r := r) E a) :=
    Complex.continuous_re.comp_continuousOn (L18Aux.contDiffOn_matrix_inv (hh a) hdet α α).continuousOn
  have he : ContinuousOn (fun z => Real.exp (inChart a φ z)) (localDomain (r := r) E a) :=
    Real.continuous_exp.comp_continuousOn ((hφ a).continuousOn.mono Set.inter_subset_left)
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn ((hi.mul he).mono hsub)
  refine ⟨max B 0, le_max_right _ _, ?_⟩
  intro u z hz
  have hzdom := hsub hz
  have hC : ((BundleDbar.metricMatrix (r := r) E h a z)⁻¹ α α).re * Real.exp (inChart a φ z) ≤ max B 0 := by
    apply le_trans (le_abs_self _)
    exact (show |((BundleDbar.metricMatrix (r := r) E h a z)⁻¹ α α).re * Real.exp (inChart a φ z)| ≤ B from
      by
        have hb : ‖((BundleDbar.metricMatrix (r := r) E h a z)⁻¹ α α).re * Real.exp (inChart a φ z)‖ ≤ B := hB z hz
        simpa only [Real.norm_eq_abs] using hb).trans (le_max_left _ _)
  have hq : 0 ≤ chartTopCoefficientNormSq (r := r) E h u a z := by
    rw [chartTopCoefficientNormSq_eq_value E h u a z hzdom]
    exact ((h (chartInv a z)).positive_definite _).1
  have hw : Real.exp (inChart a φ z) * Real.exp (-φ (chartInv a z)) = 1 := by
    change Real.exp (φ (chartInv a z)) * Real.exp (-φ (chartInv a z)) = 1
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  calc
    _ ≤ ((BundleDbar.metricMatrix (r := r) E h a z)⁻¹ α α).re * chartTopCoefficientNormSq (r := r) E h u a z :=
      top_coefficient_le_inverse_diagonal E h u a z hzdom α
    _ = (((BundleDbar.metricMatrix (r := r) E h a z)⁻¹ α α).re * Real.exp (inChart a φ z)) *
        (chartTopCoefficientNormSq (r := r) E h u a z * Real.exp (-φ (chartInv a z))) := by
      calc
        _ = (((BundleDbar.metricMatrix (r := r) E h a z)⁻¹ α α).re * chartTopCoefficientNormSq (r := r) E h u a z) *
            (Real.exp (inChart a φ z) * Real.exp (-φ (chartInv a z))) := by rw [hw, mul_one]
        _ = _ := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hC (mul_nonneg hq (Real.exp_pos _).le)


theorem map_chartInvExtension_volume (g : HermitianField M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g μ) (a : M.Carrier) :
    μ.restrict (bundleChartSource (r := r) E a) =
      (((lebesgueC n).restrict (localDomain (r := r) E a)).withDensity
        (fun z => ENNReal.ofReal (Real.sqrt (realMetricFn g a z).det))).map (chartInvExtension a) := by
  calc
    _ = ((μ.restrict (bundleChartSource (r := r) E a)).map (chartPtExtension a)).map (chartInvExtension a) := by
      rw [Measure.map_map (chartInvExtension_measurable a) (chartPtExtension_measurable a)]
      have he : (chartInvExtension a ∘ chartPtExtension a) =ᵐ[
          μ.restrict (bundleChartSource (r := r) E a)] id := by
        filter_upwards [ae_restrict_mem (bundleChartSource_isOpen (r := r) E a).measurableSet] with x hx
        change chartInvExtension a (chartPtExtension a x) = x
        have hxt : chartPt a x ∈ chartTarget a := (extChartAt (ComplexModel n) a).map_source hx.1
        rw [chartPtExtension, if_pos hx.1, chartInvExtension, if_pos hxt,
          chartInv_chartPt_of_mem a x (by simpa only [extChartAt_source] using hx.1)]
      rw [Measure.map_congr he, Measure.map_id]
    _ = _ := by rw [map_chartPtExtension_volume (r := r) E g μ hμ a]

theorem lintegral_bundleChart_volume (g : Yau.SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (a : M.Carrier)
    (F : M.Carrier → ℝ≥0∞) (hF : AEMeasurable F μ) :
    (∫⁻ x in bundleChartSource (r := r) E a, F x ∂μ) =
      ∫⁻ z in localDomain (r := r) E a,
        ENNReal.ofReal (Real.sqrt (realMetricFn g.form a z).det) * F (chartInv a z) ∂lebesgueC n := by
  let ν := (lebesgueC n).restrict (localDomain (r := r) E a)
  let d := fun z => ENNReal.ofReal (Real.sqrt (realMetricFn g.form a z).det)
  have hd : AEMeasurable d ν := ENNReal.measurable_ofReal.comp_aemeasurable
    (((L18Aux.volumeDensity_continuousOn g a).mono Set.inter_subset_left).aemeasurable
      (localDomain_isOpen E a).measurableSet)
  have hFm : AEMeasurable F ((ν.withDensity d).map (chartInvExtension a)) := by
    rw [← map_chartInvExtension_volume (r := r) E g.form μ hμ a]
    exact hF.mono_measure Measure.restrict_le_self
  have hFc : AEMeasurable (F ∘ chartInvExtension a) (ν.withDensity d) :=
    hFm.comp_measurable (chartInvExtension_measurable a)
  rw [map_chartInvExtension_volume (r := r) E g.form μ hμ a,
    lintegral_map' hFm (chartInvExtension_measurable a).aemeasurable]
  change (∫⁻ z, (F ∘ chartInvExtension a) z ∂ν.withDensity d) = _
  rw [lintegral_withDensity_eq_lintegral_mul₀' hd hFc]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem (localDomain_isOpen E a).measurableSet] with z hz
  change d z * F (chartInvExtension a z) = d z * F (chartInv a z)
  rw [chartInvExtension, if_pos hz.1]

theorem weighted_top_chart_integral (g : Yau.SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (h : Metric E)
    (hh : BundleDbar.SmoothMetric (r := r) E h) (φ : M.Carrier → ℝ) (hφ : SmoothFn φ)
    (u : NQForm E 0) (hu : LocallyL2 (r := r) E u) (a : M.Carrier) :
    (∫⁻ x in bundleChartSource (r := r) E a,
      ENNReal.ofReal (BundleDbar.formNormSq (r := r) E g.form h u x * Real.exp (-φ x)) ∂μ) =
        ENNReal.ofReal ((2 : ℝ) ^ n) *
          ∫⁻ z in localDomain (r := r) E a,
            ENNReal.ofReal (chartTopCoefficientNormSq (r := r) E h u a z *
              Real.exp (-φ (chartInv a z))) ∂lebesgueC n := by
  have hw : Measurable (fun x => Real.exp (-φ x)) :=
    (Real.continuous_exp.comp (L18Aux.continuous_of_smoothFn hφ).neg).measurable
  have hm : AEMeasurable (fun x => ENNReal.ofReal (BundleDbar.formNormSq (r := r) E g.form h u x * Real.exp (-φ x))) μ := ENNReal.measurable_ofReal.comp_aemeasurable
    ((formNormSq_top_aemeasurable E g μ hμ h hh u hu).mul hw.aemeasurable)
  rw [lintegral_bundleChart_volume (r := r) E g μ hμ a _ hm,
    ← lintegral_const_mul' (ENNReal.ofReal ((2 : ℝ) ^ n))
      (fun z => ENNReal.ofReal (chartTopCoefficientNormSq (r := r) E h u a z * Real.exp (-φ (chartInv a z))))
      ENNReal.ofReal_ne_top]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem (localDomain_isOpen E a).measurableSet] with z hz
  rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg _), realMetricFn_sqrt_det g.form a z hz.1,
    formNormSq_top_inChart E g.form h u a z hz,
    ← ENNReal.ofReal_mul (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) n)]
  congr 1
  change ((2 : ℝ) ^ n * (hMat g.form a z).det.re) *
      (((hMat g.form a z).det.re)⁻¹ * chartTopCoefficientNormSq (r := r) E h u a z * Real.exp (-φ (chartInv a z))) = _
  field_simp [ne_of_gt (L18Aux.hMat_det_re_pos g.form a hz.1)]

theorem compact_top_coefficient_integral_bound (g : Yau.SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (h : Metric E)
    (hh : BundleDbar.SmoothMetric (r := r) E h) (φ : M.Carrier → ℝ) (hφ : SmoothFn φ)
    (a : M.Carrier) (K : Set (ComplexVector n)) (hK : IsCompact K)
    (hsub : K ⊆ localDomain (r := r) E a) (α : Fin r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : NQForm E 0, LocallyL2 (r := r) E u →
      (∫⁻ z in K, ENNReal.ofReal (‖coefficients (r := r) E u a z Fin.elim0 α‖ ^ 2) ∂lebesgueC n) ≤
        ENNReal.ofReal C * weightedNormSq (r := r) E g.form h μ φ u := by
  obtain ⟨C, hC, hbound⟩ := compact_top_coefficient_weight_bound E h hh φ hφ a K hK hsub α
  refine ⟨C, hC, ?_⟩
  intro u hu
  have hTwo : (1 : ℝ≥0∞) ≤ ENNReal.ofReal ((2 : ℝ) ^ n) := by
    have ht : (1 : ℝ) ≤ (2 : ℝ) ^ n := one_le_pow₀ (by norm_num)
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal ht
  have hnormal : (∫⁻ z in localDomain (r := r) E a,
      ENNReal.ofReal (chartTopCoefficientNormSq (r := r) E h u a z * Real.exp (-φ (chartInv a z))) ∂lebesgueC n) ≤
        weightedNormSq (r := r) E g.form h μ φ u := by
    calc
      _ = 1 * ∫⁻ z in localDomain (r := r) E a,
          ENNReal.ofReal (chartTopCoefficientNormSq (r := r) E h u a z * Real.exp (-φ (chartInv a z))) ∂lebesgueC n := by rw [one_mul]
      _ ≤ ENNReal.ofReal ((2 : ℝ) ^ n) * ∫⁻ z in localDomain (r := r) E a,
          ENNReal.ofReal (chartTopCoefficientNormSq (r := r) E h u a z * Real.exp (-φ (chartInv a z))) ∂lebesgueC n :=
        mul_le_mul_left hTwo _
      _ = _ := (weighted_top_chart_integral E g μ hμ h hh φ hφ u hu a).symm
      _ ≤ _ := setLIntegral_le_lintegral _ _
  calc
    _ ≤ ∫⁻ z in K, ENNReal.ofReal (C * (chartTopCoefficientNormSq (r := r) E h u a z *
        Real.exp (-φ (chartInv a z)))) ∂lebesgueC n := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem hK.measurableSet] with z hz
      exact ENNReal.ofReal_le_ofReal (hbound u z hz)
    _ = ENNReal.ofReal C * ∫⁻ z in K, ENNReal.ofReal (chartTopCoefficientNormSq (r := r) E h u a z *
        Real.exp (-φ (chartInv a z))) ∂lebesgueC n := by
      simp_rw [ENNReal.ofReal_mul hC]
      exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ _ := mul_le_mul_right ((lintegral_mono_set hsub).trans hnormal) _

end Yau.LeafProofs.L14Aux

namespace Yau.LeafProofs.L14Aux

open BundleDbar

theorem complex_toLp_norm_sq {X : Type*} [MeasurableSpace X] (ν : Measure X)
    (f : X → ℂ) (hf : MemLp f 2 ν) :
    ‖hf.toLp f‖ ^ 2 = (∫⁻ x, ENNReal.ofReal (‖f x‖ ^ 2) ∂ν).toReal := by
  have hi : Integrable (fun x => ‖f x‖ ^ 2) ν :=
    (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf
  calc
    _ = (inner ℂ (hf.toLp f) (hf.toLp f)).re := norm_sq_eq_re_inner (𝕜 := ℂ) _
    _ = ∫ x, (inner ℂ ((hf.toLp f) x) ((hf.toLp f) x)).re ∂ν := by
      simpa only [L2.inner_def, RCLike.re_eq_complex_re] using
        (integral_re (𝕜 := ℂ) (L2.integrable_inner (hf.toLp f) (hf.toLp f))).symm
    _ = ∫ x, ‖(hf.toLp f) x‖ ^ 2 ∂ν := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        change (inner ℂ ((hf.toLp f) x) ((hf.toLp f) x)).re = ‖(hf.toLp f) x‖ ^ 2
        exact (norm_sq_eq_re_inner (𝕜 := ℂ) ((hf.toLp f) x)).symm
    _ = ∫ x, ‖f x‖ ^ 2 ∂ν := integral_congr_ae (hf.coeFn_toLp.mono fun x hx => by
      change ‖(hf.toLp f) x‖ ^ 2 = ‖f x‖ ^ 2
      rw [hx])
    _ = _ := integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall fun x => sq_nonneg ‖f x‖) hi.aestronglyMeasurable

variable {n r : ℕ} {M : ComplexManifold n}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]
variable (g : Yau.SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
  (h : Metric E) (hh : BundleDbar.SmoothMetric (r := r) E h) (φ : M.Carrier → ℝ) (hφ : SmoothFn φ)
  (a : M.Carrier) (K : Set (ComplexVector n)) (hK : IsCompact K)
  (hsub : K ⊆ localDomain (r := r) E a) (α : Fin r)

def weightedTopLocalCoefficient (u : WeightedTopSection E g μ hμ h hh φ hφ) :
    Lp ℂ 2 ((lebesgueC n).restrict K) :=
  (locallyL2_coefficients_memLp E u.1 u.2.1 a Fin.elim0 α K hK hsub).toLp
    (fun z => coefficients (r := r) E u.1 a z Fin.elim0 α)

theorem weightedTopLocalCoefficient_ae (u : WeightedTopSection E g μ hμ h hh φ hφ) :
    weightedTopLocalCoefficient E g μ hμ h hh φ hφ a K hK hsub α u =ᵐ[(lebesgueC n).restrict K]
      (fun z => coefficients (r := r) E u.1 a z Fin.elim0 α) := MemLp.coeFn_toLp _

def weightedTopLocalCoefficientLinear :
    WeightedTopSection E g μ hμ h hh φ hφ →ₗ[ℂ] Lp ℂ 2 ((lebesgueC n).restrict K) where
  toFun := weightedTopLocalCoefficient E g μ hμ h hh φ hφ a K hK hsub α
  map_add' u v := by
    apply Lp.ext
    filter_upwards [weightedTopLocalCoefficient_ae E g μ hμ h hh φ hφ a K hK hsub α (u+v),
      weightedTopLocalCoefficient_ae E g μ hμ h hh φ hφ a K hK hsub α u,
      weightedTopLocalCoefficient_ae E g μ hμ h hh φ hφ a K hK hsub α v,
      Lp.coeFn_add (weightedTopLocalCoefficient E g μ hμ h hh φ hφ a K hK hsub α u)
        (weightedTopLocalCoefficient E g μ hμ h hh φ hφ a K hK hsub α v)] with z huv hu hv hadd
    rw [huv, hadd, Pi.add_apply, hu, hv]
    exact coefficients_add E u.1 v.1 a z Fin.elim0 α
  map_smul' c u := by
    change weightedTopLocalCoefficient E g μ hμ h hh φ hφ a K hK hsub α (c • u) =
      c • weightedTopLocalCoefficient E g μ hμ h hh φ hφ a K hK hsub α u
    apply Lp.ext
    filter_upwards [weightedTopLocalCoefficient_ae E g μ hμ h hh φ hφ a K hK hsub α (c • u),
      weightedTopLocalCoefficient_ae E g μ hμ h hh φ hφ a K hK hsub α u,
      Lp.coeFn_smul c (weightedTopLocalCoefficient E g μ hμ h hh φ hφ a K hK hsub α u)] with z hcu hu hsmul
    rw [hcu, hsmul, Pi.smul_apply, hu]
    exact coefficients_smul E c u.1 a z Fin.elim0 α

theorem weightedTopLocalCoefficient_norm_sq (u : WeightedTopSection E g μ hμ h hh φ hφ) :
    ‖weightedTopLocalCoefficient E g μ hμ h hh φ hφ a K hK hsub α u‖ ^ 2 =
      (∫⁻ z in K, ENNReal.ofReal (‖coefficients (r := r) E u.1 a z Fin.elim0 α‖ ^ 2) ∂lebesgueC n).toReal :=
  complex_toLp_norm_sq _ _ _

theorem weightedTopLocalCoefficient_bounded :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : WeightedTopSection E g μ hμ h hh φ hφ,
      ‖weightedTopLocalCoefficient E g μ hμ h hh φ hφ a K hK hsub α u‖ ≤ C * ‖u‖ := by
  obtain ⟨C, hC, hb⟩ := compact_top_coefficient_integral_bound E g μ hμ h hh φ hφ a K hK hsub α
  refine ⟨Real.sqrt C, Real.sqrt_nonneg C, ?_⟩
  intro u
  have hfin : ENNReal.ofReal C * weightedNormSq (r := r) E g.form h μ φ u.1 < ⊤ :=
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top u.2.2
  have hs : ‖weightedTopLocalCoefficient E g μ hμ h hh φ hφ a K hK hsub α u‖ ^ 2 ≤ C * ‖u‖ ^ 2 := by
    rw [weightedTopLocalCoefficient_norm_sq E g μ hμ h hh φ hφ a K hK hsub α]
    have ht := ENNReal.toReal_mono hfin.ne (hb u.1 u.2.1)
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC] at ht
    have hn := weightedTopSection_norm_sq E g μ hμ h hh φ hφ u
    change ‖u‖ ^ 2 = (weightedNormSq (r := r) E g.form h μ φ u.1).toReal at hn
    rwa [hn]
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg C) (norm_nonneg u))).mp
  calc
    _ ≤ C * ‖u‖ ^ 2 := hs
    _ = (Real.sqrt C * ‖u‖) ^ 2 := by rw [mul_pow, Real.sq_sqrt hC]

def weightedTopLocalCoefficientCLM :
    WeightedTopSection E g μ hμ h hh φ hφ →L[ℂ] Lp ℂ 2 ((lebesgueC n).restrict K) :=
  (weightedTopLocalCoefficientLinear E g μ hμ h hh φ hφ a K hK hsub α).mkContinuousOfExistsBound
    (by
      obtain ⟨C, _, hC⟩ := weightedTopLocalCoefficient_bounded E g μ hμ h hh φ hφ a K hK hsub α
      exact ⟨C, hC⟩)

theorem weightedTopLocalCoefficientCLM_apply (u : WeightedTopSection E g μ hμ h hh φ hφ) :
    weightedTopLocalCoefficientCLM E g μ hμ h hh φ hφ a K hK hsub α u =
      weightedTopLocalCoefficient E g μ hμ h hh φ hφ a K hK hsub α u := rfl

/-- The local coefficient of a computed weighted Hilbert element is obtained
by extending the actual coefficient map into the complete local L² space. -/
def weightedTopHilbertLocalCoefficient :
    WeightedTopHilbert E g μ hμ h hh φ hφ →L[ℂ] Lp ℂ 2 ((lebesgueC n).restrict K) :=
  (weightedTopLocalCoefficientCLM E g μ hμ h hh φ hφ a K hK hsub α).fromCompletion

theorem weightedTopHilbertLocalCoefficient_realize (u : WeightedTopSection E g μ hμ h hh φ hφ) :
    weightedTopHilbertLocalCoefficient E g μ hμ h hh φ hφ a K hK hsub α
      (realizeWeightedTopSection E g μ hμ h hh φ hφ u) =
        weightedTopLocalCoefficient E g μ hμ h hh φ hφ a K hK hsub α u :=
  ContinuousLinearMap.fromCompletion_apply_coe _ u

theorem weightedTopHilbertLocalCoefficient_realize_ae (u : WeightedTopSection E g μ hμ h hh φ hφ) :
    weightedTopHilbertLocalCoefficient E g μ hμ h hh φ hφ a K hK hsub α
      (realizeWeightedTopSection E g μ hμ h hh φ hφ u) =ᵐ[(lebesgueC n).restrict K]
        (fun z => coefficients (r := r) E u.1 a z Fin.elim0 α) := by
  rw [weightedTopHilbertLocalCoefficient_realize E g μ hμ h hh φ hφ a K hK hsub α]
  exact weightedTopLocalCoefficient_ae E g μ hμ h hh φ hφ a K hK hsub α u


theorem weightedTopHilbertLocalCoefficient_restrict
    (K' : Set (ComplexVector n)) (hK' : IsCompact K')
    (hsub' : K' ⊆ localDomain (r := r) E a) (hKK' : K ⊆ K')
    (u : WeightedTopHilbert E g μ hμ h hh φ hφ) :
    Lp.LpToLpOfMeasureLeSMul (E := ℂ) (p := 2) (c := 1) (by simp)
      (show (lebesgueC n).restrict K ≤ (1 : ℝ≥0∞) • (lebesgueC n).restrict K' from
        by simpa only [one_smul] using Measure.restrict_mono hKK' (le_refl (lebesgueC n)))
      (weightedTopHilbertLocalCoefficient E g μ hμ h hh φ hφ a K' hK' hsub' α u) =
        weightedTopHilbertLocalCoefficient E g μ hμ h hh φ hφ a K hK hsub α u := by
  let hmeasure : (lebesgueC n).restrict K ≤ (1 : ℝ≥0∞) • (lebesgueC n).restrict K' :=
    by simpa only [one_smul] using Measure.restrict_mono hKK' (le_refl (lebesgueC n))
  let T := Lp.LpToLpOfMeasureLeSMul (E := ℂ) (p := 2) (c := 1) (by simp) hmeasure
  change T (weightedTopHilbertLocalCoefficient E g μ hμ h hh φ hφ a K' hK' hsub' α u) =
    weightedTopHilbertLocalCoefficient E g μ hμ h hh φ hφ a K hK hsub α u
  refine UniformSpace.Completion.induction_on u
    (isClosed_eq (T.continuous.comp (weightedTopHilbertLocalCoefficient E g μ hμ h hh φ hφ a K' hK' hsub' α).continuous)
      (weightedTopHilbertLocalCoefficient E g μ hμ h hh φ hφ a K hK hsub α).continuous) ?_
  intro v
  change T (weightedTopHilbertLocalCoefficient E g μ hμ h hh φ hφ a K' hK' hsub' α
      (realizeWeightedTopSection E g μ hμ h hh φ hφ v)) =
    weightedTopHilbertLocalCoefficient E g μ hμ h hh φ hφ a K hK hsub α
      (realizeWeightedTopSection E g μ hμ h hh φ hφ v)
  rw [weightedTopHilbertLocalCoefficient_realize E g μ hμ h hh φ hφ a K' hK' hsub' α,
    weightedTopHilbertLocalCoefficient_realize E g μ hμ h hh φ hφ a K hK hsub α]
  apply Lp.ext
  have hbig := (weightedTopLocalCoefficient_ae E g μ hμ h hh φ hφ a K' hK' hsub' α v).filter_mono
    (ae_mono (Measure.restrict_mono hKK' (le_refl (lebesgueC n))))
  filter_upwards [Lp.coeFn_LpToLpOfMeasureLeSMul (E := ℂ) (p := 2) (c := 1) (by simp) hmeasure
      (weightedTopLocalCoefficient E g μ hμ h hh φ hφ a K' hK' hsub' α v), hbig,
    weightedTopLocalCoefficient_ae E g μ hμ h hh φ hφ a K hK hsub α v] with z ht hb hs
  exact ht.trans (hb.trans hs.symm)

theorem weightedTopHilbertLocalCoefficient_ae_restrict
    (K' : Set (ComplexVector n)) (hK' : IsCompact K')
    (hsub' : K' ⊆ localDomain (r := r) E a) (hKK' : K ⊆ K')
    (u : WeightedTopHilbert E g μ hμ h hh φ hφ) :
    weightedTopHilbertLocalCoefficient E g μ hμ h hh φ hφ a K' hK' hsub' α u =ᵐ[(lebesgueC n).restrict K]
      weightedTopHilbertLocalCoefficient E g μ hμ h hh φ hφ a K hK hsub α u := by
  let hmeasure : (lebesgueC n).restrict K ≤ (1 : ℝ≥0∞) • (lebesgueC n).restrict K' :=
    by simpa only [one_smul] using Measure.restrict_mono hKK' (le_refl (lebesgueC n))
  have hcoe := Lp.coeFn_LpToLpOfMeasureLeSMul (E := ℂ) (p := 2) (c := 1) (by simp) hmeasure
    (weightedTopHilbertLocalCoefficient E g μ hμ h hh φ hφ a K' hK' hsub' α u)
  rw [weightedTopHilbertLocalCoefficient_restrict E g μ hμ h hh φ hφ a K hK hsub α K' hK' hsub' hKK' u] at hcoe
  exact hcoe.symm


end Yau.LeafProofs.L14Aux

namespace Yau.LeafProofs.L14Aux

open BundleDbar

theorem compatibleLocalLp_glue {X : Type*} [MeasurableSpace X] (ν : Measure X)
    (s : ℕ → Set X) (hs : ∀ j, MeasurableSet (s j))
    (v : ∀ j, Lp ℂ 2 (ν.restrict (s j)))
    (hcompat : ∀ i j, i ≤ j → (v i : X → ℂ) =ᵐ[ν.restrict (s i)] (v j : X → ℂ)) :
    ∃ f : X → ℂ, ∀ j, MemLp f 2 (ν.restrict (s j)) ∧
      f =ᵐ[ν.restrict (s j)] (v j : X → ℂ) := by
  classical
  let f : X → ℂ := fun x => if hx : ∃ j, x ∈ s j then v (Nat.find hx) x else 0
  refine ⟨f, ?_⟩
  intro j
  have hpair : ∀ᵐ x ∂ν, ∀ i, i ≤ j → x ∈ s i → v i x = v j x := by
    apply ae_all_iff.mpr
    intro i
    by_cases hij : i ≤ j
    · exact (ae_imp_of_ae_restrict (hcompat i j hij)).mono fun x hx _ => hx
    · exact Filter.Eventually.of_forall fun x hx => False.elim (hij hx)
  have heq : f =ᵐ[ν.restrict (s j)] (v j : X → ℂ) := by
    filter_upwards [hpair.filter_mono (ae_mono Measure.restrict_le_self), ae_restrict_mem (hs j)] with x hx hxj
    have hex : ∃ i, x ∈ s i := ⟨j, hxj⟩
    change (if h : ∃ i, x ∈ s i then v (Nat.find h) x else 0) = v j x
    rw [dif_pos hex]
    exact hx (Nat.find hex) (Nat.find_min' hex hxj) (Nat.find_spec hex)
  exact ⟨(memLp_congr_ae heq).mpr (Lp.memLp (v j)), heq⟩

variable {n r : ℕ} {M : ComplexManifold n}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

def localDomainCompactExhaustion (a : M.Carrier) : CompactExhaustion (localDomain (r := r) E a) := by
  letI : LocallyCompactSpace (localDomain (r := r) E a) := (localDomain_isOpen E a).locallyCompactSpace
  exact CompactExhaustion.choice _

def localDomainCompactSet (a : M.Carrier) (j : ℕ) : Set (ComplexVector n) :=
  Subtype.val '' (localDomainCompactExhaustion (r := r) E a j)

theorem localDomainCompactSet_isCompact (a : M.Carrier) (j : ℕ) :
    IsCompact (localDomainCompactSet (r := r) E a j) :=
  (localDomainCompactExhaustion E a).isCompact j |>.image continuous_subtype_val

theorem localDomainCompactSet_subset (a : M.Carrier) (j : ℕ) :
    localDomainCompactSet (r := r) E a j ⊆ localDomain (r := r) E a := by
  rintro z ⟨x, _, rfl⟩
  exact x.2

theorem localDomainCompactSet_mono (a : M.Carrier) : Monotone (localDomainCompactSet (r := r) E a) := by
  intro i j hij
  exact Set.image_mono ((localDomainCompactExhaustion E a).subset hij)

theorem iUnion_localDomainCompactSet (a : M.Carrier) :
    (⋃ j, localDomainCompactSet (r := r) E a j) = localDomain (r := r) E a := by
  apply Set.Subset.antisymm
  · exact Set.iUnion_subset fun j => localDomainCompactSet_subset E a j
  · intro z hz
    obtain ⟨j, hj⟩ := (localDomainCompactExhaustion E a).exists_mem ⟨z, hz⟩
    exact Set.mem_iUnion.mpr ⟨j, ⟨⟨z, hz⟩, hj, rfl⟩⟩

theorem localDomainCompactSet_covers_compact (a : M.Carrier)
    (K : Set (ComplexVector n)) (hK : IsCompact K) (hsub : K ⊆ localDomain (r := r) E a) :
    ∃ j, K ⊆ localDomainCompactSet (r := r) E a j := by
  have hpre : IsCompact ((Subtype.val : localDomain (r := r) E a → ComplexVector n) ⁻¹' K) :=
    Topology.IsEmbedding.subtypeVal.isCompact_preimage' hK (by simpa only [Subtype.range_coe] using hsub)
  obtain ⟨j, hj⟩ := (localDomainCompactExhaustion E a).exists_superset_of_isCompact hpre
  refine ⟨j, ?_⟩
  intro z hz
  exact ⟨⟨z, hsub hz⟩, hj hz, rfl⟩

variable (g : Yau.SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
  (h : Metric E) (hh : BundleDbar.SmoothMetric (r := r) E h) (φ : M.Carrier → ℝ) (hφ : SmoothFn φ)

theorem weightedTopHilbert_exists_chartCoefficient
    (u : WeightedTopHilbert E g μ hμ h hh φ hφ) (a : M.Carrier) (α : Fin r) :
    ∃ f : ComplexVector n → ℂ,
      AEStronglyMeasurable f ((lebesgueC n).restrict (localDomain (r := r) E a)) ∧
      ∀ (K : Set (ComplexVector n)) (hK : IsCompact K)
          (hsub : K ⊆ localDomain (r := r) E a),
        MemLp f 2 ((lebesgueC n).restrict K) ∧
        f =ᵐ[(lebesgueC n).restrict K]
          weightedTopHilbertLocalCoefficient E g μ hμ h hh φ hφ a K hK hsub α u := by
  let s := localDomainCompactSet (r := r) E a
  let v := fun j => weightedTopHilbertLocalCoefficient E g μ hμ h hh φ hφ a (s j)
    (localDomainCompactSet_isCompact E a j) (localDomainCompactSet_subset E a j) α u
  have hcompat : ∀ i j, i ≤ j → (v i : ComplexVector n → ℂ) =ᵐ[(lebesgueC n).restrict (s i)]
      (v j : ComplexVector n → ℂ) := by
    intro i j hij
    exact (weightedTopHilbertLocalCoefficient_ae_restrict E g μ hμ h hh φ hφ a (s i)
      (localDomainCompactSet_isCompact E a i) (localDomainCompactSet_subset E a i) α (s j)
      (localDomainCompactSet_isCompact E a j) (localDomainCompactSet_subset E a j)
      (localDomainCompactSet_mono E a hij) u).symm
  obtain ⟨f, hf⟩ := compatibleLocalLp_glue (lebesgueC n) s
    (fun j => (localDomainCompactSet_isCompact E a j).measurableSet) v hcompat
  have hm : AEStronglyMeasurable f ((lebesgueC n).restrict (⋃ j, s j)) :=
    AEStronglyMeasurable.iUnion (fun j => (hf j).1.aestronglyMeasurable)
  have hUnion : (⋃ j, s j) = localDomain (r := r) E a := iUnion_localDomainCompactSet E a
  rw [hUnion] at hm
  refine ⟨f, hm, ?_⟩
  intro K hK hsub
  obtain ⟨j, hj⟩ := localDomainCompactSet_covers_compact E a K hK hsub
  refine ⟨(hf j).1.mono_measure (Measure.restrict_mono hj le_rfl), ?_⟩
  exact ((hf j).2.filter_mono (ae_mono (Measure.restrict_mono hj le_rfl))).trans
    (weightedTopHilbertLocalCoefficient_ae_restrict E g μ hμ h hh φ hφ a K hK hsub α (s j)
      (localDomainCompactSet_isCompact E a j) (localDomainCompactSet_subset E a j) hj u)

def weightedTopHilbertChartCoefficient
    (u : WeightedTopHilbert E g μ hμ h hh φ hφ) (a : M.Carrier) (α : Fin r) : ComplexVector n → ℂ :=
  (weightedTopHilbert_exists_chartCoefficient E g μ hμ h hh φ hφ u a α).choose

theorem weightedTopHilbertChartCoefficient_aestronglyMeasurable
    (u : WeightedTopHilbert E g μ hμ h hh φ hφ) (a : M.Carrier) (α : Fin r) :
    AEStronglyMeasurable (weightedTopHilbertChartCoefficient E g μ hμ h hh φ hφ u a α)
      ((lebesgueC n).restrict (localDomain (r := r) E a)) :=
  (weightedTopHilbert_exists_chartCoefficient E g μ hμ h hh φ hφ u a α).choose_spec.1

theorem weightedTopHilbertChartCoefficient_memLp
    (u : WeightedTopHilbert E g μ hμ h hh φ hφ) (a : M.Carrier) (α : Fin r)
    (K : Set (ComplexVector n)) (hK : IsCompact K) (hsub : K ⊆ localDomain (r := r) E a) :
    MemLp (weightedTopHilbertChartCoefficient E g μ hμ h hh φ hφ u a α)
      2 ((lebesgueC n).restrict K) :=
  ((weightedTopHilbert_exists_chartCoefficient E g μ hμ h hh φ hφ u a α).choose_spec.2 K hK hsub).1

theorem weightedTopHilbertChartCoefficient_ae
    (u : WeightedTopHilbert E g μ hμ h hh φ hφ) (a : M.Carrier) (α : Fin r)
    (K : Set (ComplexVector n)) (hK : IsCompact K) (hsub : K ⊆ localDomain (r := r) E a) :
    weightedTopHilbertChartCoefficient E g μ hμ h hh φ hφ u a α =ᵐ[(lebesgueC n).restrict K]
      weightedTopHilbertLocalCoefficient E g μ hμ h hh φ hφ a K hK hsub α u :=
  ((weightedTopHilbert_exists_chartCoefficient E g μ hμ h hh φ hφ u a α).choose_spec.2 K hK hsub).2

theorem weightedTopHilbertChartCoefficient_realize_ae
    (u : WeightedTopSection E g μ hμ h hh φ hφ) (a : M.Carrier) (α : Fin r) :
    weightedTopHilbertChartCoefficient E g μ hμ h hh φ hφ
      (realizeWeightedTopSection E g μ hμ h hh φ hφ u) a α =ᵐ[(lebesgueC n).restrict (localDomain (r := r) E a)]
        (fun z => coefficients (r := r) E u.1 a z Fin.elim0 α) := by
  rw [← iUnion_localDomainCompactSet E a, ae_eq_restrict_iUnion_iff]
  intro j
  exact (weightedTopHilbertChartCoefficient_ae E g μ hμ h hh φ hφ
    (realizeWeightedTopSection E g μ hμ h hh φ hφ u) a α (localDomainCompactSet E a j)
    (localDomainCompactSet_isCompact E a j) (localDomainCompactSet_subset E a j)).trans
      (weightedTopHilbertLocalCoefficient_realize_ae E g μ hμ h hh φ hφ a (localDomainCompactSet E a j)
        (localDomainCompactSet_isCompact E a j) (localDomainCompactSet_subset E a j) α u)

end Yau.LeafProofs.L14Aux

namespace Yau.LeafProofs.L14Aux

open BundleDbar

variable {n r : ℕ} {M : ComplexManifold n}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

def topTensorValueEquiv (a x : M.Carrier)
    (hx : x ∈ (extChartAt (ComplexModel n) a).source) :
    (antiComplexSubmodule E x 0) ≃ₗ[ℂ] E x where
  toFun A := A.1 Fin.elim0 (chartFrameBasis a x hx)
  invFun v := ⟨AlternatingMap.constOfIsEmpty ℝ (TangentVector M x) (Fin 0)
    ((chartFrameBasis a x hx).det.smulRight v), by
      intro w i
      exact Fin.elim0 i⟩
  left_inv A := by
    apply Subtype.ext
    apply AlternatingMap.ext
    intro w
    have hw : w = Fin.elim0 := Subsingleton.elim _ _
    rw [hw]
    have he : (chartFrameBasis a x hx).det.smulRight (A.1 Fin.elim0 (chartFrameBasis a x hx)) =
        A.1 Fin.elim0 := by
      apply sub_eq_zero.mp
      apply alternating_eq_zero_of_apply_basis_eq_zero (Module.Free.chooseBasis ℂ (E x)) (chartFrameBasis a x hx)
      simp only [AlternatingMap.sub_apply]
      change ((chartFrameBasis a x hx).det (chartFrameBasis a x hx)) •
        A.1 Fin.elim0 (chartFrameBasis a x hx) - A.1 Fin.elim0 (chartFrameBasis a x hx) = 0
      rw [Basis.det_self, one_smul, sub_self]
    exact he
  right_inv v := by
    change ((chartFrameBasis a x hx).det (chartFrameBasis a x hx)) • v = v
    rw [Basis.det_self, one_smul]
  map_add' A B := rfl
  map_smul' c A := rfl

theorem topTensorValueEquiv_form (u : NQForm E 0) (a x : M.Carrier)
    (hx : x ∈ (extChartAt (ComplexModel n) a).source) :
    topTensorValueEquiv E a x hx (u x) = topFormValue E u a x := by
  change (u x).1 Fin.elim0 (chartFrameBasis a x hx) = _
  unfold topFormValue
  congr 1
  funext i
  exact chartFrameBasis_apply a x hx i

def topTensorCoordinatesEquiv (a x : M.Carrier) (hx : x ∈ bundleChartSource (r := r) E a) :
    (antiComplexSubmodule E x 0) ≃ₗ[ℂ] ComplexVector r :=
  (topTensorValueEquiv E a x hx.1).trans
    ((localTriv (r := r) E a).continuousLinearEquivAt ℂ x hx.2).toLinearEquiv

theorem topTensorCoordinatesEquiv_form (u : NQForm E 0) (a : M.Carrier)
    (z : ComplexVector n) (hz : z ∈ localDomain (r := r) E a) :
    topTensorCoordinatesEquiv E a (chartInv a z)
      ⟨(extChartAt (ComplexModel n) a).map_target hz.1, hz.2⟩ (u (chartInv a z)) =
        coefficients (r := r) E u a z Fin.elim0 := by
  ext α
  change (((localTriv (r := r) E a).continuousLinearEquivAt ℂ (chartInv a z) hz.2)
    (topTensorValueEquiv E a (chartInv a z) ((extChartAt (ComplexModel n) a).map_target hz.1)
      (u (chartInv a z)))) α = _
  have hv := congrArg (fun v : E (chartInv a z) =>
    ((localTriv (r := r) E a).continuousLinearEquivAt ℂ (chartInv a z) hz.2 v) α)
      (topTensorValueEquiv_form E u a (chartInv a z) ((extChartAt (ComplexModel n) a).map_target hz.1))
  have ht := congrArg (fun L : E (chartInv a z) → ComplexVector r => L (topFormValue E u a (chartInv a z)) α)
    ((localTriv (r := r) E a).coe_continuousLinearEquivAt_eq (R := ℂ) hz.2)
  exact hv.trans (ht.trans (coefficients_topFormValue E u a z α).symm)

theorem topTensorValueEquiv_change (a b x : M.Carrier)
    (hxa : x ∈ (extChartAt (ComplexModel n) a).source)
    (hxb : x ∈ (extChartAt (ComplexModel n) b).source)
    (A : antiComplexSubmodule E x 0) :
    topTensorValueEquiv E b x hxb A =
      ((chartFrameBasis a x hxa).toMatrix (chartFrameBasis b x hxb)).det •
        topTensorValueEquiv E a x hxa A :=
  alternating_apply_basis_change (Module.Free.chooseBasis ℂ (E x))
    (chartFrameBasis a x hxa) (chartFrameBasis b x hxb) (A.1 Fin.elim0)

theorem topTensorCoordinatesEquiv_apply (a x : M.Carrier)
    (hx : x ∈ bundleChartSource (r := r) E a) (A : antiComplexSubmodule E x 0) :
    topTensorCoordinatesEquiv E a x hx A =
      (localTriv (r := r) E a).continuousLinearMapAt ℂ x (topTensorValueEquiv E a x hx.1 A) := by
  exact congrFun ((localTriv (r := r) E a).coe_continuousLinearEquivAt_eq (R := ℂ) hx.2) _

theorem topTensorValueEquiv_symm_coordinates (a x : M.Carrier)
    (hx : x ∈ bundleChartSource (r := r) E a) (v : ComplexVector r) :
    topTensorValueEquiv E a x hx.1 ((topTensorCoordinatesEquiv E a x hx).symm v) =
      (localTriv (r := r) E a).symmL ℂ x v := by
  rw [topTensorCoordinatesEquiv, LinearEquiv.symm_trans_apply, LinearEquiv.apply_symm_apply]
  exact congrFun ((localTriv (r := r) E a).symm_continuousLinearEquivAt_eq hx.2) v

theorem topTensorCoordinatesEquiv_transition (a b x : M.Carrier)
    (hxa : x ∈ bundleChartSource (r := r) E a)
    (hxb : x ∈ bundleChartSource (r := r) E b) (v : ComplexVector r) :
    topTensorCoordinatesEquiv E b x hxb ((topTensorCoordinatesEquiv E a x hxa).symm v) =
      ((chartFrameBasis a x hxa.1).toMatrix (chartFrameBasis b x hxb.1)).det •
        (localTriv (r := r) E b).continuousLinearMapAt ℂ x
          ((localTriv (r := r) E a).symmL ℂ x v) := by
  rw [topTensorCoordinatesEquiv_apply E b x hxb,
    topTensorValueEquiv_change E a b x hxa.1 hxb.1,
    topTensorValueEquiv_symm_coordinates E a x hxa, map_smul]

end Yau.LeafProofs.L14Aux

namespace Yau.LeafProofs.L14Aux

open BundleDbar Filter

variable {n r : ℕ} {M : ComplexManifold n}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

def weightedTopAmplitude (g : HermitianField M) (h : Metric E) (φ : M.Carrier → ℝ)
    (u : NQForm E 0) (x : M.Carrier) : ℝ :=
  Real.sqrt (BundleDbar.formNormSq (r := r) E g h u x * Real.exp (-φ x))

theorem weightedTopAmplitude_nonneg (g : HermitianField M) (h : Metric E) (φ : M.Carrier → ℝ)
    (u : NQForm E 0) (x : M.Carrier) : 0 ≤ weightedTopAmplitude (r := r) E g h φ u x :=
  Real.sqrt_nonneg _

theorem weightedTopAmplitude_sq (g : HermitianField M) (h : Metric E) (φ : M.Carrier → ℝ)
    (u : NQForm E 0) (x : M.Carrier) :
    weightedTopAmplitude (r := r) E g h φ u x ^ 2 =
      BundleDbar.formNormSq (r := r) E g h u x * Real.exp (-φ x) :=
  Real.sq_sqrt (mul_nonneg (formNormSq_top_nonneg E g h u x) (Real.exp_pos _).le)

variable (g : Yau.SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
  (h : Metric E) (hh : BundleDbar.SmoothMetric (r := r) E h) (φ : M.Carrier → ℝ) (hφ : SmoothFn φ)

theorem weightedTopAmplitude_memLp
    (g : Yau.SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (h : Metric E) (hh : BundleDbar.SmoothMetric (r := r) E h)
    (φ : M.Carrier → ℝ) (hφ : SmoothFn φ) (u : NQForm E 0) (hu : WeightedL2 (r := r) E g.form h μ φ u) :
    MemLp (weightedTopAmplitude (r := r) E g.form h φ u) 2 μ := by
  have hi := weightedTopNorm_integrable E g μ hμ h hh φ hφ u hu
  have hm : AEStronglyMeasurable (weightedTopAmplitude (r := r) E g.form h φ u) μ :=
    (Real.continuous_sqrt.measurable.comp_aemeasurable hi.aestronglyMeasurable.aemeasurable).aestronglyMeasurable
  apply (memLp_two_iff_integrable_sq_norm hm).mpr
  exact hi.congr (Eventually.of_forall fun x => by
    change BundleDbar.formNormSq (r := r) E g.form h u x * Real.exp (-φ x) =
      ‖weightedTopAmplitude (r := r) E g.form h φ u x‖ ^ 2
    rw [Real.norm_eq_abs, sq_abs, weightedTopAmplitude_sq])

def weightedTopAmplitudeLp (u : WeightedTopSection E g μ hμ h hh φ hφ) : Lp ℝ 2 μ :=
  (weightedTopAmplitude_memLp E g μ hμ h hh φ hφ u.1 u.2).toLp
    (weightedTopAmplitude (r := r) E g.form h φ u.1)

theorem weightedTopAmplitudeLp_ae (u : WeightedTopSection E g μ hμ h hh φ hφ) :
    weightedTopAmplitudeLp E g μ hμ h hh φ hφ u =ᵐ[μ] weightedTopAmplitude (r := r) E g.form h φ u.1 :=
  MemLp.coeFn_toLp _

theorem real_toLp_norm_sq {X : Type*} [MeasurableSpace X] (ν : Measure X)
    (f : X → ℝ) (hf : MemLp f 2 ν) :
    ‖hf.toLp f‖ ^ 2 = (∫⁻ x, ENNReal.ofReal (‖f x‖ ^ 2) ∂ν).toReal := by
  have hi : Integrable (fun x => ‖f x‖ ^ 2) ν :=
    (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf
  calc
    _ = inner ℝ (hf.toLp f) (hf.toLp f) := norm_sq_eq_re_inner (𝕜 := ℝ) _
    _ = ∫ x, ‖(hf.toLp f) x‖ ^ 2 ∂ν := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by
        change inner ℝ ((hf.toLp f) x) ((hf.toLp f) x) = ‖(hf.toLp f) x‖ ^ 2
        exact (norm_sq_eq_re_inner (𝕜 := ℝ) ((hf.toLp f) x)).symm
    _ = ∫ x, ‖f x‖ ^ 2 ∂ν := integral_congr_ae (hf.coeFn_toLp.mono fun x hx => by
      change ‖(hf.toLp f) x‖ ^ 2 = ‖f x‖ ^ 2
      rw [hx])
    _ = _ := integral_eq_lintegral_of_nonneg_ae
      (Eventually.of_forall fun x => sq_nonneg ‖f x‖) hi.aestronglyMeasurable

theorem weightedTopAmplitudeLp_norm (u : WeightedTopSection E g μ hμ h hh φ hφ) :
    ‖weightedTopAmplitudeLp E g μ hμ h hh φ hφ u‖ = ‖u‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [weightedTopAmplitudeLp, real_toLp_norm_sq, weightedTopSection_norm_sq E g μ hμ h hh φ hφ u]
  congr 1
  apply lintegral_congr
  intro x
  rw [Real.norm_eq_abs, sq_abs, weightedTopAmplitude_sq]
  rfl

theorem weightedTopAmplitude_summable_ae
    (v : ℕ → WeightedTopSection E g μ hμ h hh φ hφ) (hv : Summable (fun j => ‖v j‖)) :
    ∀ᵐ x ∂μ, Summable (fun j => weightedTopAmplitude (r := r) E g.form h φ (v j).1 x) := by
  have hsum : (∑' j, eLpNorm (weightedTopAmplitude (r := r) E g.form h φ (v j).1) 2 μ) ≠ ⊤ := by
    have ht := hv.tsum_ofReal_ne_top
    convert ht using 1
    congr 1
    funext j
    rw [← Lp.enorm_toLp (weightedTopAmplitude_memLp E g μ hμ h hh φ hφ (v j).1 (v j).2)]
    change ‖weightedTopAmplitudeLp E g μ hμ h hh φ hφ (v j)‖ₑ = ENNReal.ofReal ‖v j‖
    rw [← ofReal_norm, weightedTopAmplitudeLp_norm E g μ hμ h hh φ hφ]
  have hs := summable_norm_of_tsum_eLpNorm_ne_top (p := 2) (by norm_num : (1 : ℝ≥0∞) ≤ 2) hsum
  filter_upwards [hs] with x hx
  convert hx using 1
  funext j
  exact (Real.norm_of_nonneg (weightedTopAmplitude_nonneg E g.form h φ (v j).1 x)).symm

end Yau.LeafProofs.L14Aux

namespace Yau.LeafProofs.L14Aux

open BundleDbar Filter

variable {n r : ℕ} {M : ComplexManifold n}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

def canonicalTopTensorCoordinates (x : M.Carrier) : (antiComplexSubmodule E x 0) ≃ₗ[ℂ] ComplexVector r :=
  topTensorCoordinatesEquiv E x x ⟨mem_extChartAt_source x, FiberBundle.mem_baseSet_trivializationAt' x⟩

theorem canonicalTopTensorCoordinates_apply (u : NQForm E 0) (x : M.Carrier) (α : Fin r) :
    canonicalTopTensorCoordinates (r := r) E x (u x) α =
      (bundleFrameBasis (r := r) E x x (FiberBundle.mem_baseSet_trivializationAt' x)).repr
        (topFormValue E u x x) α := by
  have hval := topTensorValueEquiv_form E u x x (mem_extChartAt_source x)
  have hcoord := topTensorCoordinatesEquiv_apply (r := r) E x x
    ⟨mem_extChartAt_source x, FiberBundle.mem_baseSet_trivializationAt' x⟩ (u x)
  have he := congrArg (fun v : E x => (localTriv (r := r) E x).continuousLinearMapAt ℂ x v α) hval
  exact (congrArg (fun v : ComplexVector r => v α) hcoord).trans
    (he.trans (bundleFrameBasis_repr E x x (FiberBundle.mem_baseSet_trivializationAt' x) _ α).symm)

theorem canonicalTopTensorCoordinates_amplitude_bound
    (g : HermitianField M) (h : Metric E) (φ : M.Carrier → ℝ) (x : M.Carrier) (α : Fin r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : NQForm E 0,
      ‖canonicalTopTensorCoordinates (r := r) E x (u x) α‖ ≤
        C * weightedTopAmplitude (r := r) E g h φ u x := by
  let b := bundleFrameBasis (r := r) E x x (FiberBundle.mem_baseSet_trivializationAt' x)
  let H := hermitianGram (h x) b
  let d := (gMat g x).det.re
  let c := (H⁻¹ α α).re
  have hH : H.PosDef := hermitianGram_posDef (h x) b
  have hd : 0 < d := (Complex.pos_iff.mp (gMat_posDef g x).det_pos).1
  have hc : 0 ≤ c := (Complex.nonneg_iff.mp (hH.inv.posSemidef.diag_nonneg (i := α))).1
  have hC : 0 ≤ c * d * Real.exp (φ x) := mul_nonneg (mul_nonneg hc hd.le) (Real.exp_pos _).le
  refine ⟨Real.sqrt (c * d * Real.exp (φ x)), Real.sqrt_nonneg _, ?_⟩
  intro u
  have hv : (star (fun β => b.repr (topFormValue E u x x) β) ⬝ᵥ H *ᵥ
      (fun β => b.repr (topFormValue E u x x) β)).re =
        ((h x).toFun (topFormValue E u x x) (topFormValue E u x x)).re := by
    simpa only [dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum, mul_assoc] using
      congrArg Complex.re (hermitian_coordinates (h x) b (topFormValue E u x x) (topFormValue E u x x))
  have hq : ((h x).toFun (topFormValue E u x x) (topFormValue E u x x)).re =
      d * BundleDbar.formNormSq (r := r) E g h u x := by
    rw [formNormSq_top_factor, gMat_inv_det_re, topCoefficientNormSq_eq_value E h u x]
    change _ = d * (d⁻¹ * _)
    rw [← mul_assoc, mul_inv_cancel₀ hd.ne', one_mul]
  have hsq := matrix_coefficient_le_inverse_diagonal H hH
    (fun β => b.repr (topFormValue E u x x) β) α
  rw [hv, hq] at hsq
  rw [canonicalTopTensorCoordinates_apply E u x α]
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (weightedTopAmplitude_nonneg E g h φ u x))).mp
  calc
    _ ≤ c * (d * BundleDbar.formNormSq (r := r) E g h u x) := hsq
    _ = (Real.sqrt (c * d * Real.exp (φ x)) * weightedTopAmplitude (r := r) E g h φ u x) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hC, weightedTopAmplitude_sq]
      have he : Real.exp (φ x) * Real.exp (-φ x) = 1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
      calc
        _ = (c * (d * BundleDbar.formNormSq (r := r) E g h u x)) *
            (Real.exp (φ x) * Real.exp (-φ x)) := by rw [he, mul_one]
        _ = _ := by ring

variable (g : Yau.SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
  (h : Metric E) (hh : BundleDbar.SmoothMetric (r := r) E h) (φ : M.Carrier → ℝ) (hφ : SmoothFn φ)

theorem weightedTopSection_series_coordinates_summable_ae
    (v : ℕ → WeightedTopSection E g μ hμ h hh φ hφ) (hv : Summable (fun j => ‖v j‖)) :
    ∀ᵐ x ∂μ, Summable (fun j => canonicalTopTensorCoordinates (r := r) E x ((v j).1 x)) := by
  filter_upwards [weightedTopAmplitude_summable_ae E g μ hμ h hh φ hφ v hv] with x hx
  have hc : ∀ α : Fin r, Summable (fun j => canonicalTopTensorCoordinates (r := r) E x ((v j).1 x) α) := by
    intro α
    obtain ⟨C, _, hC⟩ := canonicalTopTensorCoordinates_amplitude_bound E g.form h φ x α
    exact (hx.mul_left C).of_norm_bounded (fun j => hC (v j).1)
  exact (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin r => ℂ)).summable.mp
    (Pi.summable.mpr hc)

/-- Actual intrinsic tensors defined by pointwise finite-dimensional summation.
At the exceptional nonsummable points `tsum` uses its standard zero value. -/
def topFormTsum (v : ℕ → NQForm E 0) : NQForm E 0 := fun x =>
  (canonicalTopTensorCoordinates (r := r) E x).symm (∑' j, canonicalTopTensorCoordinates (r := r) E x (v j x))

theorem canonicalTopTensorCoordinates_tsum (v : ℕ → NQForm E 0) (x : M.Carrier) :
    canonicalTopTensorCoordinates (r := r) E x (topFormTsum (r := r) E v x) =
      ∑' j, canonicalTopTensorCoordinates (r := r) E x (v j x) :=
  LinearEquiv.apply_symm_apply _ _

def topTensorCoordinateChangeCLM (a b x : M.Carrier)
    (hxa : x ∈ bundleChartSource (r := r) E a) (hxb : x ∈ bundleChartSource (r := r) E b) :
    ComplexVector r →L[ℂ] ComplexVector r :=
  LinearMap.toContinuousLinearMap
    (((topTensorCoordinatesEquiv E a x hxa).symm.trans (topTensorCoordinatesEquiv E b x hxb)).toLinearMap)

theorem topTensorCoordinateChangeCLM_apply (a b x : M.Carrier)
    (hxa : x ∈ bundleChartSource (r := r) E a) (hxb : x ∈ bundleChartSource (r := r) E b)
    (v : ComplexVector r) :
    topTensorCoordinateChangeCLM (r := r) E a b x hxa hxb v =
      topTensorCoordinatesEquiv E b x hxb ((topTensorCoordinatesEquiv E a x hxa).symm v) := rfl

theorem topFormTsum_chart_hasSum (v : ℕ → NQForm E 0) (a x : M.Carrier)
    (hx : x ∈ bundleChartSource (r := r) E a)
    (hs : Summable (fun j => canonicalTopTensorCoordinates (r := r) E x (v j x))) :
    HasSum (fun j => topTensorCoordinatesEquiv E a x hx (v j x))
      (topTensorCoordinatesEquiv E a x hx (topFormTsum (r := r) E v x)) := by
  let hx0 : x ∈ bundleChartSource (r := r) E x :=
    ⟨mem_extChartAt_source x, FiberBundle.mem_baseSet_trivializationAt' x⟩
  have ht := (topTensorCoordinateChangeCLM (r := r) E x a x hx0 hx).hasSum hs.hasSum
  convert ht using 1
  · funext j
    change topTensorCoordinatesEquiv E a x hx (v j x) =
      topTensorCoordinatesEquiv E a x hx ((canonicalTopTensorCoordinates (r := r) E x).symm
        (canonicalTopTensorCoordinates (r := r) E x (v j x)))
    exact (congrArg (topTensorCoordinatesEquiv E a x hx)
      ((canonicalTopTensorCoordinates (r := r) E x).symm_apply_apply (v j x))).symm
  · rfl


theorem topFormTsum_coefficients_hasSum (v : ℕ → NQForm E 0) (a : M.Carrier)
    (z : ComplexVector n) (hz : z ∈ localDomain (r := r) E a) (α : Fin r)
    (hs : Summable (fun j => canonicalTopTensorCoordinates (r := r) E (chartInv a z) (v j (chartInv a z)))) :
    HasSum (fun j => coefficients (r := r) E (v j) a z Fin.elim0 α)
      (coefficients (r := r) E (topFormTsum (r := r) E v) a z Fin.elim0 α) := by
  have ht := (PiLp.proj 2 (fun _ : Fin r => ℂ) (𝕜 := ℂ) α).hasSum
    (topFormTsum_chart_hasSum E v a (chartInv a z)
      ⟨(extChartAt (ComplexModel n) a).map_target hz.1, hz.2⟩ hs)
  convert ht using 1
  · funext j
    exact (congrArg (fun w : ComplexVector r => w α) (topTensorCoordinatesEquiv_form E (v j) a z hz)).symm
  · exact (congrArg (fun w : ComplexVector r => w α)
      (topTensorCoordinatesEquiv_form E (topFormTsum (r := r) E v) a z hz)).symm

end Yau.LeafProofs.L14Aux

namespace Yau.LeafProofs.L14Aux

open BundleDbar Filter

variable {n r : ℕ} {M : ComplexManifold n}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

theorem ae_chartInv_of_ae (g : Yau.SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (a : M.Carrier) (P : M.Carrier → Prop)
    (hP : ∀ᵐ x ∂μ, P x) :
    ∀ᵐ z ∂(lebesgueC n).restrict (localDomain (r := r) E a), P (chartInv a z) := by
  have ht := (chartInvExtension_quasiMeasurePreserving (r := r) E g μ hμ a).ae (hP.filter_mono (ae_mono Measure.restrict_le_self))
  filter_upwards [ht, ae_restrict_mem (localDomain_isOpen (r := r) E a).measurableSet] with z hz hzdom
  simpa only [chartInvExtension, if_pos hzdom.1] using hz

variable (g : Yau.SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
  (h : Metric E) (hh : BundleDbar.SmoothMetric (r := r) E h) (φ : M.Carrier → ℝ) (hφ : SmoothFn φ)

theorem weightedTopLocalCoefficient_series_enorm
    (v : ℕ → WeightedTopSection E g μ hμ h hh φ hφ) (hv : Summable (fun j => ‖v j‖))
    (a : M.Carrier) (K : Set (ComplexVector n)) (hK : IsCompact K)
    (hsub : K ⊆ localDomain (r := r) E a) (α : Fin r) :
    (∑' j, ‖weightedTopLocalCoefficient E g μ hμ h hh φ hφ a K hK hsub α (v j)‖ₑ) ≠ ⊤ := by
  obtain ⟨C, _, hC⟩ := weightedTopLocalCoefficient_bounded E g μ hμ h hh φ hφ a K hK hsub α
  have hs : Summable (fun j => ‖weightedTopLocalCoefficient E g μ hμ h hh φ hφ a K hK hsub α (v j)‖) :=
    Summable.of_nonneg_of_le (fun j => norm_nonneg _) (fun j => hC (v j)) (hv.mul_left C)
  simpa only [ofReal_norm] using hs.tsum_ofReal_ne_top

theorem topFormTsum_coefficients_ae_localLpTsum
    (v : ℕ → WeightedTopSection E g μ hμ h hh φ hφ) (hv : Summable (fun j => ‖v j‖))
    (a : M.Carrier) (K : Set (ComplexVector n)) (hK : IsCompact K)
    (hsub : K ⊆ localDomain (r := r) E a) (α : Fin r) :
    (fun z => coefficients (r := r) E (topFormTsum (r := r) E (fun j => (v j).1)) a z Fin.elim0 α)
      =ᵐ[(lebesgueC n).restrict K]
        (∑' j, weightedTopLocalCoefficient E g μ hμ h hh φ hφ a K hK hsub α (v j) : Lp ℂ 2 ((lebesgueC n).restrict K)) := by
  have hpoint := ae_chartInv_of_ae (r := r) E g μ hμ a _
    (weightedTopSection_series_coordinates_summable_ae E g μ hμ h hh φ hφ v hv)
  have hpointK := hpoint.filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl))
  have hcoefs : ∀ᵐ z ∂(lebesgueC n).restrict K, ∀ j,
      weightedTopLocalCoefficient E g μ hμ h hh φ hφ a K hK hsub α (v j) z =
        coefficients (r := r) E (v j).1 a z Fin.elim0 α :=
    ae_all_iff.mpr (fun j => weightedTopLocalCoefficient_ae E g μ hμ h hh φ hφ a K hK hsub α (v j))
  have hsum := Lp.hasSum_coeFn_tsum
    (weightedTopLocalCoefficient_series_enorm E g μ hμ h hh φ hφ v hv a K hK hsub α)
  filter_upwards [hpointK, hcoefs, hsum, ae_restrict_mem hK.measurableSet] with z hp hc hs hz
  have ht := topFormTsum_coefficients_hasSum E (fun j => (v j).1) a z (hsub hz) α hp
  apply ht.unique
  convert hs using 1
  funext j
  exact (hc j).symm

theorem topFormTsum_coefficients_memLp
    (v : ℕ → WeightedTopSection E g μ hμ h hh φ hφ) (hv : Summable (fun j => ‖v j‖))
    (a : M.Carrier) (K : Set (ComplexVector n)) (hK : IsCompact K)
    (hsub : K ⊆ localDomain (r := r) E a) (α : Fin r) :
    MemLp (fun z => coefficients (r := r) E (topFormTsum (r := r) E (fun j => (v j).1)) a z Fin.elim0 α)
      2 ((lebesgueC n).restrict K) :=
  (memLp_congr_ae (topFormTsum_coefficients_ae_localLpTsum E g μ hμ h hh φ hφ v hv a K hK hsub α)).mpr
    (Lp.memLp _)

theorem topFormTsum_locallyL2
    (v : ℕ → WeightedTopSection E g μ hμ h hh φ hφ) (hv : Summable (fun j => ‖v j‖)) :
    LocallyL2 (r := r) E (topFormTsum (r := r) E (fun j => (v j).1)) := by
  intro a I α
  have hI : I = Fin.elim0 := Subsingleton.elim _ _
  subst I
  constructor
  · have hm : AEStronglyMeasurable
        (fun z => coefficients (r := r) E (topFormTsum (r := r) E (fun j => (v j).1)) a z Fin.elim0 α)
        ((lebesgueC n).restrict (⋃ j, localDomainCompactSet (r := r) E a j)) :=
      AEStronglyMeasurable.iUnion (fun j =>
        (topFormTsum_coefficients_memLp E g μ hμ h hh φ hφ v hv a (localDomainCompactSet E a j)
          (localDomainCompactSet_isCompact E a j) (localDomainCompactSet_subset E a j) α).aestronglyMeasurable)
    simpa only [iUnion_localDomainCompactSet E a] using hm
  · intro K hK hsub
    have hf := topFormTsum_coefficients_memLp E g μ hμ h hh φ hφ v hv a K hK hsub α
    have hi := (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf
    exact (hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun z => sq_nonneg
      ‖coefficients (r := r) E (topFormTsum (r := r) E (fun j => (v j).1)) a z Fin.elim0 α‖)).mp hi.2

end Yau.LeafProofs.L14Aux

namespace Yau.LeafProofs.L14Aux

open BundleDbar Filter

variable {n r : ℕ} {M : ComplexManifold n}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

def canonicalTopTensorWeightedQuadratic (g : HermitianField M) (h : Metric E) (φ : M.Carrier → ℝ)
    (x : M.Carrier) (v : ComplexVector r) : ℝ :=
  ((gMat g x).det.re)⁻¹ *
    (∑ α, ∑ β, star (v α) * hermitianGram (h x)
      (bundleFrameBasis (r := r) E x x (FiberBundle.mem_baseSet_trivializationAt' x)) α β * v β).re *
        Real.exp (-φ x)

theorem canonicalTopTensorWeightedQuadratic_continuous (g : HermitianField M) (h : Metric E)
    (φ : M.Carrier → ℝ) (x : M.Carrier) :
    Continuous (canonicalTopTensorWeightedQuadratic (r := r) E g h φ x) := by
  unfold canonicalTopTensorWeightedQuadratic
  fun_prop

theorem canonicalTopTensorWeightedQuadratic_form (g : HermitianField M) (h : Metric E)
    (φ : M.Carrier → ℝ) (u : NQForm E 0) (x : M.Carrier) :
    canonicalTopTensorWeightedQuadratic (r := r) E g h φ x (canonicalTopTensorCoordinates (r := r) E x (u x)) =
      BundleDbar.formNormSq (r := r) E g h u x * Real.exp (-φ x) := by
  unfold canonicalTopTensorWeightedQuadratic
  simp_rw [canonicalTopTensorCoordinates_apply E u x]
  rw [hermitian_coordinates, formNormSq_top_factor, gMat_inv_det_re, topCoefficientNormSq_eq_value E h u x]

variable (g : Yau.SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
  (h : Metric E) (hh : BundleDbar.SmoothMetric (r := r) E h) (φ : M.Carrier → ℝ) (hφ : SmoothFn φ)

def weightedTopSectionPointCoordinates (x : M.Carrier) :
    WeightedTopSection E g μ hμ h hh φ hφ →ₗ[ℂ] ComplexVector r where
  toFun u := canonicalTopTensorCoordinates (r := r) E x (u.1 x)
  map_add' u v := (canonicalTopTensorCoordinates (r := r) E x).map_add (u.1 x) (v.1 x)
  map_smul' c u := (canonicalTopTensorCoordinates (r := r) E x).map_smul c (u.1 x)

theorem weightedTopSectionPointCoordinates_sum {ι : Type*} (v : ι → WeightedTopSection E g μ hμ h hh φ hφ)
    (s : Finset ι) (x : M.Carrier) :
    canonicalTopTensorCoordinates (r := r) E x ((∑ j ∈ s, v j).1 x) =
      ∑ j ∈ s, canonicalTopTensorCoordinates (r := r) E x ((v j).1 x) :=
  map_sum (weightedTopSectionPointCoordinates E g μ hμ h hh φ hφ x) v s

theorem topFormTsum_weightedQuadratic_tendsto_ae
    (v : ℕ → WeightedTopSection E g μ hμ h hh φ hφ) (hv : Summable (fun j => ‖v j‖)) :
    ∀ᵐ x ∂μ, Tendsto (fun N => ENNReal.ofReal
        (BundleDbar.formNormSq (r := r) E g.form h ((∑ j ∈ Finset.range N, v j).1) x * Real.exp (-φ x)))
      atTop (𝓝 (ENNReal.ofReal (BundleDbar.formNormSq (r := r) E g.form h
        (topFormTsum (r := r) E (fun j => (v j).1)) x * Real.exp (-φ x)))) := by
  filter_upwards [weightedTopSection_series_coordinates_summable_ae E g μ hμ h hh φ hφ v hv] with x hx
  have hs : Tendsto (fun N => canonicalTopTensorCoordinates (r := r) E x ((∑ j ∈ Finset.range N, v j).1 x)) atTop
      (𝓝 (canonicalTopTensorCoordinates (r := r) E x (topFormTsum (r := r) E (fun j => (v j).1) x))) := by
    simpa only [weightedTopSectionPointCoordinates_sum E g μ hμ h hh φ hφ,
      canonicalTopTensorCoordinates_tsum (r := r) E] using hx.tendsto_sum_tsum_nat
  have ht := (ENNReal.continuous_ofReal.comp
    (canonicalTopTensorWeightedQuadratic_continuous (r := r) E g.form h φ x)).continuousAt.tendsto.comp hs
  simpa only [Function.comp_def, canonicalTopTensorWeightedQuadratic_form (r := r) E g.form h φ] using ht

theorem weightedTopSection_normSq_eq_ofReal (u : WeightedTopSection E g μ hμ h hh φ hφ) :
    weightedNormSq (r := r) E g.form h μ φ u.1 = ENNReal.ofReal (‖u‖ ^ 2) := by
  have hn := weightedTopSection_norm_sq E g μ hμ h hh φ hφ u
  change ‖u‖ ^ 2 = (weightedNormSq (r := r) E g.form h μ φ u.1).toReal at hn
  rw [hn, ENNReal.ofReal_toReal u.2.2.ne]

theorem weightedTopSection_partialNormSq_le
    (v : ℕ → WeightedTopSection E g μ hμ h hh φ hφ) (hv : Summable (fun j => ‖v j‖)) (N : ℕ) :
    weightedNormSq (r := r) E g.form h μ φ (∑ j ∈ Finset.range N, v j).1 ≤
      ENNReal.ofReal ((∑' j, ‖v j‖) ^ 2) := by
  rw [weightedTopSection_normSq_eq_ofReal E g μ hμ h hh φ hφ]
  have hn := (norm_sum_le (Finset.range N) v).trans
    (hv.sum_le_tsum (Finset.range N) (fun j _ => norm_nonneg _))
  have hS : 0 ≤ ∑' j, ‖v j‖ := tsum_nonneg (fun j => norm_nonneg _)
  apply ENNReal.ofReal_le_ofReal
  nlinarith [norm_nonneg (∑ j ∈ Finset.range N, v j)]

theorem topFormTsum_weightedNormSq_le
    (v : ℕ → WeightedTopSection E g μ hμ h hh φ hφ) (hv : Summable (fun j => ‖v j‖)) :
    weightedNormSq (r := r) E g.form h μ φ (topFormTsum (r := r) E (fun j => (v j).1)) ≤
      ENNReal.ofReal ((∑' j, ‖v j‖) ^ 2) := by
  let F := fun N x => ENNReal.ofReal (BundleDbar.formNormSq (r := r) E g.form h
    (∑ j ∈ Finset.range N, v j).1 x * Real.exp (-φ x))
  have hw : Measurable (fun x => Real.exp (-φ x)) :=
    (Real.continuous_exp.comp (L18Aux.continuous_of_smoothFn hφ).neg).measurable
  have hm : ∀ N, AEMeasurable (F N) μ := fun N =>
    ENNReal.measurable_ofReal.comp_aemeasurable
      ((formNormSq_top_aemeasurable E g μ hμ h hh (∑ j ∈ Finset.range N, v j).1
        (∑ j ∈ Finset.range N, v j).2.1).mul hw.aemeasurable)
  calc
    _ = ∫⁻ x, liminf (fun N => F N x) atTop ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [topFormTsum_weightedQuadratic_tendsto_ae E g μ hμ h hh φ hφ v hv] with x hx
      exact hx.liminf_eq.symm
    _ ≤ liminf (fun N => ∫⁻ x, F N x ∂μ) atTop := lintegral_liminf_le' hm
    _ ≤ _ := liminf_le_of_frequently_le' (Eventually.of_forall
      (fun N => weightedTopSection_partialNormSq_le E g μ hμ h hh φ hφ v hv N)).frequently

theorem topFormTsum_weightedL2
    (v : ℕ → WeightedTopSection E g μ hμ h hh φ hφ) (hv : Summable (fun j => ‖v j‖)) :
    WeightedL2 (r := r) E g.form h μ φ (topFormTsum (r := r) E (fun j => (v j).1)) :=
  ⟨topFormTsum_locallyL2 E g μ hμ h hh φ hφ v hv,
    lt_of_le_of_lt (topFormTsum_weightedNormSq_le E g μ hμ h hh φ hφ v hv) ENNReal.ofReal_lt_top⟩

end Yau.LeafProofs.L14Aux

namespace Yau.LeafProofs.L14Aux

open BundleDbar Filter

variable {n r : ℕ} {M : ComplexManifold n}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]
variable (g : Yau.SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
  (h : Metric E) (hh : BundleDbar.SmoothMetric (r := r) E h) (φ : M.Carrier → ℝ) (hφ : SmoothFn φ)

def weightedTopSectionTsum (v : ℕ → WeightedTopSection E g μ hμ h hh φ hφ)
    (hv : Summable (fun j => ‖v j‖)) : WeightedTopSection E g μ hμ h hh φ hφ :=
  ⟨topFormTsum (r := r) E (fun j => (v j).1), topFormTsum_weightedL2 E g μ hμ h hh φ hφ v hv⟩

theorem weightedTopSectionTsum_norm_le (v : ℕ → WeightedTopSection E g μ hμ h hh φ hφ)
    (hv : Summable (fun j => ‖v j‖)) :
    ‖weightedTopSectionTsum E g μ hμ h hh φ hφ v hv‖ ≤ ∑' j, ‖v j‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (tsum_nonneg (fun j => norm_nonneg _))).mp
  have hn := weightedTopSection_norm_sq E g μ hμ h hh φ hφ (weightedTopSectionTsum E g μ hμ h hh φ hφ v hv)
  change ‖weightedTopSectionTsum E g μ hμ h hh φ hφ v hv‖ ^ 2 =
    (weightedNormSq (r := r) E g.form h μ φ (topFormTsum (r := r) E (fun j => (v j).1))).toReal at hn
  rw [hn]
  simpa only [ENNReal.toReal_ofReal (sq_nonneg _)] using ENNReal.toReal_mono ENNReal.ofReal_ne_top
    (topFormTsum_weightedNormSq_le E g μ hμ h hh φ hφ v hv)

theorem topFormTsum_sub_partial_ae
    (v : ℕ → WeightedTopSection E g μ hμ h hh φ hφ) (hv : Summable (fun j => ‖v j‖)) (N : ℕ) :
    ∀ᵐ x ∂μ,
      (topFormTsum (r := r) E (fun j => (v j).1) - (∑ j ∈ Finset.range N, v j).1) x =
        topFormTsum (r := r) E (fun j => (v (j+N)).1) x := by
  filter_upwards [weightedTopSection_series_coordinates_summable_ae E g μ hμ h hh φ hφ v hv] with x hx
  letI : AddCommGroup {A : MixedTensor E x 0 // AntiComplexLinear E A} := (antiComplexSubmodule E x 0).addCommGroup
  apply (canonicalTopTensorCoordinates (r := r) E x).injective
  change canonicalTopTensorCoordinates E x
      (topFormTsum (r := r) E (fun j => (v j).1) x - (∑ j ∈ Finset.range N, v j).1 x) = _
  calc
    _ = canonicalTopTensorCoordinates E x (topFormTsum (r := r) E (fun j => (v j).1) x) -
        canonicalTopTensorCoordinates E x ((∑ j ∈ Finset.range N, v j).1 x) :=
      map_sub (canonicalTopTensorCoordinates (r := r) E x) _ _
    _ = (∑' j, canonicalTopTensorCoordinates E x ((v j).1 x)) -
        ∑ j ∈ Finset.range N, canonicalTopTensorCoordinates E x ((v j).1 x) :=
      congrArg₂ (fun a b : ComplexVector r => a-b)
        (canonicalTopTensorCoordinates_tsum E (fun j => (v j).1) x)
        (weightedTopSectionPointCoordinates_sum E g μ hμ h hh φ hφ v (Finset.range N) x)
    _ = ∑' j, canonicalTopTensorCoordinates E x ((v (j+N)).1 x) := by
      have ht := hx.sum_add_tsum_nat_add N
      exact sub_eq_iff_eq_add.mpr (ht.symm.trans (add_comm _ _))
    _ = _ := (canonicalTopTensorCoordinates_tsum E (fun j => (v (j+N)).1) x).symm

theorem weightedTopSectionTsum_norm_sub_partial_le
    (v : ℕ → WeightedTopSection E g μ hμ h hh φ hφ) (hv : Summable (fun j => ‖v j‖)) (N : ℕ) :
    ‖weightedTopSectionTsum E g μ hμ h hh φ hφ v hv - ∑ j ∈ Finset.range N, v j‖ ≤
      ∑' j, ‖v (j+N)‖ := by
  have htail : Summable (fun j => ‖v (j+N)‖) := hv.comp_injective (by intro i j hij; exact Nat.add_right_cancel hij)
  let t := weightedTopSectionTsum E g μ hμ h hh φ hφ (fun j => v (j+N)) htail
  have heq : ‖weightedTopSectionTsum E g μ hμ h hh φ hφ v hv - ∑ j ∈ Finset.range N, v j‖ ^ 2 = ‖t‖ ^ 2 := by
    rw [weightedTopSection_norm_sq E g μ hμ h hh φ hφ, weightedTopSection_norm_sq E g μ hμ h hh φ hφ]
    apply congrArg ENNReal.toReal
    apply weightedNormSq_congr_ae E g.form h μ φ
    exact topFormTsum_sub_partial_ae E g μ hμ h hh φ hφ v hv N
  have hn := (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp heq
  rw [hn]
  exact weightedTopSectionTsum_norm_le E g μ hμ h hh φ hφ (fun j => v (j+N)) htail

theorem weightedTopSectionTsum_tendsto_partial
    (v : ℕ → WeightedTopSection E g μ hμ h hh φ hφ) (hv : Summable (fun j => ‖v j‖)) :
    Tendsto (fun N => ∑ j ∈ Finset.range N, v j) atTop
      (𝓝 (weightedTopSectionTsum E g μ hμ h hh φ hφ v hv)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun N => norm_nonneg _)
    (fun N => ?_) (tendsto_sum_nat_add (fun j => ‖v j‖))
  rw [norm_sub_rev]
  exact weightedTopSectionTsum_norm_sub_partial_le E g μ hμ h hh φ hφ v hv N

theorem weightedTopSection_complete : CompleteSpace (WeightedTopSection E g μ hμ h hh φ hφ) := by
  apply Metric.complete_of_cauchySeq_tendsto
  intro u hu
  obtain ⟨f, hf₁, hf₂⟩ := Metric.exists_subseq_summable_dist_of_cauchySeq u hu
  simp only [dist_eq_norm] at hf₂
  let v n := u (f (n+1)) - u (f n)
  have hv_sum : (fun n => ∑ i ∈ Finset.range n, v i) = fun n => u (f n) - u (f 0) := by
    funext n
    exact Finset.sum_range_sub (u ∘ f) n
  have ha := weightedTopSectionTsum_tendsto_partial E g μ hμ h hh φ hφ v hf₂
  refine ⟨weightedTopSectionTsum E g μ hμ h hh φ hφ v hf₂ + u (f 0), ?_⟩
  refine tendsto_nhds_of_cauchySeq_of_subseq hu hf₁.tendsto_atTop ?_
  rw [hv_sum] at ha
  have h₁ := Tendsto.add_const (u (f 0)) ha
  simpa only [sub_add_cancel] using! h₁

theorem realizeWeightedTopSection_surjective :
    Function.Surjective (realizeWeightedTopSection E g μ hμ h hh φ hφ) := by
  letI : CompleteSpace (WeightedTopSection E g μ hμ h hh φ hφ) :=
    weightedTopSection_complete E g μ hμ h hh φ hφ
  have hc : IsClosed (Set.range (realizeWeightedTopSection E g μ hμ h hh φ hφ)) :=
    (UniformSpace.Completion.isUniformInducing_coe (WeightedTopSection E g μ hμ h hh φ hφ)).isComplete_range.isClosed
  exact Set.range_eq_univ.mp (hc.closure_eq.symm.trans
    (realizeWeightedTopSection_denseRange E g μ hμ h hh φ hφ).closure_range)

theorem realizeWeightedTopClass_surjective :
    Function.Surjective (realizeWeightedTopClass E g μ hμ h hh φ hφ) := by
  intro u
  obtain ⟨v, hv⟩ := realizeWeightedTopSection_surjective E g μ hμ h hh φ hφ u
  exact ⟨Quotient.mk _ v, hv⟩

theorem realizeWeightedTopClass_bijective :
    Function.Bijective (realizeWeightedTopClass E g μ hμ h hh φ hφ) :=
  ⟨realizeWeightedTopClass_injective E g μ hμ h hh φ hφ,
    realizeWeightedTopClass_surjective E g μ hμ h hh φ hφ⟩

def weightedTopHilbertRepresentative (u : WeightedTopHilbert E g μ hμ h hh φ hφ) :
    WeightedTopSection E g μ hμ h hh φ hφ :=
  (realizeWeightedTopSection_surjective E g μ hμ h hh φ hφ u).choose

theorem weightedTopHilbertRepresentative_realize (u : WeightedTopHilbert E g μ hμ h hh φ hφ) :
    realizeWeightedTopSection E g μ hμ h hh φ hφ (weightedTopHilbertRepresentative E g μ hμ h hh φ hφ u) = u :=
  (realizeWeightedTopSection_surjective E g μ hμ h hh φ hφ u).choose_spec

theorem weightedTopHilbertRepresentative_normSq (u : WeightedTopHilbert E g μ hμ h hh φ hφ) :
    weightedNormSq (r := r) E g.form h μ φ (weightedTopHilbertRepresentative E g μ hμ h hh φ hφ u).1 =
      ENNReal.ofReal (‖u‖ ^ 2) := by
  rw [weightedTopSection_normSq_eq_ofReal E g μ hμ h hh φ hφ]
  have hnorm : ‖realizeWeightedTopSection E g μ hμ h hh φ hφ
      (weightedTopHilbertRepresentative E g μ hμ h hh φ hφ u)‖ =
      ‖weightedTopHilbertRepresentative E g μ hμ h hh φ hφ u‖ := UniformSpace.Completion.norm_coe _
  rw [weightedTopHilbertRepresentative_realize E g μ hμ h hh φ hφ u] at hnorm
  rw [hnorm]

end Yau.LeafProofs.L14Aux

namespace Yau.LeafProofs.L14Aux

open BundleDbar Filter
open scoped Kronecker

theorem sum_fin_one_function {n : ℕ} {V : Type*} [AddCommMonoid V]
    (f : (Fin 1 → Fin n) → V) :
    (∑ I, f I) = ∑ i, f (fun _ => i) := by
  apply Fintype.sum_equiv (Equiv.funUnique (Fin 1) (Fin n)) f (fun i => f (fun _ => i))
  intro I
  congr 1
  funext k
  exact congrArg I (Subsingleton.elim k default)

theorem metricPairing_eq_kronecker {n r : ℕ}
    (G : Matrix (Fin n) (Fin n) ℂ) (H : Matrix (Fin r) (Fin r) ℂ)
    (F V : Fin n → Fin r → ℂ) :
    (∑ i, ∑ j, ∑ α, ∑ β, star (F i α) * H α β * G i j * V j β) =
      star (fun p : Fin n × Fin r => F p.1 p.2) ⬝ᵥ
        (G ⊗ₖ H) *ᵥ (fun p : Fin n × Fin r => V p.1 p.2) := by
  simp only [dotProduct, Matrix.mulVec, Fintype.sum_prod_type, Pi.star_apply,
    Matrix.kronecker_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro α hα
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro β hβ
  ring

theorem metricPairing_self_nonneg {n r : ℕ}
    (G : Matrix (Fin n) (Fin n) ℂ) (hG : G.PosDef)
    (H : Matrix (Fin r) (Fin r) ℂ) (hH : H.PosDef) (F : Fin n → Fin r → ℂ) :
    0 ≤ (∑ i, ∑ j, ∑ α, ∑ β, star (F i α) * H α β * G i j * F j β).re := by
  rw [metricPairing_eq_kronecker]
  exact (Complex.nonneg_iff.mp ((hG.kronecker hH).posSemidef.dotProduct_mulVec_nonneg _)).1

variable {n r : ℕ} {M : ComplexManifold n}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

theorem coefficientInner_eq_kronecker (g : HermitianField M) (h : Metric E) (x : M.Carrier)
    (F V : Fin n → Fin r → ℂ) :
    coefficientInner (r := r) E g h x F V =
      (gMat g x)⁻¹.det * (star (fun p : Fin n × Fin r => F p.1 p.2) ⬝ᵥ
        ((gMat g x)⁻¹ ⊗ₖ BundleDbar.metricMatrix (r := r) E h x (chartPt x x)) *ᵥ
          (fun p : Fin n × Fin r => V p.1 p.2)) := by
  unfold coefficientInner
  rw [metricPairing_eq_kronecker]

theorem coefficientInner_self_nonneg (g : HermitianField M) (h : Metric E) (x : M.Carrier)
    (F : Fin n → Fin r → ℂ) : 0 ≤ (coefficientInner (r := r) E g h x F F).re := by
  have hz : chartPt x x ∈ localDomain (r := r) E x := by
    refine ⟨mem_extChartAt_target x, ?_⟩
    change chartInv x (chartPt x x) ∈ (localTriv (r := r) E x).baseSet
    rw [chartInv_chartPt_of_mem x x (mem_chart_source _ _)]
    exact FiberBundle.mem_baseSet_trivializationAt' x
  have hi : (gMat g x)⁻¹.det.im = 0 := matrix_isHermitian_det_im _ (gMat_posDef g x).inv.isHermitian
  unfold coefficientInner
  rw [Complex.mul_re, hi, zero_mul, sub_zero]
  exact mul_nonneg (Complex.nonneg_iff.mp (gMat_posDef g x).inv.posSemidef.det_nonneg).1
    (metricPairing_self_nonneg _ (gMat_posDef g x).inv _ (metricMatrix_posDef E h x (chartPt x x) hz) F)

theorem formNormSq_one_eq_coefficientInner (g : HermitianField M) (h : Metric E)
    (u : NQForm E 1) (x : M.Carrier) :
    BundleDbar.formNormSq (r := r) E g h u x =
      (coefficientInner (r := r) E g h x
        (fun i α => coefficients (r := r) E u x (chartPt x x) (fun _ => i) α)
        (fun i α => coefficients (r := r) E u x (chartPt x x) (fun _ => i) α)).re := by
  have hi : (gMat g x)⁻¹.det.im = 0 := matrix_isHermitian_det_im _ (gMat_posDef g x).inv.isHermitian
  unfold BundleDbar.formNormSq coefficientInner
  simp only [Nat.factorial_one, Nat.cast_one, inv_one, one_mul, Fin.prod_univ_one,
    sum_fin_one_function, Complex.mul_re, hi, zero_mul, sub_zero]
  congr 2
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro α hα
  apply Finset.sum_congr rfl
  intro β hβ
  ring

theorem formNormSq_one_nonneg (g : HermitianField M) (h : Metric E)
    (u : NQForm E 1) (x : M.Carrier) :
    0 ≤ BundleDbar.formNormSq (r := r) E g h u x := by
  rw [formNormSq_one_eq_coefficientInner E g h u x]
  exact coefficientInner_self_nonneg E g h x _

theorem coefficientInner_self_pos (g : HermitianField M) (h : Metric E) (x : M.Carrier)
    (F : Fin n → Fin r → ℂ) (hF : F ≠ 0) :
    0 < (coefficientInner (r := r) E g h x F F).re := by
  have hz : chartPt x x ∈ localDomain (r := r) E x := by
    refine ⟨mem_extChartAt_target x, ?_⟩
    change chartInv x (chartPt x x) ∈ (localTriv (r := r) E x).baseSet
    rw [chartInv_chartPt_of_mem x x (mem_chart_source _ _)]
    exact FiberBundle.mem_baseSet_trivializationAt' x
  have hflat : (fun p : Fin n × Fin r => F p.1 p.2) ≠ 0 := by
    intro hf
    apply hF
    funext i α
    exact congrFun hf (i, α)
  have hi : (gMat g x)⁻¹.det.im = 0 := matrix_isHermitian_det_im _ (gMat_posDef g x).inv.isHermitian
  rw [coefficientInner_eq_kronecker E g h x, Complex.mul_re, hi, zero_mul, sub_zero]
  apply mul_pos (Complex.pos_iff.mp (gMat_posDef g x).inv.det_pos).1
  exact (Complex.pos_iff.mp (((gMat_posDef g x).inv.kronecker
    (metricMatrix_posDef E h x (chartPt x x) hz)).dotProduct_mulVec_pos hflat)).1

theorem coefficientInner_self_eq_zero_iff (g : HermitianField M) (h : Metric E) (x : M.Carrier)
    (F : Fin n → Fin r → ℂ) : (coefficientInner (r := r) E g h x F F).re = 0 ↔ F = 0 := by
  constructor
  · intro hz
    by_contra hf
    have hp := coefficientInner_self_pos E g h x F hf
    rw [hz] at hp
    exact lt_irrefl 0 hp
  · intro hf
    subst F
    simp only [coefficientInner, Pi.zero_apply, star_zero, zero_mul, Finset.sum_const_zero,
      mul_zero, Complex.zero_re]

theorem formNormSq_one_eq_zero_iff_coefficients (g : HermitianField M) (h : Metric E)
    (u : NQForm E 1) (x : M.Carrier) :
    BundleDbar.formNormSq (r := r) E g h u x = 0 ↔
      ∀ i α, coefficients (r := r) E u x (chartPt x x) (fun _ => i) α = 0 := by
  rw [formNormSq_one_eq_coefficientInner E g h u x, coefficientInner_self_eq_zero_iff E g h x]
  constructor
  · intro hf i α
    exact congrFun (congrFun hf i) α
  · intro hf
    exact funext (fun i => funext (hf i))

end Yau.LeafProofs.L14Aux

namespace Yau.LeafProofs.L14Aux

open BundleDbar Filter

section AntiOneAlgebra
variable {V W ι : Type*} [AddCommGroup V] [Module ℂ V] [Module ℝ V]
  [AddCommGroup W] [Module ℂ W] [Module ℝ W]
  [Fintype ι] [DecidableEq ι]

theorem antiOne_apply_basis_expansion (b : Basis ι ℂ V)
    (A : V [⋀^Fin 1]→ₗ[ℝ] W)
    (hA : ∀ (v : Fin 1 → V) (i : Fin 1) (c : ℂ),
      A (Function.update v i (c • v i)) = star c • A v) (v : V) :
    A (fun _ => v) = ∑ i, star (b.repr v i) • A (fun _ => b i) := by
  let L : V →ₗ[ℝ] W := (AlternatingMap.ofSubsingleton ℝ V W (0 : Fin 1)).symm A
  have hL : ∀ w : V, L w = A (fun _ => w) := by intro w; rfl
  have hscale : ∀ (c : ℂ) (w : V), L (c • w) = star c • L w := by
    intro c w
    have he : Function.update (fun _ : Fin 1 => w) 0 (c • w) = (fun _ => c • w) := by
      funext k
      have hk : k = 0 := Subsingleton.elim _ _
      subst k
      simp
    have ha := hA (fun _ => w) 0 c
    rw [he] at ha
    exact ha
  change L v = _
  calc
    _ = L (∑ i, b.repr v i • b i) := congrArg L (b.sum_repr v).symm
    _ = ∑ i, L (b.repr v i • b i) := map_sum L _ _
    _ = _ := Finset.sum_congr rfl (fun i _ => hscale (b.repr v i) (b i))

theorem antiOne_eq_zero_of_apply_basis_eq_zero (b : Basis ι ℂ V)
    (A : V [⋀^Fin 1]→ₗ[ℝ] W)
    (hA : ∀ (v : Fin 1 → V) (i : Fin 1) (c : ℂ),
      A (Function.update v i (c • v i)) = star c • A v)
    (hzero : ∀ i, A (fun _ => b i) = 0) : A = 0 := by
  apply AlternatingMap.ext
  intro v
  have hv : v = fun _ => v 0 := by
    funext k
    exact congrArg v (Subsingleton.elim k 0)
  rw [hv, antiOne_apply_basis_expansion b A hA]
  simp only [hzero, smul_zero, Finset.sum_const_zero, AlternatingMap.zero_apply]
end AntiOneAlgebra

variable {n r : ℕ} {M : ComplexManifold n}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

theorem coefficients_at_center {q : ℕ} (u : NQForm E q) (x : M.Carrier)
    (I : Fin q → Fin n) :
    coefficients (r := r) E u x (chartPt x x) I =
      (localTriv (r := r) E x).continuousLinearMapAt ℂ x
        (((u x).1 (fun k => chartVec x x (stdVec (I k))))
          (fun k => chartVec x x (stdVec k))) := by
  let F : M.Carrier → ComplexVector r := fun y =>
    (localTriv (r := r) E x).continuousLinearMapAt ℂ y
      (((u y).1 (fun k => chartVec x y (stdVec (I k)))) (fun k => chartVec x y (stdVec k)))
  exact congrArg F (chartInv_chartPt_of_mem x x (mem_chart_source _ _))

theorem oneForm_tensor_eq_zero_of_coefficients_eq_zero (u : NQForm E 1) (x : M.Carrier)
    (hzero : ∀ i α, coefficients (r := r) E u x (chartPt x x) (fun _ => i) α = 0) :
    u x = (0 : NQForm E 1) x := by
  let b := chartFrameBasis x x (mem_extChartAt_source x)
  let d := bundleFrameBasis (r := r) E x x (FiberBundle.mem_baseSet_trivializationAt' x)
  apply Subtype.ext
  rw [nqForm_zero_apply]
  apply antiOne_eq_zero_of_apply_basis_eq_zero b (u x).1 (u x).2
  intro i
  apply alternating_eq_zero_of_apply_basis_eq_zero d b
  apply d.ext_elem
  intro α
  have heOuter : (fun _ : Fin 1 => b i) = (fun _ => chartVec x x (stdVec i)) :=
    funext (fun _ => chartFrameBasis_apply x x (mem_extChartAt_source x) i)
  have heHol : b = (fun k => chartVec x x (stdVec k)) :=
    funext (fun k => chartFrameBasis_apply x x (mem_extChartAt_source x) k)
  have heval : ((u x).1 (fun _ => b i)) b =
      ((u x).1 (fun _ => chartVec x x (stdVec i))) (fun k => chartVec x x (stdVec k)) :=
    congrArg₂ (fun w v => ((u x).1 w) v) heOuter heHol
  have hc := congrArg (fun v : ComplexVector r => v α) (coefficients_at_center E u x (fun _ => i))
  have hv : d.repr (((u x).1 (fun _ => b i)) b) α = 0 := by
    calc
      _ = (localTriv (r := r) E x).continuousLinearMapAt ℂ x (((u x).1 (fun _ => b i)) b) α :=
        bundleFrameBasis_repr E x x (FiberBundle.mem_baseSet_trivializationAt' x) _ α
      _ = (localTriv (r := r) E x).continuousLinearMapAt ℂ x
          (((u x).1 (fun _ => chartVec x x (stdVec i))) (fun k => chartVec x x (stdVec k))) α :=
        congrArg (fun v : E x => (localTriv (r := r) E x).continuousLinearMapAt ℂ x v α) heval
      _ = coefficients (r := r) E u x (chartPt x x) (fun _ => i) α := hc.symm
      _ = 0 := hzero i α
  simpa only [map_zero, Finsupp.zero_apply] using hv

theorem formNormSq_zero (g : HermitianField M) (h : Metric E) (q : ℕ) (x : M.Carrier) :
    BundleDbar.formNormSq (r := r) E g h (0 : NQForm E q) x = 0 := by
  unfold BundleDbar.formNormSq
  simp only [coefficients_zero, star_zero, zero_mul, Finset.sum_const_zero, Complex.zero_re, mul_zero]

theorem formNormSq_one_eq_zero_iff (g : HermitianField M) (h : Metric E)
    (u : NQForm E 1) (x : M.Carrier) :
    BundleDbar.formNormSq (r := r) E g h u x = 0 ↔ u x = (0 : NQForm E 1) x := by
  constructor
  · intro hz
    exact oneForm_tensor_eq_zero_of_coefficients_eq_zero E u x
      ((formNormSq_one_eq_zero_iff_coefficients E g h u x).mp hz)
  · intro hz
    exact (formNormSq_congr_at E g h u (0 : NQForm E 1) x hz).trans (formNormSq_zero E g h 1 x)

end Yau.LeafProofs.L14Aux

namespace Yau.LeafProofs.L14Aux

open BundleDbar Filter

section FrameAlgebra
variable {V W ι κ : Type*} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W] [Fintype ι] [DecidableEq ι]

theorem alternating_hermitian_complex_ratio_basis_independent
    (d : Basis κ ℂ W) (hV : Yau.HermitianInnerProduct V) (hW : Yau.HermitianInnerProduct W)
    (b c : Basis ι ℂ V) (A B : V [⋀^ι]→ₗ[ℂ] W) :
    hW.toFun (A c) (B c) / ((hermitianGram hV c).det.re : ℂ) =
      hW.toFun (A b) (B b) / ((hermitianGram hV b).det.re : ℂ) := by
  rw [alternating_apply_basis_change d b c A, alternating_apply_basis_change d b c B,
    hW.map_smul_left, hW.map_smul_right]
  have he (z w : ℂ) : star z * (w * z) = (Complex.normSq z : ℂ) * w := by
    calc
      _ = (star z * z) * w := by ring
      _ = _ := by rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self]
  rw [he, hermitianGram_det_changeBasis_re hV b c, Complex.ofReal_mul]
  apply mul_div_mul_left
  apply mt Complex.ofReal_eq_zero.mp
  apply mt Complex.normSq_eq_zero.mp
  exact (b.isUnit_det c).ne_zero
end FrameAlgebra

theorem trace_inv_congruence {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G B A : Matrix ι ι ℂ) (hA : IsUnit A.det) :
    ((Aᴴ * G * A)⁻¹ * (Aᴴ * B * A)).trace = (G⁻¹ * B).trace := by
  have hstar : IsUnit (Aᴴ).det := by
    rw [Matrix.det_conjTranspose]
    exact hA.star
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev]
  calc
    _ = (A⁻¹ * (G⁻¹ * B) * A).trace := by
      congr 1
      simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hstar]
    _ = (A * A⁻¹ * (G⁻¹ * B)).trace := Matrix.trace_mul_cycle A⁻¹ (G⁻¹ * B) A
    _ = _ := by rw [Matrix.mul_nonsing_inv A hA, Matrix.one_mul]

section AntiContractionAlgebra
variable {V W ι : Type*} [AddCommGroup V] [Module ℂ V] [Module ℝ V]
  [AddCommGroup W] [Module ℂ W] [Module ℝ W] [Fintype ι] [DecidableEq ι]

def antiOneGram (hW : Yau.HermitianInnerProduct W) (A B : V [⋀^Fin 1]→ₗ[ℝ] W)
    (b : Basis ι ℂ V) : Matrix ι ι ℂ :=
  fun i j => hW.toFun (A (fun _ => b j)) (B (fun _ => b i))

theorem antiOneGram_changeBasis (hW : Yau.HermitianInnerProduct W)
    (A B : V [⋀^Fin 1]→ₗ[ℝ] W)
    (hA : ∀ (v : Fin 1 → V) (i : Fin 1) (c : ℂ),
      A (Function.update v i (c • v i)) = star c • A v)
    (hB : ∀ (v : Fin 1 → V) (i : Fin 1) (c : ℂ),
      B (Function.update v i (c • v i)) = star c • B v) (b c : Basis ι ℂ V) :
    antiOneGram hW A B c = (b.toMatrix c)ᴴ * antiOneGram hW A B b * b.toMatrix c := by
  ext i j
  change hW.toFun (A (fun _ => c j)) (B (fun _ => c i)) =
    ∑ p, (∑ q, star ((b.toMatrix c) q i) * hW.toFun (A (fun _ => b p)) (B (fun _ => b q))) * (b.toMatrix c) p j
  rw [antiOne_apply_basis_expansion b A hA (c j), antiOne_apply_basis_expansion b B hB (c i)]
  simp only [hermitian_sum_left, hermitian_sum_right, hW.map_smul_left, hW.map_smul_right,
    star_star, Basis.toMatrix_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro q hq
  ring

theorem trace_inv_antiOneGram_eq_sum (hV : Yau.HermitianInnerProduct V)
    (hW : Yau.HermitianInnerProduct W) (A B : V [⋀^Fin 1]→ₗ[ℝ] W) (b : Basis ι ℂ V) :
    ((hermitianGram hV b)⁻¹ * antiOneGram hW A B b).trace =
      ∑ i, ∑ j, (hermitianGram hV b)⁻¹ i j * hW.toFun (A (fun _ => b i)) (B (fun _ => b j)) := rfl

theorem antiOneContraction_basis_independent (hV : Yau.HermitianInnerProduct V)
    (hW : Yau.HermitianInnerProduct W) (A B : V [⋀^Fin 1]→ₗ[ℝ] W)
    (hA : ∀ (v : Fin 1 → V) (i : Fin 1) (c : ℂ),
      A (Function.update v i (c • v i)) = star c • A v)
    (hB : ∀ (v : Fin 1 → V) (i : Fin 1) (c : ℂ),
      B (Function.update v i (c • v i)) = star c • B v) (b c : Basis ι ℂ V) :
    ((hermitianGram hV c)⁻¹ * antiOneGram hW A B c).trace =
      ((hermitianGram hV b)⁻¹ * antiOneGram hW A B b).trace := by
  rw [hermitianGram_changeBasis hV b c, antiOneGram_changeBasis hW A B hA hB b c]
  exact trace_inv_congruence _ _ _ (b.isUnit_det c)
end AntiContractionAlgebra

end Yau.LeafProofs.L14Aux

namespace Yau.LeafProofs.L14Aux

open BundleDbar Filter

section OneFrameAlgebra
variable {V W ι κ : Type*} [AddCommGroup V] [Module ℂ V] [Module ℝ V]
  [AddCommGroup W] [Module ℂ W] [Module ℝ W] [IsScalarTower ℝ ℂ W] [Fintype ι] [DecidableEq ι]

def alternatingEvaluationReal (v : ι → V) : (V [⋀^ι]→ₗ[ℂ] W) →ₗ[ℝ] W where
  toFun A := A v
  map_add' A B := rfl
  map_smul' c A := by simp only [RingHom.id_apply, AlternatingMap.smul_apply]

def oneTensorHolEvaluation (A : V [⋀^Fin 1]→ₗ[ℝ] (V [⋀^ι]→ₗ[ℂ] W))
    (b : Basis ι ℂ V) : V [⋀^Fin 1]→ₗ[ℝ] W :=
  (alternatingEvaluationReal b).compAlternatingMap A

theorem oneTensorHolEvaluation_apply (A : V [⋀^Fin 1]→ₗ[ℝ] (V [⋀^ι]→ₗ[ℂ] W))
    (b : Basis ι ℂ V) (v : Fin 1 → V) : oneTensorHolEvaluation A b v = A v b := rfl

theorem oneTensorHolEvaluation_anti (A : V [⋀^Fin 1]→ₗ[ℝ] (V [⋀^ι]→ₗ[ℂ] W))
    (hA : ∀ (v : Fin 1 → V) (i : Fin 1) (c : ℂ),
      A (Function.update v i (c • v i)) = star c • A v) (b : Basis ι ℂ V)
    (v : Fin 1 → V) (i : Fin 1) (c : ℂ) :
    oneTensorHolEvaluation A b (Function.update v i (c • v i)) =
      star c • oneTensorHolEvaluation A b v :=
  congrArg (fun T : V [⋀^ι]→ₗ[ℂ] W => T b) (hA v i c)

def oneTensorFramePairing (hV : Yau.HermitianInnerProduct V) (hW : Yau.HermitianInnerProduct W)
    (hol anti : Basis ι ℂ V) (A B : V [⋀^Fin 1]→ₗ[ℝ] (V [⋀^ι]→ₗ[ℂ] W)) : ℂ :=
  (((hermitianGram hV hol).det.re : ℂ))⁻¹ *
    ((hermitianGram hV anti)⁻¹ * antiOneGram hW (oneTensorHolEvaluation A hol) (oneTensorHolEvaluation B hol) anti).trace

theorem oneTensorFramePairing_eq_sum (hV : Yau.HermitianInnerProduct V) (hW : Yau.HermitianInnerProduct W)
    (hol anti : Basis ι ℂ V) (A B : V [⋀^Fin 1]→ₗ[ℝ] (V [⋀^ι]→ₗ[ℂ] W)) :
    oneTensorFramePairing hV hW hol anti A B =
      ∑ i, ∑ j, (hermitianGram hV anti)⁻¹ i j *
        (hW.toFun (A (fun _ => anti i) hol) (B (fun _ => anti j) hol) /
          ((hermitianGram hV hol).det.re : ℂ)) := by
  unfold oneTensorFramePairing
  rw [trace_inv_antiOneGram_eq_sum]
  simp only [oneTensorHolEvaluation_apply]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [div_eq_mul_inv]
  ring

theorem oneTensorFramePairing_anti_basis_independent (hV : Yau.HermitianInnerProduct V)
    (hW : Yau.HermitianInnerProduct W) (hol b c : Basis ι ℂ V)
    (A B : V [⋀^Fin 1]→ₗ[ℝ] (V [⋀^ι]→ₗ[ℂ] W))
    (hA : ∀ (v : Fin 1 → V) (i : Fin 1) (s : ℂ),
      A (Function.update v i (s • v i)) = star s • A v)
    (hB : ∀ (v : Fin 1 → V) (i : Fin 1) (s : ℂ),
      B (Function.update v i (s • v i)) = star s • B v) :
    oneTensorFramePairing hV hW hol c A B = oneTensorFramePairing hV hW hol b A B := by
  unfold oneTensorFramePairing
  rw [antiOneContraction_basis_independent hV hW _ _
    (oneTensorHolEvaluation_anti A hA hol) (oneTensorHolEvaluation_anti B hB hol) b c]

theorem oneTensorFramePairing_hol_basis_independent (d : Basis κ ℂ W)
    (hV : Yau.HermitianInnerProduct V) (hW : Yau.HermitianInnerProduct W)
    (b c anti : Basis ι ℂ V) (A B : V [⋀^Fin 1]→ₗ[ℝ] (V [⋀^ι]→ₗ[ℂ] W)) :
    oneTensorFramePairing hV hW c anti A B = oneTensorFramePairing hV hW b anti A B := by
  rw [oneTensorFramePairing_eq_sum, oneTensorFramePairing_eq_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [alternating_hermitian_complex_ratio_basis_independent d hV hW b c
    (A (fun _ => anti i)) (B (fun _ => anti j))]

theorem oneTensorFramePairing_basis_independent (d : Basis κ ℂ W)
    (hV : Yau.HermitianInnerProduct V) (hW : Yau.HermitianInnerProduct W)
    (b c : Basis ι ℂ V) (A B : V [⋀^Fin 1]→ₗ[ℝ] (V [⋀^ι]→ₗ[ℂ] W))
    (hA : ∀ (v : Fin 1 → V) (i : Fin 1) (s : ℂ),
      A (Function.update v i (s • v i)) = star s • A v)
    (hB : ∀ (v : Fin 1 → V) (i : Fin 1) (s : ℂ),
      B (Function.update v i (s • v i)) = star s • B v) :
    oneTensorFramePairing hV hW c c A B = oneTensorFramePairing hV hW b b A B := by
  calc
    _ = oneTensorFramePairing hV hW b c A B := oneTensorFramePairing_hol_basis_independent d hV hW b c c A B
    _ = _ := oneTensorFramePairing_anti_basis_independent hV hW b b c A B hA hB
end OneFrameAlgebra
end Yau.LeafProofs.L14Aux

namespace Yau.LeafProofs.L14Aux

open BundleDbar Filter

variable {n r : ℕ} {M : ComplexManifold n}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

def oneFormFrameValue (u : NQForm E 1) (a x : M.Carrier) (i : Fin n) : E x :=
  ((u x).1 (fun _ => chartVec a x (stdVec i))) (fun k => chartVec a x (stdVec k))

theorem coefficients_oneFormFrameValue (u : NQForm E 1) (a : M.Carrier) (z : ComplexVector n)
    (i : Fin n) (α : Fin r) :
    coefficients (r := r) E u a z (fun _ => i) α =
      (localTriv (r := r) E a).continuousLinearMapAt ℂ (chartInv a z)
        (oneFormFrameValue E u a (chartInv a z) i) α := rfl

theorem oneFormFrameValue_eq_basis (u : NQForm E 1) (a x : M.Carrier)
    (hx : x ∈ (extChartAt (ComplexModel n) a).source) (i : Fin n) :
    oneFormFrameValue E u a x i =
      ((u x).1 (fun _ => chartFrameBasis a x hx i)) (chartFrameBasis a x hx) := by
  exact congrArg₂ (fun w v => ((u x).1 w) v)
    (funext (fun _ => (chartFrameBasis_apply a x hx i).symm))
    (funext (fun k => (chartFrameBasis_apply a x hx k).symm))

def oneFormPairing (g : HermitianField M) (h : Metric E) (u v : NQForm E 1) (x : M.Carrier) : ℂ :=
  oneTensorFramePairing (g x) (h x) (chartFrameBasis x x (mem_extChartAt_source x))
    (chartFrameBasis x x (mem_extChartAt_source x)) (u x).1 (v x).1

theorem oneFormPairing_in_fixed_chart (g : HermitianField M) (h : Metric E) (u v : NQForm E 1)
    (a x : M.Carrier) (hx : x ∈ (extChartAt (ComplexModel n) a).source) :
    oneFormPairing E g h u v x = oneTensorFramePairing (g x) (h x) (chartFrameBasis a x hx)
      (chartFrameBasis a x hx) (u x).1 (v x).1 :=
  oneTensorFramePairing_basis_independent
    (Module.Free.chooseBasis ℂ (E x))
    (g x) (h x) (chartFrameBasis a x hx) (chartFrameBasis x x (mem_extChartAt_source x))
    (u x).1 (v x).1 (u x).2 (v x).2

theorem oneFormPairing_inChart (g : HermitianField M) (h : Metric E) (u v : NQForm E 1)
    (a : M.Carrier) (z : ComplexVector n) (hz : z ∈ localDomain (r := r) E a) :
    oneFormPairing E g h u v (chartInv a z) =
      ∑ i, ∑ j, (hMat g a z)⁻¹ i j *
        ((∑ α, ∑ β, star (coefficients (r := r) E u a z (fun _ => i) α) *
          BundleDbar.metricMatrix (r := r) E h a z α β * coefficients (r := r) E v a z (fun _ => j) β) /
            ((hMat g a z).det.re : ℂ)) := by
  let x := chartInv a z
  let hx := (extChartAt (ComplexModel n) a).map_target hz.1
  let b := chartFrameBasis a x hx
  have hgram : hermitianGram (g x) b = hMat g a z := (frameGram_eq_hermitianGram g a x hx).symm
  calc
    _ = oneTensorFramePairing (g x) (h x) b b (u x).1 (v x).1 := oneFormPairing_in_fixed_chart E g h u v a x hx
    _ = ∑ i, ∑ j, (hermitianGram (g x) b)⁻¹ i j *
        ((h x).toFun (((u x).1 (fun _ => b i)) b) (((v x).1 (fun _ => b j)) b) /
          ((hermitianGram (g x) b).det.re : ℂ)) := oneTensorFramePairing_eq_sum _ _ _ _ _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      have hmetric : (∑ α, ∑ β, star (coefficients (r := r) E u a z (fun _ => i) α) *
          BundleDbar.metricMatrix (r := r) E h a z α β * coefficients (r := r) E v a z (fun _ => j) β) =
          (h x).toFun (oneFormFrameValue E u a x i) (oneFormFrameValue E v a x j) := by
        simp_rw [coefficients_oneFormFrameValue]
        exact metricMatrix_pairing E h a z hz _ _
      have hp : (h x).toFun (((u x).1 (fun _ => b i)) b) (((v x).1 (fun _ => b j)) b) =
          ∑ α, ∑ β, star (coefficients (r := r) E u a z (fun _ => i) α) *
            BundleDbar.metricMatrix (r := r) E h a z α β * coefficients (r := r) E v a z (fun _ => j) β :=
        (congrArg₂ (h x).toFun (oneFormFrameValue_eq_basis E u a x hx i).symm
          (oneFormFrameValue_eq_basis E v a x hx j).symm).trans hmetric.symm
      calc
        _ = (hMat g a z)⁻¹ i j *
            ((h x).toFun (((u x).1 (fun _ => b i)) b) (((v x).1 (fun _ => b j)) b) / ((hMat g a z).det.re : ℂ)) :=
          congrArg (fun C : Matrix (Fin n) (Fin n) ℂ => C⁻¹ i j *
            ((h x).toFun (((u x).1 (fun _ => b i)) b) (((v x).1 (fun _ => b j)) b) / (C.det.re : ℂ))) hgram
        _ = _ := congrArg (fun w : ℂ => (hMat g a z)⁻¹ i j * (w / ((hMat g a z).det.re : ℂ))) hp

theorem oneFormPairing_eq_coefficientInner (g : HermitianField M) (h : Metric E)
    (u v : NQForm E 1) (x : M.Carrier) :
    oneFormPairing E g h u v x = coefficientInner (r := r) E g h x
      (fun i α => coefficients (r := r) E u x (chartPt x x) (fun _ => i) α)
      (fun i α => coefficients (r := r) E v x (chartPt x x) (fun _ => i) α) := by
  have hz : chartPt x x ∈ localDomain (r := r) E x := by
    refine ⟨mem_extChartAt_target x, ?_⟩
    change chartInv x (chartPt x x) ∈ (localTriv (r := r) E x).baseSet
    rw [chartInv_chartPt_of_mem x x (mem_chart_source _ _)]
    exact FiberBundle.mem_baseSet_trivializationAt' x
  have hp := congrArg (fun y => oneFormPairing E g h u v y)
    (chartInv_chartPt_of_mem x x (mem_chart_source _ _))
  have hs := oneFormPairing_inChart (r := r) E g h u v x (chartPt x x) hz
  have hs' : oneFormPairing E g h u v x =
      ∑ i, ∑ j, (gMat g x)⁻¹ i j *
        ((∑ α, ∑ β, star (coefficients (r := r) E u x (chartPt x x) (fun _ => i) α) *
          BundleDbar.metricMatrix (r := r) E h x (chartPt x x) α β *
            coefficients (r := r) E v x (chartPt x x) (fun _ => j) β) /
          ((gMat g x).det.re : ℂ)) := hp.symm.trans hs
  have hd : (gMat g x)⁻¹.det = (((gMat g x).det.re)⁻¹ : ℝ) := by
    apply Complex.ext
    · exact gMat_inv_det_re g x
    · exact matrix_isHermitian_det_im _ (gMat_posDef g x).inv.isHermitian
  rw [hs', coefficientInner, hd, Complex.ofReal_inv]
  simp_rw [div_eq_mul_inv, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro α hα
  apply Finset.sum_congr rfl
  intro β hβ
  ring

theorem oneFormPairing_self_re (g : HermitianField M) (h : Metric E) (u : NQForm E 1) (x : M.Carrier) :
    (oneFormPairing E g h u u x).re = BundleDbar.formNormSq (r := r) E g h u x := by
  rw [oneFormPairing_eq_coefficientInner (r := r) E g h u u x]
  exact (formNormSq_one_eq_coefficientInner E g h u x).symm

theorem formNormSq_one_inChart (g : HermitianField M) (h : Metric E)
    (u : NQForm E 1) (a : M.Carrier) (z : ComplexVector n) (hz : z ∈ localDomain (r := r) E a) :
    BundleDbar.formNormSq (r := r) E g h u (chartInv a z) =
      (∑ i, ∑ j, (hMat g a z)⁻¹ i j *
        ((∑ α, ∑ β, star (coefficients (r := r) E u a z (fun _ => i) α) *
          BundleDbar.metricMatrix (r := r) E h a z α β * coefficients (r := r) E u a z (fun _ => j) β) /
            ((hMat g a z).det.re : ℂ))).re :=
  (oneFormPairing_self_re (r := r) E g h u (chartInv a z)).symm.trans
    (congrArg Complex.re (oneFormPairing_inChart E g h u u a z hz))

end Yau.LeafProofs.L14Aux

namespace Yau.LeafProofs.L14Aux

open BundleDbar Filter

variable {n r : ℕ} {M : ComplexManifold n}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

theorem aemeasurable_complex_of_bundleCharts (g : HermitianField M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g μ) (F : M.Carrier → ℂ)
    (hF : ∀ a, AEMeasurable (fun z => F (chartInv a z))
      ((lebesgueC n).restrict (localDomain (r := r) E a))) : AEMeasurable F μ := by
  have hre := aemeasurable_of_bundleCharts (r := r) E g μ hμ (fun x => (F x).re)
    (fun a => Complex.measurable_re.comp_aemeasurable (hF a))
  have him := aemeasurable_of_bundleCharts (r := r) E g μ hμ (fun x => (F x).im)
    (fun a => Complex.measurable_im.comp_aemeasurable (hF a))
  have hm : AEMeasurable (fun x => ((F x).re : ℂ) + ((F x).im : ℂ) * Complex.I) μ :=
    (Complex.continuous_ofReal.measurable.comp_aemeasurable hre).add
      ((Complex.continuous_ofReal.measurable.comp_aemeasurable him).mul_const Complex.I)
  convert hm using 1
  funext x
  exact (Complex.re_add_im _).symm

theorem oneFormPairing_inChart_aemeasurable (g : Yau.SmoothMetric M)
    (h : Metric E) (hh : BundleDbar.SmoothMetric (r := r) E h)
    (u v : NQForm E 1) (hu : LocallyL2 (r := r) E u) (hv : LocallyL2 (r := r) E v) (a : M.Carrier) :
    AEMeasurable (fun z => oneFormPairing E g.form h u v (chartInv a z))
      ((lebesgueC n).restrict (localDomain (r := r) E a)) := by
  have hD : AEMeasurable (fun z => ((hMat g.form a z).det.re : ℂ))
      ((lebesgueC n).restrict (localDomain (r := r) E a)) := by
    apply Complex.continuous_ofReal.measurable.comp_aemeasurable
    exact (((Complex.continuous_re.comp_continuousOn
      (L18Aux.contDiffOn_matrix_det (L18Aux.hMat_contDiffOn g a)).continuousOn).mono
        Set.inter_subset_left).aestronglyMeasurable (localDomain_isOpen E a).measurableSet).aemeasurable
  have hInv : ∀ i j, AEMeasurable (fun z => (hMat g.form a z)⁻¹ i j)
      ((lebesgueC n).restrict (localDomain (r := r) E a)) := fun i j =>
    (((L18Aux.hMat_inverse_contDiffOn g a i j).continuousOn.mono Set.inter_subset_left).aestronglyMeasurable
      (localDomain_isOpen E a).measurableSet).aemeasurable
  have hP : ∀ i j, AEMeasurable (fun z =>
      ∑ α, ∑ β, star (coefficients (r := r) E u a z (fun _ => i) α) *
        BundleDbar.metricMatrix (r := r) E h a z α β * coefficients (r := r) E v a z (fun _ => j) β)
      ((lebesgueC n).restrict (localDomain (r := r) E a)) := by
    intro i j
    apply Finset.aemeasurable_fun_sum
    intro α _
    apply Finset.aemeasurable_fun_sum
    intro β _
    have hα := (hu a (fun _ => i) α).1.aemeasurable
    have hβ := (hv a (fun _ => j) β).1.aemeasurable
    have hH := ((hh a α β).continuousOn.aestronglyMeasurable
      (localDomain_isOpen E a).measurableSet (μ := lebesgueC n)).aemeasurable
    exact ((continuous_star.measurable.comp_aemeasurable hα).mul hH).mul hβ
  have hm : AEMeasurable (fun z => ∑ i, ∑ j, (hMat g.form a z)⁻¹ i j *
      ((∑ α, ∑ β, star (coefficients (r := r) E u a z (fun _ => i) α) *
        BundleDbar.metricMatrix (r := r) E h a z α β * coefficients (r := r) E v a z (fun _ => j) β) /
          ((hMat g.form a z).det.re : ℂ))) ((lebesgueC n).restrict (localDomain (r := r) E a)) := by
    apply Finset.aemeasurable_fun_sum
    intro i _
    apply Finset.aemeasurable_fun_sum
    intro j _
    exact (hInv i j).mul ((hP i j).div hD)
  apply hm.congr
  filter_upwards [ae_restrict_mem (localDomain_isOpen E a).measurableSet] with z hz
  exact (oneFormPairing_inChart (r := r) E g.form h u v a z hz).symm

theorem oneFormPairing_aemeasurable (g : Yau.SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (h : Metric E) (hh : BundleDbar.SmoothMetric (r := r) E h)
    (u v : NQForm E 1) (hu : LocallyL2 (r := r) E u) (hv : LocallyL2 (r := r) E v) :
    AEMeasurable (oneFormPairing E g.form h u v) μ :=
  aemeasurable_complex_of_bundleCharts (r := r) E g.form μ hμ _
    (fun a => oneFormPairing_inChart_aemeasurable E g h hh u v hu hv a)

theorem formNormSq_one_aemeasurable (g : Yau.SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (h : Metric E) (hh : BundleDbar.SmoothMetric (r := r) E h)
    (u : NQForm E 1) (hu : LocallyL2 (r := r) E u) :
    AEMeasurable (BundleDbar.formNormSq (r := r) E g.form h u) μ := by
  have hm := Complex.measurable_re.comp_aemeasurable
    (oneFormPairing_aemeasurable E g μ hμ h hh u u hu hu)
  exact hm.congr (Eventually.of_forall (oneFormPairing_self_re (r := r) E g.form h u))

theorem weightedOneNorm_integrable (g : Yau.SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (h : Metric E) (hh : BundleDbar.SmoothMetric (r := r) E h)
    (φ : M.Carrier → ℝ) (hφ : SmoothFn φ)
    (u : NQForm E 1) (hu : WeightedL2 (r := r) E g.form h μ φ u) :
    Integrable (fun x => BundleDbar.formNormSq (r := r) E g.form h u x * Real.exp (-φ x)) μ := by
  have hw : Measurable (fun x => Real.exp (-φ x)) :=
    (Real.continuous_exp.comp (L18Aux.continuous_of_smoothFn hφ).neg).measurable
  have hm := (formNormSq_one_aemeasurable E g μ hμ h hh u hu.1).mul hw.aemeasurable
  refine ⟨hm.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal
    (Eventually.of_forall fun x => mul_nonneg (formNormSq_one_nonneg E g.form h u x) (Real.exp_pos _).le)).mpr hu.2⟩

theorem weightedNormSq_one_eq_ofReal_integral (g : Yau.SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (h : Metric E) (hh : BundleDbar.SmoothMetric (r := r) E h)
    (φ : M.Carrier → ℝ) (hφ : SmoothFn φ)
    (u : NQForm E 1) (hu : WeightedL2 (r := r) E g.form h μ φ u) :
    weightedNormSq (r := r) E g.form h μ φ u = ENNReal.ofReal
      (∫ x, BundleDbar.formNormSq (r := r) E g.form h u x * Real.exp (-φ x) ∂μ) :=
  (ofReal_integral_eq_lintegral_ofReal (weightedOneNorm_integrable E g μ hμ h hh φ hφ u hu)
    (Eventually.of_forall fun x => mul_nonneg (formNormSq_one_nonneg E g.form h u x) (Real.exp_pos _).le)).symm

end Yau.LeafProofs.L14Aux

namespace Yau.LeafProofs.L14Aux

open BundleDbar Filter
open scoped Kronecker

variable {n r : ℕ} {M : ComplexManifold n}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

theorem coefficientInner_add_left (g : HermitianField M) (h : Metric E) (x : M.Carrier)
    (F U V : Fin n → Fin r → ℂ) :
    coefficientInner (r := r) E g h x (F+U) V =
      coefficientInner (r := r) E g h x F V + coefficientInner (r := r) E g h x U V := by
  unfold coefficientInner
  simp only [Pi.add_apply, star_add, add_mul, Finset.sum_add_distrib, mul_add]

theorem coefficientInner_add_right (g : HermitianField M) (h : Metric E) (x : M.Carrier)
    (F U V : Fin n → Fin r → ℂ) :
    coefficientInner (r := r) E g h x F (U+V) =
      coefficientInner (r := r) E g h x F U + coefficientInner (r := r) E g h x F V := by
  unfold coefficientInner
  simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem coefficientInner_smul_left (g : HermitianField M) (h : Metric E) (x : M.Carrier)
    (c : ℂ) (F V : Fin n → Fin r → ℂ) :
    coefficientInner (r := r) E g h x (c • F) V = star c * coefficientInner (r := r) E g h x F V := by
  unfold coefficientInner
  simp only [Pi.smul_apply, smul_eq_mul, star_mul]
  rw [mul_left_comm (star c)]
  congr 1
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro α hα
  apply Finset.sum_congr rfl
  intro β hβ
  ring

theorem coefficientInner_conj_symm (g : HermitianField M) (h : Metric E) (x : M.Carrier)
    (F V : Fin n → Fin r → ℂ) :
    star (coefficientInner (r := r) E g h x V F) = coefficientInner (r := r) E g h x F V := by
  have hz : chartPt x x ∈ localDomain (r := r) E x := by
    refine ⟨mem_extChartAt_target x, ?_⟩
    change chartInv x (chartPt x x) ∈ (localTriv (r := r) E x).baseSet
    rw [chartInv_chartPt_of_mem x x (mem_chart_source _ _)]
    exact FiberBundle.mem_baseSet_trivializationAt' x
  have hK := (gMat_posDef g x).inv.kronecker (metricMatrix_posDef E h x (chartPt x x) hz)
  have hdim : (gMat g x)⁻¹.det.im = 0 := matrix_isHermitian_det_im _ (gMat_posDef g x).inv.isHermitian
  have hdreal : (gMat g x)⁻¹.det = ((gMat g x)⁻¹.det.re : ℂ) := by
    apply Complex.ext
    · rfl
    · exact hdim
  have hdstar : star (gMat g x)⁻¹.det = (gMat g x)⁻¹.det := by
    rw [hdreal]
    simp only [Complex.star_def, Complex.conj_ofReal]
  rw [coefficientInner_eq_kronecker E g h x V F, coefficientInner_eq_kronecker E g h x F V, star_mul, hdstar]
  rw [hK.isHermitian.star_dotProduct_mulVec_comm]
  exact mul_comm _ _

section OnePairFrameAlgebra
variable {V W ι : Type*} [AddCommGroup V] [Module ℂ V] [Module ℝ V]
  [AddCommGroup W] [Module ℂ W] [Module ℝ W] [IsScalarTower ℝ ℂ W]
  [Fintype ι] [DecidableEq ι]

theorem oneTensorFramePairing_add_left (hV : Yau.HermitianInnerProduct V) (hW : Yau.HermitianInnerProduct W)
    (hol anti : Basis ι ℂ V) (A B C : V [⋀^Fin 1]→ₗ[ℝ] (V [⋀^ι]→ₗ[ℂ] W)) :
    oneTensorFramePairing hV hW hol anti (A+B) C =
      oneTensorFramePairing hV hW hol anti A C + oneTensorFramePairing hV hW hol anti B C := by
  simp only [oneTensorFramePairing_eq_sum, AlternatingMap.add_apply, hW.map_add_left,
    add_div, mul_add, Finset.sum_add_distrib]

theorem oneTensorFramePairing_add_right (hV : Yau.HermitianInnerProduct V) (hW : Yau.HermitianInnerProduct W)
    (hol anti : Basis ι ℂ V) (A B C : V [⋀^Fin 1]→ₗ[ℝ] (V [⋀^ι]→ₗ[ℂ] W)) :
    oneTensorFramePairing hV hW hol anti A (B+C) =
      oneTensorFramePairing hV hW hol anti A B + oneTensorFramePairing hV hW hol anti A C := by
  simp only [oneTensorFramePairing_eq_sum, AlternatingMap.add_apply, hW.map_add_right,
    add_div, mul_add, Finset.sum_add_distrib]

theorem oneTensorFramePairing_smul_left (hV : Yau.HermitianInnerProduct V) (hW : Yau.HermitianInnerProduct W)
    (hol anti : Basis ι ℂ V) (c : ℂ) (A B : V [⋀^Fin 1]→ₗ[ℝ] (V [⋀^ι]→ₗ[ℂ] W)) :
    oneTensorFramePairing hV hW hol anti (c • A) B = star c * oneTensorFramePairing hV hW hol anti A B := by
  simp only [oneTensorFramePairing_eq_sum, AlternatingMap.smul_apply, hW.map_smul_left]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [div_eq_mul_inv, div_eq_mul_inv]
  ring

theorem oneTensorFramePairing_smul_right (hV : Yau.HermitianInnerProduct V) (hW : Yau.HermitianInnerProduct W)
    (hol anti : Basis ι ℂ V) (c : ℂ) (A B : V [⋀^Fin 1]→ₗ[ℝ] (V [⋀^ι]→ₗ[ℂ] W)) :
    oneTensorFramePairing hV hW hol anti A (c • B) = c * oneTensorFramePairing hV hW hol anti A B := by
  simp only [oneTensorFramePairing_eq_sum, AlternatingMap.smul_apply, hW.map_smul_right]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [div_eq_mul_inv, div_eq_mul_inv]
  ring

theorem antiOneGram_conjTranspose (hW : Yau.HermitianInnerProduct W)
    (A B : V [⋀^Fin 1]→ₗ[ℝ] W) (b : Basis ι ℂ V) :
    (antiOneGram hW B A b)ᴴ = antiOneGram hW A B b := by
  ext i j
  exact (hW.conjugate_symmetric (A (fun _ => b j)) (B (fun _ => b i))).symm

theorem oneTensorFramePairing_conj_symm (hV : Yau.HermitianInnerProduct V) (hW : Yau.HermitianInnerProduct W)
    (hol anti : Basis ι ℂ V) (A B : V [⋀^Fin 1]→ₗ[ℝ] (V [⋀^ι]→ₗ[ℂ] W)) :
    star (oneTensorFramePairing hV hW hol anti B A) = oneTensorFramePairing hV hW hol anti A B := by
  unfold oneTensorFramePairing
  rw [star_mul, ← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul,
    antiOneGram_conjTranspose, (hermitianGram_posDef hV anti).inv.isHermitian.eq,
    Matrix.trace_mul_comm]
  simp only [Complex.star_def, map_inv₀, Complex.conj_ofReal]
  exact mul_comm _ _

end OnePairFrameAlgebra

theorem oneFormPairing_add_left (g : HermitianField M) (h : Metric E)
    (u v w : NQForm E 1) (x : M.Carrier) :
    oneFormPairing E g h (u+v) w x = oneFormPairing E g h u w x + oneFormPairing E g h v w x :=
  oneTensorFramePairing_add_left (g x) (h x) _ _ (u x).1 (v x).1 (w x).1

theorem oneFormPairing_add_right (g : HermitianField M) (h : Metric E)
    (u v w : NQForm E 1) (x : M.Carrier) :
    oneFormPairing E g h u (v+w) x = oneFormPairing E g h u v x + oneFormPairing E g h u w x :=
  oneTensorFramePairing_add_right (g x) (h x) _ _ (u x).1 (v x).1 (w x).1

theorem oneFormPairing_smul_left (g : HermitianField M) (h : Metric E)
    (c : ℂ) (u v : NQForm E 1) (x : M.Carrier) :
    oneFormPairing E g h (c • u) v x = star c * oneFormPairing E g h u v x :=
  oneTensorFramePairing_smul_left (g x) (h x) _ _ c (u x).1 (v x).1

theorem oneFormPairing_smul_right (g : HermitianField M) (h : Metric E)
    (c : ℂ) (u v : NQForm E 1) (x : M.Carrier) :
    oneFormPairing E g h u (c • v) x = c * oneFormPairing E g h u v x :=
  oneTensorFramePairing_smul_right (g x) (h x) _ _ c (u x).1 (v x).1

theorem oneFormPairing_conj_symm (g : HermitianField M) (h : Metric E)
    (u v : NQForm E 1) (x : M.Carrier) :
    star (oneFormPairing E g h v u x) = oneFormPairing E g h u v x :=
  oneTensorFramePairing_conj_symm (g x) (h x) _ _ (u x).1 (v x).1

def oneFormPointPreInner (g : HermitianField M) (h : Metric E) (x : M.Carrier) :
    PreInnerProductSpace.Core ℂ (NQForm E 1) where
  inner u v := oneFormPairing E g h u v x
  conj_inner_symm u v := oneFormPairing_conj_symm E g h u v x
  re_inner_nonneg u := by
    change 0 ≤ (oneFormPairing E g h u u x).re
    rw [oneFormPairing_self_re (r := r) E g h u x]
    exact formNormSq_one_nonneg E g h u x
  add_left u v w := oneFormPairing_add_left E g h u v w x
  smul_left u v c := oneFormPairing_smul_left E g h c u v x

theorem oneFormPairing_cauchySchwarz (g : HermitianField M) (h : Metric E)
    (u v : NQForm E 1) (x : M.Carrier) :
    Complex.normSq (oneFormPairing E g h u v x) ≤
      BundleDbar.formNormSq (r := r) E g h u x * BundleDbar.formNormSq (r := r) E g h v x := by
  letI : PreInnerProductSpace.Core ℂ (NQForm E 1) := oneFormPointPreInner (r := r) E g h x
  have ht := InnerProductSpace.Core.inner_mul_inner_self_le (𝕜 := ℂ) u v
  change ‖oneFormPairing E g h u v x‖ * ‖oneFormPairing E g h v u x‖ ≤
    (oneFormPairing E g h u u x).re * (oneFormPairing E g h v v x).re at ht
  rw [oneFormPairing_self_re (r := r) E g h u x, oneFormPairing_self_re (r := r) E g h v x] at ht
  have hn : ‖oneFormPairing E g h v u x‖ = ‖oneFormPairing E g h u v x‖ := by
    simpa only [norm_star] using congrArg norm (oneFormPairing_conj_symm E g h u v x)
  rw [hn] at ht
  simpa only [Complex.normSq_eq_norm_sq, pow_two] using ht

end Yau.LeafProofs.L14Aux

namespace Yau.LeafProofs.L14Aux

open BundleDbar Filter

variable {n r : ℕ} {M : ComplexManifold n}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

theorem formNormSq_one_add_le (g : HermitianField M) (h : Metric E)
    (u v : NQForm E 1) (x : M.Carrier) :
    BundleDbar.formNormSq (r := r) E g h (u+v) x ≤
      2 * BundleDbar.formNormSq (r := r) E g h u x + 2 * BundleDbar.formNormSq (r := r) E g h v x := by
  letI : PreInnerProductSpace.Core ℂ (NQForm E 1) := oneFormPointPreInner (r := r) E g h x
  have hp := congrArg Complex.re (InnerProductSpace.Core.inner_add_add_self (𝕜 := ℂ) u v)
  have hm := congrArg Complex.re (InnerProductSpace.Core.inner_sub_sub_self (𝕜 := ℂ) u v)
  change (oneFormPairing E g h (u+v) (u+v) x).re =
    (oneFormPairing E g h u u x + oneFormPairing E g h u v x +
      oneFormPairing E g h v u x + oneFormPairing E g h v v x).re at hp
  change (oneFormPairing E g h (u-v) (u-v) x).re =
    (oneFormPairing E g h u u x - oneFormPairing E g h u v x -
      oneFormPairing E g h v u x + oneFormPairing E g h v v x).re at hm
  simp only [Complex.add_re, Complex.sub_re, oneFormPairing_self_re (r := r) E g h] at hp hm
  nlinarith [formNormSq_one_nonneg (r := r) E g h (u-v) x]

theorem formNormSq_one_smul (g : HermitianField M) (h : Metric E)
    (c : ℂ) (u : NQForm E 1) (x : M.Carrier) :
    BundleDbar.formNormSq (r := r) E g h (c • u) x = Complex.normSq c * BundleDbar.formNormSq (r := r) E g h u x := by
  rw [← oneFormPairing_self_re (r := r) E g h (c • u) x, oneFormPairing_smul_left, oneFormPairing_smul_right]
  have he : star c * (c * oneFormPairing E g h u u x) = (Complex.normSq c : ℂ) * oneFormPairing E g h u u x := by
    rw [← mul_assoc, Complex.star_def, ← Complex.normSq_eq_conj_mul_self]
  rw [he]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    oneFormPairing_self_re (r := r) E g h]

theorem weightedNormSq_one_smul (g : HermitianField M) (h : Metric E)
    (μ : Measure M.Carrier) (φ : M.Carrier → ℝ) (c : ℂ) (u : NQForm E 1) :
    weightedNormSq (r := r) E g h μ φ (c • u) =
      ENNReal.ofReal (Complex.normSq c) * weightedNormSq (r := r) E g h μ φ u := by
  unfold weightedNormSq
  simp_rw [formNormSq_one_smul, mul_assoc, ENNReal.ofReal_mul (Complex.normSq_nonneg c)]
  exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

theorem weightedL2_one_zero (g : HermitianField M) (h : Metric E)
    (μ : Measure M.Carrier) (φ : M.Carrier → ℝ) :
    WeightedL2 (r := r) E g h μ φ (0 : NQForm E 1) := by
  refine ⟨locallyL2_zero E 1, ?_⟩
  simp [weightedNormSq, BundleDbar.formNormSq, coefficients_zero]

theorem weightedL2_one_smul (g : HermitianField M) (h : Metric E)
    (μ : Measure M.Carrier) (φ : M.Carrier → ℝ) (c : ℂ) (u : NQForm E 1)
    (hu : WeightedL2 (r := r) E g h μ φ u) : WeightedL2 (r := r) E g h μ φ (c • u) := by
  refine ⟨locallyL2_smul E c u hu.1, ?_⟩
  rw [weightedNormSq_one_smul]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hu.2


theorem weightedL2_one_add (g : Yau.SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (h : Metric E)
    (hh : BundleDbar.SmoothMetric (r := r) E h) (φ : M.Carrier → ℝ) (hφ : SmoothFn φ)
    (u v : NQForm E 1) (hu : WeightedL2 (r := r) E g.form h μ φ u)
    (hv : WeightedL2 (r := r) E g.form h μ φ v) :
    WeightedL2 (r := r) E g.form h μ φ (u + v) := by
  have hlocal := locallyL2_add E u v hu.1 hv.1
  have hw : Measurable (fun x => Real.exp (-φ x)) :=
    (Real.continuous_exp.comp (L18Aux.continuous_of_smoothFn hφ).neg).measurable
  have hm : AEStronglyMeasurable (fun x => BundleDbar.formNormSq (r := r) E g.form h (u + v) x *
      Real.exp (-φ x)) μ :=
    ((L14Aux.formNormSq_one_aemeasurable E g μ hμ h hh (u + v) hlocal).mul hw.aemeasurable).aestronglyMeasurable
  have hdom := ((L14Aux.weightedOneNorm_integrable E g μ hμ h hh φ hφ u hu).const_mul 2).add
    ((L14Aux.weightedOneNorm_integrable E g μ hμ h hh φ hφ v hv).const_mul 2)
  have hn : ∀ᵐ x ∂μ, 0 ≤ BundleDbar.formNormSq (r := r) E g.form h (u + v) x * Real.exp (-φ x) :=
    Filter.Eventually.of_forall fun x => mul_nonneg (L14Aux.formNormSq_one_nonneg (r := r) E g.form h (u + v) x)
      (Real.exp_pos _).le
  have hi : Integrable (fun x => BundleDbar.formNormSq (r := r) E g.form h (u + v) x * Real.exp (-φ x)) μ := by
    apply hdom.mono' hm
    filter_upwards [hn] with x hnx
    change ‖BundleDbar.formNormSq (r := r) E g.form h (u + v) x * Real.exp (-φ x)‖ ≤
      2 * (BundleDbar.formNormSq (r := r) E g.form h u x * Real.exp (-φ x)) +
        2 * (BundleDbar.formNormSq (r := r) E g.form h v x * Real.exp (-φ x))
    rw [Real.norm_of_nonneg hnx]
    have ht := mul_le_mul_of_nonneg_right (formNormSq_one_add_le (r := r) E g.form h u v x)
      (Real.exp_pos (-φ x)).le
    nlinarith
  exact ⟨hlocal, (hasFiniteIntegral_iff_ofReal hn).mp hi.2⟩

def weightedOneFormSubmodule (g : Yau.SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (h : Metric E)
    (hh : BundleDbar.SmoothMetric (r := r) E h) (φ : M.Carrier → ℝ) (hφ : SmoothFn φ) :
    Submodule ℂ (NQForm E 1) where
  carrier := {u | WeightedL2 (r := r) E g.form h μ φ u}
  zero_mem' := weightedL2_one_zero E g.form h μ φ
  add_mem' := fun hu hv => weightedL2_one_add E g μ hμ h hh φ hφ _ _ hu hv
  smul_mem' := fun c u hu => weightedL2_one_smul E g.form h μ φ c u hu

def weightedOnePairing (g : HermitianField M) (h : Metric E) (φ : M.Carrier → ℝ)
    (u v : NQForm E 1) (x : M.Carrier) : ℂ :=
  oneFormPairing E g h u v x * (Real.exp (-φ x) : ℂ)

theorem weightedOnePairing_self_re (g : HermitianField M) (h : Metric E)
    (φ : M.Carrier → ℝ) (u : NQForm E 1) (x : M.Carrier) :
    (weightedOnePairing E g h φ u u x).re =
      BundleDbar.formNormSq (r := r) E g h u x * Real.exp (-φ x) := by
  simp only [weightedOnePairing, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero]
  rw [oneFormPairing_self_re (r := r)]

theorem weightedOnePairing_integrable (g : Yau.SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (h : Metric E)
    (hh : BundleDbar.SmoothMetric (r := r) E h) (φ : M.Carrier → ℝ) (hφ : SmoothFn φ)
    (u v : NQForm E 1) (hu : WeightedL2 (r := r) E g.form h μ φ u)
    (hv : WeightedL2 (r := r) E g.form h μ φ v) :
    Integrable (weightedOnePairing E g.form h φ u v) μ := by
  have hw : AEMeasurable (fun x => (Real.exp (-φ x) : ℂ)) μ :=
    Complex.continuous_ofReal.measurable.comp_aemeasurable
      (Real.continuous_exp.comp (L18Aux.continuous_of_smoothFn hφ).neg).measurable.aemeasurable
  have hm : AEStronglyMeasurable (weightedOnePairing E g.form h φ u v) μ :=
    ((oneFormPairing_aemeasurable E g μ hμ h hh u v hu.1 hv.1).mul hw).aestronglyMeasurable
  have ha : ∀ᵐ x ∂μ, 0 ≤ BundleDbar.formNormSq (r := r) E g.form h u x * Real.exp (-φ x) :=
    Filter.Eventually.of_forall fun x => mul_nonneg (formNormSq_one_nonneg (r := r) E g.form h u x) (Real.exp_pos _).le
  have hb : ∀ᵐ x ∂μ, 0 ≤ BundleDbar.formNormSq (r := r) E g.form h v x * Real.exp (-φ x) :=
    Filter.Eventually.of_forall fun x => mul_nonneg (formNormSq_one_nonneg (r := r) E g.form h v x) (Real.exp_pos _).le
  have hbound : ∀ᵐ x ∂μ, Complex.normSq (weightedOnePairing E g.form h φ u v x) ≤
      (BundleDbar.formNormSq (r := r) E g.form h u x * Real.exp (-φ x)) *
        (BundleDbar.formNormSq (r := r) E g.form h v x * Real.exp (-φ x)) := by
    apply Filter.Eventually.of_forall
    intro x
    unfold weightedOnePairing
    rw [Complex.normSq_mul, Complex.normSq_ofReal]
    calc
      _ ≤ (BundleDbar.formNormSq (r := r) E g.form h u x * BundleDbar.formNormSq (r := r) E g.form h v x) *
          (Real.exp (-φ x) * Real.exp (-φ x)) :=
        mul_le_mul_of_nonneg_right (oneFormPairing_cauchySchwarz (r := r) E g.form h u v x)
          (mul_self_nonneg (Real.exp (-φ x)))
      _ = _ := by ring
  exact integrable_of_normSq_le_mul μ _ _ _ hm
    (weightedOneNorm_integrable E g μ hμ h hh φ hφ u hu)
    (weightedOneNorm_integrable E g μ hμ h hh φ hφ v hv) ha hb hbound

def weightedOneInner (g : HermitianField M) (μ : Measure M.Carrier) (h : Metric E)
    (φ : M.Carrier → ℝ) (u v : NQForm E 1) : ℂ :=
  ∫ x, weightedOnePairing E g h φ u v x ∂μ

@[instance_reducible]
def weightedOneFormPreInner (g : Yau.SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (h : Metric E)
    (hh : BundleDbar.SmoothMetric (r := r) E h) (φ : M.Carrier → ℝ) (hφ : SmoothFn φ) :
    PreInnerProductSpace.Core ℂ (weightedOneFormSubmodule (r := r) E g μ hμ h hh φ hφ) where
  inner u v := weightedOneInner E g.form μ h φ u.1 v.1
  conj_inner_symm u v := by
    change star (∫ x, weightedOnePairing E g.form h φ v.1 u.1 x ∂μ) =
      ∫ x, weightedOnePairing E g.form h φ u.1 v.1 x ∂μ
    calc
      _ = ∫ x, star (weightedOnePairing E g.form h φ v.1 u.1 x) ∂μ := (integral_conj (f := weightedOnePairing E g.form h φ v.1 u.1)).symm
      _ = _ := by
        apply integral_congr_ae
        apply Filter.Eventually.of_forall
        intro x
        change star (oneFormPairing E g.form h v.1 u.1 x * (Real.exp (-φ x) : ℂ)) =
          oneFormPairing E g.form h u.1 v.1 x * (Real.exp (-φ x) : ℂ)
        rw [star_mul, oneFormPairing_conj_symm,
          show star (Real.exp (-φ x) : ℂ) = (Real.exp (-φ x) : ℂ) from by
            simp only [Complex.star_def, Complex.conj_ofReal]]
        ring
  re_inner_nonneg u := by
    change 0 ≤ (∫ x, weightedOnePairing E g.form h φ u.1 u.1 x ∂μ).re
    have hp := weightedOnePairing_integrable E g μ hμ h hh φ hφ u.1 u.1 u.2 u.2
    have hr : (∫ x, (weightedOnePairing E g.form h φ u.1 u.1 x).re ∂μ) =
        (∫ x, weightedOnePairing E g.form h φ u.1 u.1 x ∂μ).re := by
      simpa only [RCLike.re_eq_complex_re] using integral_re (𝕜 := ℂ) hp
    rw [← hr]
    apply integral_nonneg
    intro x
    change 0 ≤ (weightedOnePairing E g.form h φ u.1 u.1 x).re
    rw [weightedOnePairing_self_re (r := r)]
    exact mul_nonneg (formNormSq_one_nonneg E g.form h u.1 x) (Real.exp_pos _).le
  add_left u v w := by
    change weightedOneInner E g.form μ h φ (u.1 + v.1) w.1 =
      weightedOneInner E g.form μ h φ u.1 w.1 + weightedOneInner E g.form μ h φ v.1 w.1
    unfold weightedOneInner
    calc
      _ = ∫ x, weightedOnePairing E g.form h φ u.1 w.1 x + weightedOnePairing E g.form h φ v.1 w.1 x ∂μ := by
        apply integral_congr_ae
        apply Filter.Eventually.of_forall
        intro x
        unfold weightedOnePairing
        rw [oneFormPairing_add_left, add_mul]
      _ = _ := integral_add (weightedOnePairing_integrable E g μ hμ h hh φ hφ u.1 w.1 u.2 w.2)
        (weightedOnePairing_integrable E g μ hμ h hh φ hφ v.1 w.1 v.2 w.2)
  smul_left u v c := by
    change weightedOneInner E g.form μ h φ (c • u.1) v.1 = star c * weightedOneInner E g.form μ h φ u.1 v.1
    unfold weightedOneInner
    calc
      _ = ∫ x, star c * weightedOnePairing E g.form h φ u.1 v.1 x ∂μ := by
        apply integral_congr_ae
        apply Filter.Eventually.of_forall
        intro x
        unfold weightedOnePairing
        rw [oneFormPairing_smul_left]
        ring
      _ = _ := integral_const_mul _ _

theorem weightedNormSq_one_eq_zero_iff (g : Yau.SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (h : Metric E)
    (hh : BundleDbar.SmoothMetric (r := r) E h) (φ : M.Carrier → ℝ) (hφ : SmoothFn φ)
    (u : NQForm E 1) (hu : LocallyL2 (r := r) E u) :
    weightedNormSq (r := r) E g.form h μ φ u = 0 ↔ ∀ᵐ x ∂μ, u x = (0 : NQForm E 1) x := by
  have hw : Measurable (fun x => Real.exp (-φ x)) :=
    (Real.continuous_exp.comp (L18Aux.continuous_of_smoothFn hφ).neg).measurable
  have hm : AEMeasurable (fun x => ENNReal.ofReal
      (BundleDbar.formNormSq (r := r) E g.form h u x * Real.exp (-φ x))) μ :=
    ENNReal.measurable_ofReal.comp_aemeasurable
      ((formNormSq_one_aemeasurable E g μ hμ h hh u hu).mul hw.aemeasurable)
  unfold weightedNormSq
  rw [lintegral_eq_zero_iff' hm]
  constructor
  · intro hz
    filter_upwards [hz] with x hx
    have hle := ENNReal.ofReal_eq_zero.mp hx
    have hnn := mul_nonneg (formNormSq_one_nonneg (r := r) E g.form h u x) (Real.exp_pos (-φ x)).le
    have hn : BundleDbar.formNormSq (r := r) E g.form h u x = 0 :=
      (mul_eq_zero.mp (le_antisymm hle hnn)).resolve_right (ne_of_gt (Real.exp_pos _))
    exact (formNormSq_one_eq_zero_iff (r := r) E g.form h u x).mp hn
  · intro hz
    filter_upwards [hz] with x hx
    have hn := (formNormSq_one_eq_zero_iff (r := r) E g.form h u x).mpr hx
    simp only [hn, zero_mul, ENNReal.ofReal_zero, Pi.zero_apply]
end Yau.LeafProofs.L14Aux

namespace Yau.LeafProofs.L14Aux

open BundleDbar Filter

variable {n r : ℕ} {M : ComplexManifold n}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

def WeightedOneSection (g : Yau.SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (h : Metric E)
    (hh : BundleDbar.SmoothMetric (r := r) E h) (φ : M.Carrier → ℝ) (hφ : SmoothFn φ) : Type :=
  weightedOneFormSubmodule (r := r) E g μ hμ h hh φ hφ

variable (g : Yau.SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
  (h : Metric E) (hh : BundleDbar.SmoothMetric (r := r) E h) (φ : M.Carrier → ℝ) (hφ : SmoothFn φ)

instance weightedOneSectionAddCommGroup : AddCommGroup (WeightedOneSection E g μ hμ h hh φ hφ) :=
  (weightedOneFormSubmodule (r := r) E g μ hμ h hh φ hφ).addCommGroup

instance weightedOneSectionModule : Module ℂ (WeightedOneSection E g μ hμ h hh φ hφ) :=
  (weightedOneFormSubmodule (r := r) E g μ hμ h hh φ hφ).module

instance weightedOneSectionSeminormedAddCommGroup :
    SeminormedAddCommGroup (WeightedOneSection E g μ hμ h hh φ hφ) := by
  letI : PreInnerProductSpace.Core ℂ (WeightedOneSection E g μ hμ h hh φ hφ) :=
    weightedOneFormPreInner E g μ hμ h hh φ hφ
  exact InnerProductSpace.Core.toSeminormedAddCommGroup (𝕜 := ℂ)

instance weightedOneSectionInnerProductSpace :
    InnerProductSpace ℂ (WeightedOneSection E g μ hμ h hh φ hφ) :=
  InnerProductSpace.ofCore (weightedOneFormPreInner E g μ hμ h hh φ hφ)

def WeightedOneSection.toForm (u : WeightedOneSection E g μ hμ h hh φ hφ) : NQForm E 1 := u.1

theorem WeightedOneSection.toForm_weightedL2 (u : WeightedOneSection E g μ hμ h hh φ hφ) :
    WeightedL2 (r := r) E g.form h μ φ (u.toForm E g μ hμ h hh φ hφ) := u.2

theorem WeightedOneSection.toForm_sub (u v : WeightedOneSection E g μ hμ h hh φ hφ) :
    (u - v).toForm E g μ hμ h hh φ hφ =
      u.toForm E g μ hμ h hh φ hφ - v.toForm E g μ hμ h hh φ hφ := rfl

theorem weightedOneSection_inner_eq (u v : WeightedOneSection E g μ hμ h hh φ hφ) :
    inner ℂ u v = weightedOneInner E g.form μ h φ
      (u.toForm E g μ hμ h hh φ hφ) (v.toForm E g μ hμ h hh φ hφ) := rfl

theorem weightedOneSection_norm_sq (u : WeightedOneSection E g μ hμ h hh φ hφ) :
    ‖u‖ ^ 2 = (weightedNormSq (r := r) E g.form h μ φ (u.toForm E g μ hμ h hh φ hφ)).toReal := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), weightedOneSection_inner_eq]
  change (weightedOneInner E g.form μ h φ u.1 u.1).re = (weightedNormSq (r := r) E g.form h μ φ u.1).toReal
  have hp := weightedOnePairing_integrable E g μ hμ h hh φ hφ u.1 u.1 u.2 u.2
  have hr : (weightedOneInner E g.form μ h φ u.1 u.1).re =
      ∫ x, BundleDbar.formNormSq (r := r) E g.form h u.1 x * Real.exp (-φ x) ∂μ := by
    calc
      _ = ∫ x, (weightedOnePairing E g.form h φ u.1 u.1 x).re ∂μ := by
        simpa only [weightedOneInner, RCLike.re_eq_complex_re] using (integral_re (𝕜 := ℂ) hp).symm
      _ = _ := integral_congr_ae (Filter.Eventually.of_forall fun x => weightedOnePairing_self_re (r := r) E g.form h φ u.1 x)
  rw [hr, weightedNormSq_one_eq_ofReal_integral E g μ hμ h hh φ hφ u.1 u.2,
    ENNReal.toReal_ofReal (integral_nonneg fun x =>
      mul_nonneg (formNormSq_one_nonneg E g.form h u.1 x) (Real.exp_pos _).le)]

theorem weightedOneSection_norm_eq_zero_iff (u : WeightedOneSection E g μ hμ h hh φ hφ) :
    ‖u‖ = 0 ↔ ∀ᵐ x ∂μ, u.toForm E g μ hμ h hh φ hφ x = (0 : NQForm E 1) x := by
  have hsq := weightedOneSection_norm_sq E g μ hμ h hh φ hφ u
  change ‖u‖ ^ 2 = (weightedNormSq (r := r) E g.form h μ φ u.1).toReal at hsq
  constructor
  · intro hn
    have hreal : (weightedNormSq (r := r) E g.form h μ φ u.1).toReal = 0 := by
      rw [← hsq, hn]
      simp
    have hz : weightedNormSq (r := r) E g.form h μ φ u.1 = 0 := by
      have ht := congrArg ENNReal.ofReal hreal
      rw [ENNReal.ofReal_toReal u.2.2.ne, ENNReal.ofReal_zero] at ht
      exact ht
    exact (weightedNormSq_one_eq_zero_iff E g μ hμ h hh φ hφ u.1 u.2.1).mp hz
  · intro hu
    have hz := (weightedNormSq_one_eq_zero_iff E g μ hμ h hh φ hφ u.1 u.2.1).mpr hu
    have hn : ‖u‖ ^ 2 = 0 := by rw [hsq, hz]; simp
    nlinarith [norm_nonneg u]

theorem weightedOneSection_norm_sub_eq_zero_iff (u v : WeightedOneSection E g μ hμ h hh φ hφ) :
    ‖u - v‖ = 0 ↔ ∀ᵐ x ∂μ, u.toForm E g μ hμ h hh φ hφ x = v.toForm E g μ hμ h hh φ hφ x := by
  rw [weightedOneSection_norm_eq_zero_iff]
  apply Filter.eventually_congr
  exact Filter.Eventually.of_forall fun x => by
    simp only [Subtype.ext_iff, WeightedOneSection.toForm_sub, nqForm_sub_apply, nqForm_zero_apply, sub_eq_zero]

/-- Separated completion of the actual finite weighted top forms.
Representing its arbitrary points by tensor sections remains a separate obligation. -/
abbrev WeightedOneHilbert := UniformSpace.Completion (WeightedOneSection E g μ hμ h hh φ hφ)

def realizeWeightedOneSection (u : WeightedOneSection E g μ hμ h hh φ hφ) :
    WeightedOneHilbert E g μ hμ h hh φ hφ := u

theorem realizeWeightedOneSection_inner (u v : WeightedOneSection E g μ hμ h hh φ hφ) :
    inner ℂ (realizeWeightedOneSection E g μ hμ h hh φ hφ u)
      (realizeWeightedOneSection E g μ hμ h hh φ hφ v) =
        weightedOneInner E g.form μ h φ (u.toForm E g μ hμ h hh φ hφ) (v.toForm E g μ hμ h hh φ hφ) :=
  UniformSpace.Completion.inner_coe u v

theorem realizeWeightedOneSection_norm_sq (u : WeightedOneSection E g μ hμ h hh φ hφ) :
    ‖realizeWeightedOneSection E g μ hμ h hh φ hφ u‖ ^ 2 =
      (weightedNormSq (r := r) E g.form h μ φ (u.toForm E g μ hμ h hh φ hφ)).toReal := by
  rw [realizeWeightedOneSection, UniformSpace.Completion.norm_coe, weightedOneSection_norm_sq]

theorem realizeWeightedOneSection_eq_iff_ae (u v : WeightedOneSection E g μ hμ h hh φ hφ) :
    realizeWeightedOneSection E g μ hμ h hh φ hφ u = realizeWeightedOneSection E g μ hμ h hh φ hφ v ↔
      ∀ᵐ x ∂μ, u.toForm E g μ hμ h hh φ hφ x = v.toForm E g μ hμ h hh φ hφ x := by
  calc
    _ ↔ ‖realizeWeightedOneSection E g μ hμ h hh φ hφ u - realizeWeightedOneSection E g μ hμ h hh φ hφ v‖ = 0 := by
      simp only [norm_eq_zero, sub_eq_zero]
    _ ↔ ‖u - v‖ = 0 := by
      change ‖(u : UniformSpace.Completion (WeightedOneSection E g μ hμ h hh φ hφ)) -
        (v : UniformSpace.Completion (WeightedOneSection E g μ hμ h hh φ hφ))‖ = 0 ↔ _
      rw [← UniformSpace.Completion.coe_sub, UniformSpace.Completion.norm_coe]
    _ ↔ _ := weightedOneSection_norm_sub_eq_zero_iff E g μ hμ h hh φ hφ u v

theorem realizeWeightedOneSection_denseRange : DenseRange (realizeWeightedOneSection E g μ hμ h hh φ hφ) :=
  UniformSpace.Completion.denseRange_coe

theorem weightedOneHilbert_complete : CompleteSpace (WeightedOneHilbert E g μ hμ h hh φ hφ) := inferInstance


/-- The original frozen a.e. quotient embeds densely with its actual integral norm. -/
def realizeWeightedOneClass : WeightedL2Space (r := r) E 1 g.form h μ φ →
    WeightedOneHilbert E g μ hμ h hh φ hφ :=
  Quotient.lift
    (fun u : {u : NQForm E 1 // WeightedL2 (r := r) E g.form h μ φ u} =>
      realizeWeightedOneSection E g μ hμ h hh φ hφ u)
    (fun u v huv => (realizeWeightedOneSection_eq_iff_ae E g μ hμ h hh φ hφ u v).mpr huv)

theorem realizeWeightedOneClass_mk
    (u : {u : NQForm E 1 // WeightedL2 (r := r) E g.form h μ φ u}) :
    realizeWeightedOneClass E g μ hμ h hh φ hφ (Quotient.mk _ u) =
      realizeWeightedOneSection E g μ hμ h hh φ hφ u := rfl

theorem realizeWeightedOneClass_injective : Function.Injective (realizeWeightedOneClass E g μ hμ h hh φ hφ) := by
  intro u v
  refine Quotient.inductionOn₂ u v ?_
  intro u₀ v₀ heq
  apply Quotient.sound
  exact (realizeWeightedOneSection_eq_iff_ae E g μ hμ h hh φ hφ u₀ v₀).mp heq

theorem realizeWeightedOneClass_denseRange : DenseRange (realizeWeightedOneClass E g μ hμ h hh φ hφ) := by
  apply (realizeWeightedOneSection_denseRange E g μ hμ h hh φ hφ).mono
  rintro _ ⟨u, rfl⟩
  exact ⟨Quotient.mk _ u, rfl⟩

def weightedOneClassNormSq (g₀ : HermitianField M) (μ₀ : Measure M.Carrier)
    (h₀ : Metric E) (φ₀ : M.Carrier → ℝ) : WeightedL2Space (r := r) E 1 g₀ h₀ μ₀ φ₀ → ℝ≥0∞ :=
  Quotient.lift
    (fun u : {u : NQForm E 1 // WeightedL2 (r := r) E g₀ h₀ μ₀ φ₀ u} =>
      weightedNormSq (r := r) E g₀ h₀ μ₀ φ₀ u.1)
    (fun u v huv => weightedNormSq_congr_ae (r := r) E g₀ h₀ μ₀ φ₀ u.1 v.1 huv)

theorem weightedOneClassNormSq_lt_top (g₀ : HermitianField M) (μ₀ : Measure M.Carrier)
    (h₀ : Metric E) (φ₀ : M.Carrier → ℝ) (u : WeightedL2Space (r := r) E 1 g₀ h₀ μ₀ φ₀) :
    weightedOneClassNormSq E g₀ μ₀ h₀ φ₀ u < ⊤ := by
  refine Quotient.inductionOn u ?_
  intro u₀
  exact u₀.2.2

theorem realizeWeightedOneClass_norm_sq (u : WeightedL2Space (r := r) E 1 g.form h μ φ) :
    ‖realizeWeightedOneClass E g μ hμ h hh φ hφ u‖ ^ 2 =
      (weightedOneClassNormSq E g.form μ h φ u).toReal := by
  refine Quotient.inductionOn u ?_
  intro u₀
  exact realizeWeightedOneSection_norm_sq E g μ hμ h hh φ hφ u₀

end Yau.LeafProofs.L14Aux

namespace Yau.LeafProofs.L14Aux

open BundleDbar Filter
open scoped Kronecker

theorem matrix_coordinate_le_inverse_diagonal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Matrix (ι) (ι) ℂ) (hH : H.PosDef) (v : ι → ℂ) (α : ι) :
    ‖v α‖ ^ 2 ≤ (H⁻¹ α α).re * (star v ⬝ᵥ H *ᵥ v).re := by
  have hcancel : H⁻¹ *ᵥ (H *ᵥ v) = v := by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (hH.isUnit.map Matrix.detMonoidHom), Matrix.one_mulVec]
  have hx0 : star (Pi.single α (1 : ℂ)) ⬝ᵥ H⁻¹ *ᵥ (H *ᵥ v) = v α := by
    rw [hcancel]
    simp
  have hx1 : star (Pi.single α (1 : ℂ)) ⬝ᵥ H⁻¹ *ᵥ (Pi.single α 1) = H⁻¹ α α := by simp
  have hy1 : star (H *ᵥ v) ⬝ᵥ H⁻¹ *ᵥ (H *ᵥ v) = star v ⬝ᵥ H *ᵥ v := by
    rw [hcancel, Matrix.star_mulVec, hH.isHermitian.eq, ← Matrix.dotProduct_mulVec]
  have hc := hH.inv.star_dotProduct_mulVec_mul_le (Pi.single α 1) (H *ᵥ v)
  rw [hx0, hx1, hy1] at hc
  have hr := (Complex.le_def.mp hc).1
  have hi : (H⁻¹ α α).im = 0 := (Complex.nonneg_iff.mp (hH.inv.posSemidef.diag_nonneg (i := α))).2.symm
  simpa only [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re,
    Complex.normSq_eq_norm_sq, Complex.mul_re, hi, zero_mul, sub_zero] using hr

variable {n r : ℕ} {M : ComplexManifold n}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

def chartOneMetricMatrix (g : HermitianField M) (h : Metric E) (a : M.Carrier) (z : ComplexVector n) :
    Matrix (Fin n × Fin r) (Fin n × Fin r) ℂ :=
  (hMat g a z)⁻¹ ⊗ₖ BundleDbar.metricMatrix (r := r) E h a z

def chartOneCoefficientNormSq (g : HermitianField M) (h : Metric E) (u : NQForm E 1)
    (a : M.Carrier) (z : ComplexVector n) : ℝ :=
  (star (fun p : Fin n × Fin r => coefficients (r := r) E u a z (fun _ => p.1) p.2) ⬝ᵥ
    chartOneMetricMatrix (r := r) E g h a z *ᵥ
      (fun p : Fin n × Fin r => coefficients (r := r) E u a z (fun _ => p.1) p.2)).re

theorem chartOneMetricMatrix_posDef (g : HermitianField M) (h : Metric E)
    (a : M.Carrier) (z : ComplexVector n) (hz : z ∈ localDomain (r := r) E a) :
    (chartOneMetricMatrix (r := r) E g h a z).PosDef :=
  (L18Aux.hMat_posDef g a z hz.1).inv.kronecker (metricMatrix_posDef (r := r) E h a z hz)

theorem chartOneMetricMatrix_contDiffOn (g : Yau.SmoothMetric M) (h : Metric E)
    (hh : BundleDbar.SmoothMetric (r := r) E h) (a : M.Carrier)
    (p q : Fin n × Fin r) :
    ContDiffOn ℝ ∞ (fun z => chartOneMetricMatrix (r := r) E g.form h a z p q) (localDomain (r := r) E a) := by
  rcases p with ⟨i, α⟩
  rcases q with ⟨j, β⟩
  change ContDiffOn ℝ ∞ (fun z => (hMat g.form a z)⁻¹ i j * BundleDbar.metricMatrix (r := r) E h a z α β) _
  exact ((L18Aux.hMat_inverse_contDiffOn g a i j).mono Set.inter_subset_left).mul (hh a α β)

theorem chartOneCoefficientNormSq_nonneg (g : HermitianField M) (h : Metric E) (u : NQForm E 1)
    (a : M.Carrier) (z : ComplexVector n) (hz : z ∈ localDomain (r := r) E a) :
    0 ≤ chartOneCoefficientNormSq (r := r) E g h u a z :=
  (Complex.nonneg_iff.mp ((chartOneMetricMatrix_posDef (r := r) E g h a z hz).posSemidef.dotProduct_mulVec_nonneg _)).1

theorem one_coefficient_le_inverse_diagonal (g : HermitianField M) (h : Metric E) (u : NQForm E 1)
    (a : M.Carrier) (z : ComplexVector n) (hz : z ∈ localDomain (r := r) E a) (i : Fin n) (α : Fin r) :
    ‖coefficients (r := r) E u a z (fun _ => i) α‖ ^ 2 ≤
      ((chartOneMetricMatrix (r := r) E g h a z)⁻¹ (i, α) (i, α)).re * chartOneCoefficientNormSq (r := r) E g h u a z :=
  matrix_coordinate_le_inverse_diagonal _ (chartOneMetricMatrix_posDef (r := r) E g h a z hz)
    (fun p : Fin n × Fin r => coefficients (r := r) E u a z (fun _ => p.1) p.2) (i, α)

theorem formNormSq_one_chart_factor (g : HermitianField M) (h : Metric E) (u : NQForm E 1)
    (a : M.Carrier) (z : ComplexVector n) (hz : z ∈ localDomain (r := r) E a) :
    BundleDbar.formNormSq (r := r) E g h u (chartInv a z) =
      ((hMat g a z).det.re)⁻¹ * chartOneCoefficientNormSq (r := r) E g h u a z := by
  have hp : (∑ i, ∑ j, (hMat g a z)⁻¹ i j *
      ((∑ α, ∑ β, star (coefficients (r := r) E u a z (fun _ => i) α) *
        BundleDbar.metricMatrix (r := r) E h a z α β * coefficients (r := r) E u a z (fun _ => j) β) /
          ((hMat g a z).det.re : ℂ))) =
      (((hMat g a z).det.re : ℂ))⁻¹ *
        (star (fun p : Fin n × Fin r => coefficients (r := r) E u a z (fun _ => p.1) p.2) ⬝ᵥ
          chartOneMetricMatrix (r := r) E g h a z *ᵥ
            (fun p : Fin n × Fin r => coefficients (r := r) E u a z (fun _ => p.1) p.2)) := by
    have hq := metricPairing_eq_kronecker (hMat g a z)⁻¹ (BundleDbar.metricMatrix (r := r) E h a z)
      (fun i α => coefficients (r := r) E u a z (fun _ => i) α)
      (fun i α => coefficients (r := r) E u a z (fun _ => i) α)
    calc
      _ = (((hMat g a z).det.re : ℂ))⁻¹ *
          (∑ i, ∑ j, ∑ α, ∑ β, star (coefficients (r := r) E u a z (fun _ => i) α) *
            BundleDbar.metricMatrix (r := r) E h a z α β * (hMat g a z)⁻¹ i j *
              coefficients (r := r) E u a z (fun _ => j) β) := by
        simp_rw [div_eq_mul_inv, Finset.sum_mul, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        apply Finset.sum_congr rfl
        intro α hα
        apply Finset.sum_congr rfl
        intro β hβ
        ring
      _ = _ := congrArg (fun w : ℂ => (((hMat g a z).det.re : ℂ))⁻¹ * w) hq
  calc
    _ = (∑ i, ∑ j, (hMat g a z)⁻¹ i j *
        ((∑ α, ∑ β, star (coefficients (r := r) E u a z (fun _ => i) α) *
          BundleDbar.metricMatrix (r := r) E h a z α β * coefficients (r := r) E u a z (fun _ => j) β) /
            ((hMat g a z).det.re : ℂ))).re := formNormSq_one_inChart E g h u a z hz
    _ = _ := by
      have he := congrArg Complex.re hp
      rw [← Complex.ofReal_inv] at he
      simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, chartOneCoefficientNormSq] using he

theorem compact_one_coefficient_weight_bound (g : Yau.SmoothMetric M) (h : Metric E)
    (hh : BundleDbar.SmoothMetric (r := r) E h) (φ : M.Carrier → ℝ) (hφ : SmoothFn φ)
    (a : M.Carrier) (K : Set (ComplexVector n)) (hK : IsCompact K)
    (hsub : K ⊆ localDomain (r := r) E a) (i : Fin n) (α : Fin r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : NQForm E 1) z, z ∈ K →
      ‖coefficients (r := r) E u a z (fun _ => i) α‖ ^ 2 ≤
        C * (chartOneCoefficientNormSq (r := r) E g.form h u a z * Real.exp (-φ (chartInv a z))) := by
  have hdet : ∀ z ∈ localDomain (r := r) E a,
      (chartOneMetricMatrix (r := r) E g.form h a z).det ≠ 0 := fun z hz =>
    ((chartOneMetricMatrix_posDef (r := r) E g.form h a z hz).isUnit.map Matrix.detMonoidHom).ne_zero
  have hi : ContinuousOn (fun z => ((chartOneMetricMatrix (r := r) E g.form h a z)⁻¹ (i, α) (i, α)).re)
      (localDomain (r := r) E a) :=
    Complex.continuous_re.comp_continuousOn
      (L18Aux.contDiffOn_matrix_inv (chartOneMetricMatrix_contDiffOn (r := r) E g h hh a) hdet (i, α) (i, α)).continuousOn
  have he : ContinuousOn (fun z => Real.exp (inChart a φ z)) (localDomain (r := r) E a) :=
    Real.continuous_exp.comp_continuousOn ((hφ a).continuousOn.mono Set.inter_subset_left)
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn ((hi.mul he).mono hsub)
  refine ⟨max B 0, le_max_right _ _, ?_⟩
  intro u z hz
  have hzdom := hsub hz
  have hC : ((chartOneMetricMatrix (r := r) E g.form h a z)⁻¹ (i, α) (i, α)).re * Real.exp (inChart a φ z) ≤ max B 0 := by
    apply le_trans (le_abs_self _)
    have hb : ‖((chartOneMetricMatrix (r := r) E g.form h a z)⁻¹ (i, α) (i, α)).re * Real.exp (inChart a φ z)‖ ≤ B := hB z hz
    exact (show |((chartOneMetricMatrix (r := r) E g.form h a z)⁻¹ (i, α) (i, α)).re * Real.exp (inChart a φ z)| ≤ B from
      by simpa only [Real.norm_eq_abs] using hb).trans (le_max_left _ _)
  have hq : 0 ≤ chartOneCoefficientNormSq (r := r) E g.form h u a z := chartOneCoefficientNormSq_nonneg (r := r) E g.form h u a z hzdom
  have hw : Real.exp (inChart a φ z) * Real.exp (-φ (chartInv a z)) = 1 := by
    change Real.exp (φ (chartInv a z)) * Real.exp (-φ (chartInv a z)) = 1
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  calc
    _ ≤ ((chartOneMetricMatrix (r := r) E g.form h a z)⁻¹ (i, α) (i, α)).re * chartOneCoefficientNormSq (r := r) E g.form h u a z :=
      one_coefficient_le_inverse_diagonal (r := r) E g.form h u a z hzdom i α
    _ = (((chartOneMetricMatrix (r := r) E g.form h a z)⁻¹ (i, α) (i, α)).re * Real.exp (inChart a φ z)) *
        (chartOneCoefficientNormSq (r := r) E g.form h u a z * Real.exp (-φ (chartInv a z))) := by
      calc
        _ = (((chartOneMetricMatrix (r := r) E g.form h a z)⁻¹ (i, α) (i, α)).re * chartOneCoefficientNormSq (r := r) E g.form h u a z) *
            (Real.exp (inChart a φ z) * Real.exp (-φ (chartInv a z))) := by rw [hw, mul_one]
        _ = _ := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hC (mul_nonneg hq (Real.exp_pos _).le)
theorem weighted_one_chart_integral (g : Yau.SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (h : Metric E)
    (hh : BundleDbar.SmoothMetric (r := r) E h) (φ : M.Carrier → ℝ) (hφ : SmoothFn φ)
    (u : NQForm E 1) (hu : LocallyL2 (r := r) E u) (a : M.Carrier) :
    (∫⁻ x in bundleChartSource (r := r) E a,
      ENNReal.ofReal (BundleDbar.formNormSq (r := r) E g.form h u x * Real.exp (-φ x)) ∂μ) =
        ENNReal.ofReal ((2 : ℝ) ^ n) *
          ∫⁻ z in localDomain (r := r) E a,
            ENNReal.ofReal (chartOneCoefficientNormSq (r := r) E g.form h u a z *
              Real.exp (-φ (chartInv a z))) ∂lebesgueC n := by
  have hw : Measurable (fun x => Real.exp (-φ x)) :=
    (Real.continuous_exp.comp (L18Aux.continuous_of_smoothFn hφ).neg).measurable
  have hm : AEMeasurable (fun x => ENNReal.ofReal (BundleDbar.formNormSq (r := r) E g.form h u x * Real.exp (-φ x))) μ := ENNReal.measurable_ofReal.comp_aemeasurable
    ((formNormSq_one_aemeasurable E g μ hμ h hh u hu).mul hw.aemeasurable)
  rw [lintegral_bundleChart_volume (r := r) E g μ hμ a _ hm,
    ← lintegral_const_mul' (ENNReal.ofReal ((2 : ℝ) ^ n))
      (fun z => ENNReal.ofReal (chartOneCoefficientNormSq (r := r) E g.form h u a z * Real.exp (-φ (chartInv a z))))
      ENNReal.ofReal_ne_top]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem (localDomain_isOpen E a).measurableSet] with z hz
  rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg _), realMetricFn_sqrt_det g.form a z hz.1,
    formNormSq_one_chart_factor E g.form h u a z hz,
    ← ENNReal.ofReal_mul (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) n)]
  congr 1
  change ((2 : ℝ) ^ n * (hMat g.form a z).det.re) *
      (((hMat g.form a z).det.re)⁻¹ * chartOneCoefficientNormSq (r := r) E g.form h u a z * Real.exp (-φ (chartInv a z))) = _
  field_simp [ne_of_gt (L18Aux.hMat_det_re_pos g.form a hz.1)]

theorem compact_one_coefficient_integral_bound (g : Yau.SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (h : Metric E)
    (hh : BundleDbar.SmoothMetric (r := r) E h) (φ : M.Carrier → ℝ) (hφ : SmoothFn φ)
    (a : M.Carrier) (K : Set (ComplexVector n)) (hK : IsCompact K)
    (hsub : K ⊆ localDomain (r := r) E a) (i : Fin n) (α : Fin r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : NQForm E 1, LocallyL2 (r := r) E u →
      (∫⁻ z in K, ENNReal.ofReal (‖coefficients (r := r) E u a z (fun _ => i) α‖ ^ 2) ∂lebesgueC n) ≤
        ENNReal.ofReal C * weightedNormSq (r := r) E g.form h μ φ u := by
  obtain ⟨C, hC, hbound⟩ := compact_one_coefficient_weight_bound (r := r) E g h hh φ hφ a K hK hsub i α
  refine ⟨C, hC, ?_⟩
  intro u hu
  have hTwo : (1 : ℝ≥0∞) ≤ ENNReal.ofReal ((2 : ℝ) ^ n) := by
    have ht : (1 : ℝ) ≤ (2 : ℝ) ^ n := one_le_pow₀ (by norm_num)
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal ht
  have hnormal : (∫⁻ z in localDomain (r := r) E a,
      ENNReal.ofReal (chartOneCoefficientNormSq (r := r) E g.form h u a z * Real.exp (-φ (chartInv a z))) ∂lebesgueC n) ≤
        weightedNormSq (r := r) E g.form h μ φ u := by
    calc
      _ = 1 * ∫⁻ z in localDomain (r := r) E a,
          ENNReal.ofReal (chartOneCoefficientNormSq (r := r) E g.form h u a z * Real.exp (-φ (chartInv a z))) ∂lebesgueC n := by rw [one_mul]
      _ ≤ ENNReal.ofReal ((2 : ℝ) ^ n) * ∫⁻ z in localDomain (r := r) E a,
          ENNReal.ofReal (chartOneCoefficientNormSq (r := r) E g.form h u a z * Real.exp (-φ (chartInv a z))) ∂lebesgueC n :=
        mul_le_mul_left hTwo _
      _ = _ := (weighted_one_chart_integral E g μ hμ h hh φ hφ u hu a).symm
      _ ≤ _ := setLIntegral_le_lintegral _ _
  calc
    _ ≤ ∫⁻ z in K, ENNReal.ofReal (C * (chartOneCoefficientNormSq (r := r) E g.form h u a z *
        Real.exp (-φ (chartInv a z)))) ∂lebesgueC n := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem hK.measurableSet] with z hz
      exact ENNReal.ofReal_le_ofReal (hbound u z hz)
    _ = ENNReal.ofReal C * ∫⁻ z in K, ENNReal.ofReal (chartOneCoefficientNormSq (r := r) E g.form h u a z *
        Real.exp (-φ (chartInv a z))) ∂lebesgueC n := by
      simp_rw [ENNReal.ofReal_mul hC]
      exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ _ := mul_le_mul_right ((lintegral_mono_set hsub).trans hnormal) _

end Yau.LeafProofs.L14Aux

namespace Yau.LeafProofs.L14Aux

open BundleDbar Filter

variable {n r : ℕ} {M : ComplexManifold n}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]
variable (g : Yau.SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
  (h : Metric E) (hh : BundleDbar.SmoothMetric (r := r) E h) (φ : M.Carrier → ℝ) (hφ : SmoothFn φ)
  (a : M.Carrier) (K : Set (ComplexVector n)) (hK : IsCompact K)
  (hsub : K ⊆ localDomain (r := r) E a) (i : Fin n) (α : Fin r)

def weightedOneLocalCoefficient (u : WeightedOneSection E g μ hμ h hh φ hφ) :
    Lp ℂ 2 ((lebesgueC n).restrict K) :=
  (locallyL2_coefficients_memLp E u.1 u.2.1 a (fun _ => i) α K hK hsub).toLp
    (fun z => coefficients (r := r) E u.1 a z (fun _ => i) α)

theorem weightedOneLocalCoefficient_ae (u : WeightedOneSection E g μ hμ h hh φ hφ) :
    weightedOneLocalCoefficient E g μ hμ h hh φ hφ a K hK hsub i α u =ᵐ[(lebesgueC n).restrict K]
      (fun z => coefficients (r := r) E u.1 a z (fun _ => i) α) := MemLp.coeFn_toLp _

def weightedOneLocalCoefficientLinear :
    WeightedOneSection E g μ hμ h hh φ hφ →ₗ[ℂ] Lp ℂ 2 ((lebesgueC n).restrict K) where
  toFun := weightedOneLocalCoefficient E g μ hμ h hh φ hφ a K hK hsub i α
  map_add' u v := by
    apply Lp.ext
    filter_upwards [weightedOneLocalCoefficient_ae E g μ hμ h hh φ hφ a K hK hsub i α (u+v),
      weightedOneLocalCoefficient_ae E g μ hμ h hh φ hφ a K hK hsub i α u,
      weightedOneLocalCoefficient_ae E g μ hμ h hh φ hφ a K hK hsub i α v,
      Lp.coeFn_add (weightedOneLocalCoefficient E g μ hμ h hh φ hφ a K hK hsub i α u)
        (weightedOneLocalCoefficient E g μ hμ h hh φ hφ a K hK hsub i α v)] with z huv hu hv hadd
    rw [huv, hadd, Pi.add_apply, hu, hv]
    exact coefficients_add E u.1 v.1 a z (fun _ => i) α
  map_smul' c u := by
    change weightedOneLocalCoefficient E g μ hμ h hh φ hφ a K hK hsub i α (c • u) =
      c • weightedOneLocalCoefficient E g μ hμ h hh φ hφ a K hK hsub i α u
    apply Lp.ext
    filter_upwards [weightedOneLocalCoefficient_ae E g μ hμ h hh φ hφ a K hK hsub i α (c • u),
      weightedOneLocalCoefficient_ae E g μ hμ h hh φ hφ a K hK hsub i α u,
      Lp.coeFn_smul c (weightedOneLocalCoefficient E g μ hμ h hh φ hφ a K hK hsub i α u)] with z hcu hu hsmul
    rw [hcu, hsmul, Pi.smul_apply, hu]
    exact coefficients_smul E c u.1 a z (fun _ => i) α

theorem weightedOneLocalCoefficient_norm_sq (u : WeightedOneSection E g μ hμ h hh φ hφ) :
    ‖weightedOneLocalCoefficient E g μ hμ h hh φ hφ a K hK hsub i α u‖ ^ 2 =
      (∫⁻ z in K, ENNReal.ofReal (‖coefficients (r := r) E u.1 a z (fun _ => i) α‖ ^ 2) ∂lebesgueC n).toReal :=
  complex_toLp_norm_sq _ _ _

theorem weightedOneLocalCoefficient_bounded :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : WeightedOneSection E g μ hμ h hh φ hφ,
      ‖weightedOneLocalCoefficient E g μ hμ h hh φ hφ a K hK hsub i α u‖ ≤ C * ‖u‖ := by
  obtain ⟨C, hC, hb⟩ := compact_one_coefficient_integral_bound E g μ hμ h hh φ hφ a K hK hsub i α
  refine ⟨Real.sqrt C, Real.sqrt_nonneg C, ?_⟩
  intro u
  have hfin : ENNReal.ofReal C * weightedNormSq (r := r) E g.form h μ φ u.1 < ⊤ :=
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top u.2.2
  have hs : ‖weightedOneLocalCoefficient E g μ hμ h hh φ hφ a K hK hsub i α u‖ ^ 2 ≤ C * ‖u‖ ^ 2 := by
    rw [weightedOneLocalCoefficient_norm_sq E g μ hμ h hh φ hφ a K hK hsub i α]
    have ht := ENNReal.toReal_mono hfin.ne (hb u.1 u.2.1)
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC] at ht
    have hn := weightedOneSection_norm_sq E g μ hμ h hh φ hφ u
    change ‖u‖ ^ 2 = (weightedNormSq (r := r) E g.form h μ φ u.1).toReal at hn
    rwa [hn]
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg C) (norm_nonneg u))).mp
  calc
    _ ≤ C * ‖u‖ ^ 2 := hs
    _ = (Real.sqrt C * ‖u‖) ^ 2 := by rw [mul_pow, Real.sq_sqrt hC]

def weightedOneLocalCoefficientCLM :
    WeightedOneSection E g μ hμ h hh φ hφ →L[ℂ] Lp ℂ 2 ((lebesgueC n).restrict K) :=
  (weightedOneLocalCoefficientLinear E g μ hμ h hh φ hφ a K hK hsub i α).mkContinuousOfExistsBound
    (by
      obtain ⟨C, _, hC⟩ := weightedOneLocalCoefficient_bounded E g μ hμ h hh φ hφ a K hK hsub i α
      exact ⟨C, hC⟩)

theorem weightedOneLocalCoefficientCLM_apply (u : WeightedOneSection E g μ hμ h hh φ hφ) :
    weightedOneLocalCoefficientCLM E g μ hμ h hh φ hφ a K hK hsub i α u =
      weightedOneLocalCoefficient E g μ hμ h hh φ hφ a K hK hsub i α u := rfl

/-- The local coefficient of a computed weighted Hilbert element is obtained
by extending the actual coefficient map into the complete local L² space. -/
def weightedOneHilbertLocalCoefficient :
    WeightedOneHilbert E g μ hμ h hh φ hφ →L[ℂ] Lp ℂ 2 ((lebesgueC n).restrict K) :=
  (weightedOneLocalCoefficientCLM E g μ hμ h hh φ hφ a K hK hsub i α).fromCompletion

theorem weightedOneHilbertLocalCoefficient_realize (u : WeightedOneSection E g μ hμ h hh φ hφ) :
    weightedOneHilbertLocalCoefficient E g μ hμ h hh φ hφ a K hK hsub i α
      (realizeWeightedOneSection E g μ hμ h hh φ hφ u) =
        weightedOneLocalCoefficient E g μ hμ h hh φ hφ a K hK hsub i α u :=
  ContinuousLinearMap.fromCompletion_apply_coe _ u

theorem weightedOneHilbertLocalCoefficient_realize_ae (u : WeightedOneSection E g μ hμ h hh φ hφ) :
    weightedOneHilbertLocalCoefficient E g μ hμ h hh φ hφ a K hK hsub i α
      (realizeWeightedOneSection E g μ hμ h hh φ hφ u) =ᵐ[(lebesgueC n).restrict K]
        (fun z => coefficients (r := r) E u.1 a z (fun _ => i) α) := by
  rw [weightedOneHilbertLocalCoefficient_realize E g μ hμ h hh φ hφ a K hK hsub i α]
  exact weightedOneLocalCoefficient_ae E g μ hμ h hh φ hφ a K hK hsub i α u


theorem weightedOneHilbertLocalCoefficient_restrict
    (K' : Set (ComplexVector n)) (hK' : IsCompact K')
    (hsub' : K' ⊆ localDomain (r := r) E a) (hKK' : K ⊆ K')
    (u : WeightedOneHilbert E g μ hμ h hh φ hφ) :
    Lp.LpToLpOfMeasureLeSMul (E := ℂ) (p := 2) (c := 1) (by simp)
      (show (lebesgueC n).restrict K ≤ (1 : ℝ≥0∞) • (lebesgueC n).restrict K' from
        by simpa only [one_smul] using Measure.restrict_mono hKK' (le_refl (lebesgueC n)))
      (weightedOneHilbertLocalCoefficient E g μ hμ h hh φ hφ a K' hK' hsub' i α u) =
        weightedOneHilbertLocalCoefficient E g μ hμ h hh φ hφ a K hK hsub i α u := by
  let hmeasure : (lebesgueC n).restrict K ≤ (1 : ℝ≥0∞) • (lebesgueC n).restrict K' :=
    by simpa only [one_smul] using Measure.restrict_mono hKK' (le_refl (lebesgueC n))
  let T := Lp.LpToLpOfMeasureLeSMul (E := ℂ) (p := 2) (c := 1) (by simp) hmeasure
  change T (weightedOneHilbertLocalCoefficient E g μ hμ h hh φ hφ a K' hK' hsub' i α u) =
    weightedOneHilbertLocalCoefficient E g μ hμ h hh φ hφ a K hK hsub i α u
  refine UniformSpace.Completion.induction_on u
    (isClosed_eq (T.continuous.comp (weightedOneHilbertLocalCoefficient E g μ hμ h hh φ hφ a K' hK' hsub' i α).continuous)
      (weightedOneHilbertLocalCoefficient E g μ hμ h hh φ hφ a K hK hsub i α).continuous) ?_
  intro v
  change T (weightedOneHilbertLocalCoefficient E g μ hμ h hh φ hφ a K' hK' hsub' i α
      (realizeWeightedOneSection E g μ hμ h hh φ hφ v)) =
    weightedOneHilbertLocalCoefficient E g μ hμ h hh φ hφ a K hK hsub i α
      (realizeWeightedOneSection E g μ hμ h hh φ hφ v)
  rw [weightedOneHilbertLocalCoefficient_realize E g μ hμ h hh φ hφ a K' hK' hsub' i α,
    weightedOneHilbertLocalCoefficient_realize E g μ hμ h hh φ hφ a K hK hsub i α]
  apply Lp.ext
  have hbig := (weightedOneLocalCoefficient_ae E g μ hμ h hh φ hφ a K' hK' hsub' i α v).filter_mono
    (ae_mono (Measure.restrict_mono hKK' (le_refl (lebesgueC n))))
  filter_upwards [Lp.coeFn_LpToLpOfMeasureLeSMul (E := ℂ) (p := 2) (c := 1) (by simp) hmeasure
      (weightedOneLocalCoefficient E g μ hμ h hh φ hφ a K' hK' hsub' i α v), hbig,
    weightedOneLocalCoefficient_ae E g μ hμ h hh φ hφ a K hK hsub i α v] with z ht hb hs
  exact ht.trans (hb.trans hs.symm)

theorem weightedOneHilbertLocalCoefficient_ae_restrict
    (K' : Set (ComplexVector n)) (hK' : IsCompact K')
    (hsub' : K' ⊆ localDomain (r := r) E a) (hKK' : K ⊆ K')
    (u : WeightedOneHilbert E g μ hμ h hh φ hφ) :
    weightedOneHilbertLocalCoefficient E g μ hμ h hh φ hφ a K' hK' hsub' i α u =ᵐ[(lebesgueC n).restrict K]
      weightedOneHilbertLocalCoefficient E g μ hμ h hh φ hφ a K hK hsub i α u := by
  let hmeasure : (lebesgueC n).restrict K ≤ (1 : ℝ≥0∞) • (lebesgueC n).restrict K' :=
    by simpa only [one_smul] using Measure.restrict_mono hKK' (le_refl (lebesgueC n))
  have hcoe := Lp.coeFn_LpToLpOfMeasureLeSMul (E := ℂ) (p := 2) (c := 1) (by simp) hmeasure
    (weightedOneHilbertLocalCoefficient E g μ hμ h hh φ hφ a K' hK' hsub' i α u)
  rw [weightedOneHilbertLocalCoefficient_restrict E g μ hμ h hh φ hφ a K hK hsub i α K' hK' hsub' hKK' u] at hcoe
  exact hcoe.symm


end Yau.LeafProofs.L14Aux

namespace Yau.LeafProofs.L14Aux

open BundleDbar Filter

def l2IntegralTest {X : Type*} [MeasurableSpace X] (ν : Measure X) (ψ : X → ℂ)
    (hψ : MemLp ψ 2 ν) : Lp ℂ 2 ν →L[ℂ] ℂ :=
  innerSL ℂ (hψ.star.toLp (star ψ))

theorem l2IntegralTest_toLp {X : Type*} [MeasurableSpace X] (ν : Measure X) (ψ : X → ℂ)
    (hψ : MemLp ψ 2 ν) (f : X → ℂ) (hf : MemLp f 2 ν) :
    l2IntegralTest ν ψ hψ (hf.toLp f) = ∫ x, f x * ψ x ∂ν := by
  change inner ℂ (hψ.star.toLp (star ψ)) (hf.toLp f) = _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hψ.star.coeFn_toLp, hf.coeFn_toLp] with x hxψ hxf
  change inner ℂ ((hψ.star.toLp (star ψ)) x) ((hf.toLp f) x) = f x * ψ x
  rw [hxψ, hxf, RCLike.inner_apply]
  change f x * star (star (ψ x)) = f x * ψ x
  rw [star_star]

theorem test_mul_integrable_of_memLp {X : Type*} [MeasurableSpace X] (ν : Measure X)
    (f ψ : X → ℂ) (hf : MemLp f 2 ν) (hψ : MemLp ψ 2 ν) :
    Integrable (fun x => f x * ψ x) ν := by
  have hp : MemLp (fun x => f x * ψ x) 1 ν := hf.mul hψ
  exact memLp_one_iff_integrable.mp hp

theorem integral_mul_eq_setIntegral_of_support_subset {X : Type*} [MeasurableSpace X]
    (ν : Measure X) (f ψ : X → ℂ) (K : Set X) (hψ : Function.support ψ ⊆ K) :
    (∫ x, f x * ψ x ∂ν) = ∫ x in K, f x * ψ x ∂ν := by
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  have hp : ψ x = 0 := by
    by_contra hp
    exact hx (hψ hp)
  rw [hp, mul_zero]

theorem compact_test_memLp {n : ℕ} (ψ : ComplexVector n → ℂ)
    (hψ : Continuous ψ) (hc : HasCompactSupport ψ) (K : Set (ComplexVector n)) :
    MemLp ψ 2 ((lebesgueC n).restrict K) := by
  have hm : MemLp ψ 2 (volume : Measure (ComplexVector n)) := hψ.memLp_of_hasCompactSupport hc
  rw [← lebesgueC_eq_volume n] at hm
  exact hm.mono_measure Measure.restrict_le_self

theorem wirtBar_contDiff {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (ψ : X → ℂ) (hψ : ContDiff ℝ ∞ ψ) (v : X) : ContDiff ℝ ∞ (fun z => wirtBar ψ z v) := by
  simpa only [contDiffOn_univ] using wirtBar_contDiffOn isOpen_univ ψ hψ.contDiffOn v

theorem wirtBar_hasCompactSupport {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (ψ : X → ℂ) (hc : HasCompactSupport ψ) (v : X) : HasCompactSupport (fun z => wirtBar ψ z v) := by
  have hK : IsCompact (tsupport ψ) := hc
  exact hK.of_isClosed_subset isClosed_closure
    (closure_minimal (support_wirtBar_subset ψ v) isClosed_closure)

variable {n r : ℕ} {M : ComplexManifold n}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]
variable (g : Yau.SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
  (h : Metric E) (hh : BundleDbar.SmoothMetric (r := r) E h) (φ : M.Carrier → ℝ) (hφ : SmoothFn φ)
  (a : M.Carrier) (K : Set (ComplexVector n)) (hK : IsCompact K)
  (hsub : K ⊆ localDomain (r := r) E a) (ψ : ComplexVector n → ℂ)
  (hψ : MemLp ψ 2 ((lebesgueC n).restrict K))

def weightedTopChartTest (α : Fin r) : WeightedTopHilbert E g μ hμ h hh φ hφ →L[ℂ] ℂ :=
  (l2IntegralTest ((lebesgueC n).restrict K) ψ hψ).comp
    (weightedTopHilbertLocalCoefficient E g μ hμ h hh φ hφ a K hK hsub α)

def weightedOneChartTest (i : Fin n) (α : Fin r) : WeightedOneHilbert E g μ hμ h hh φ hφ →L[ℂ] ℂ :=
  (l2IntegralTest ((lebesgueC n).restrict K) ψ hψ).comp
    (weightedOneHilbertLocalCoefficient E g μ hμ h hh φ hφ a K hK hsub i α)

theorem weightedTopChartTest_realize_setIntegral (α : Fin r) (u : WeightedTopSection E g μ hμ h hh φ hφ) :
    weightedTopChartTest E g μ hμ h hh φ hφ a K hK hsub ψ hψ α
      (realizeWeightedTopSection E g μ hμ h hh φ hφ u) =
      ∫ z in K, coefficients (r := r) E u.1 a z Fin.elim0 α * ψ z ∂lebesgueC n := by
  unfold weightedTopChartTest
  rw [ContinuousLinearMap.comp_apply, weightedTopHilbertLocalCoefficient_realize]
  exact l2IntegralTest_toLp _ ψ hψ _ (locallyL2_coefficients_memLp E u.1 u.2.1 a Fin.elim0 α K hK hsub)

theorem weightedOneChartTest_realize_setIntegral (i : Fin n) (α : Fin r) (u : WeightedOneSection E g μ hμ h hh φ hφ) :
    weightedOneChartTest E g μ hμ h hh φ hφ a K hK hsub ψ hψ i α
      (realizeWeightedOneSection E g μ hμ h hh φ hφ u) =
      ∫ z in K, coefficients (r := r) E u.1 a z (fun _ => i) α * ψ z ∂lebesgueC n := by
  unfold weightedOneChartTest
  rw [ContinuousLinearMap.comp_apply, weightedOneHilbertLocalCoefficient_realize]
  exact l2IntegralTest_toLp _ ψ hψ _ (locallyL2_coefficients_memLp E u.1 u.2.1 a (fun _ => i) α K hK hsub)

theorem weightedTopChartTest_realize_integral (α : Fin r) (u : WeightedTopSection E g μ hμ h hh φ hφ)
    (hψK : Function.support ψ ⊆ K) :
    weightedTopChartTest E g μ hμ h hh φ hφ a K hK hsub ψ hψ α
      (realizeWeightedTopSection E g μ hμ h hh φ hφ u) =
      ∫ z, coefficients (r := r) E u.1 a z Fin.elim0 α * ψ z ∂lebesgueC n :=
  (weightedTopChartTest_realize_setIntegral E g μ hμ h hh φ hφ a K hK hsub ψ hψ α u).trans
    (integral_mul_eq_setIntegral_of_support_subset (lebesgueC n) _ ψ K hψK).symm

theorem weightedOneChartTest_realize_integral (i : Fin n) (α : Fin r) (u : WeightedOneSection E g μ hμ h hh φ hφ)
    (hψK : Function.support ψ ⊆ K) :
    weightedOneChartTest E g μ hμ h hh φ hφ a K hK hsub ψ hψ i α
      (realizeWeightedOneSection E g μ hμ h hh φ hφ u) =
      ∫ z, coefficients (r := r) E u.1 a z (fun _ => i) α * ψ z ∂lebesgueC n :=
  (weightedOneChartTest_realize_setIntegral E g μ hμ h hh φ hφ a K hK hsub ψ hψ i α u).trans
    (integral_mul_eq_setIntegral_of_support_subset (lebesgueC n) _ ψ K hψK).symm

end Yau.LeafProofs.L14Aux

namespace Yau.LeafProofs.L14Aux

open BundleDbar Filter

variable {n r : ℕ} {M : ComplexManifold n}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

theorem weakDbar_zero_iff_component_tests (u : NQForm E 0) (f : NQForm E 1) :
    WeakDbar (r := r) E u f ↔ LocallyL2 (r := r) E u ∧ LocallyL2 (r := r) E f ∧
      ∀ a (i : Fin n) α (ψ : ComplexVector n → ℂ),
        ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ localDomain (r := r) E a →
        (∫ z, coefficients (r := r) E f a z (fun _ => i) α * ψ z ∂lebesgueC n) =
          -(∫ z, coefficients (r := r) E u a z Fin.elim0 α * wirtBar ψ z (stdVec i) ∂lebesgueC n) := by
  change (LocallyL2 (r := r) E u ∧ LocallyL2 (r := r) E f ∧
    ∀ a (I : Fin 1 → Fin n) α (ψ : ComplexVector n → ℂ),
      ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ localDomain (r := r) E a →
      (∫ z, coefficients (r := r) E f a z I α * ψ z ∂lebesgueC n) =
        -∑ k : Fin 1, (-1 : ℂ) ^ k.val *
          ∫ z, coefficients (r := r) E u a z (fun l : Fin 0 => I (k.succAbove l)) α *
            wirtBar ψ z (stdVec (I k)) ∂lebesgueC n) ↔ _
  constructor
  · rintro ⟨hu, hf, hw⟩
    refine ⟨hu, hf, ?_⟩
    intro a i α ψ hψ hc hs
    have ht := hw a (fun _ => i) α ψ hψ hc hs
    have hJ : (fun _ : Fin 0 => i) = (Fin.elim0 : Fin 0 → Fin n) := Subsingleton.elim _ _
    simpa only [Fin.sum_univ_one, Fin.val_zero, pow_zero, one_mul, hJ] using ht
  · rintro ⟨hu, hf, hw⟩
    refine ⟨hu, hf, ?_⟩
    intro a I α ψ hψ hc hs
    let i := I 0
    have hI : I = (fun _ => i) := funext (fun k => congrArg I (Subsingleton.elim k 0))
    rw [hI]
    have ht := hw a i α ψ hψ hc hs
    have hJ : (fun _ : Fin 0 => i) = (Fin.elim0 : Fin 0 → Fin n) := Subsingleton.elim _ _
    simpa only [Fin.sum_univ_one, Fin.val_zero, pow_zero, one_mul, hJ] using ht

theorem weakDbar_zero_closed_of_weighted_convergence
    (g : Yau.SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (h : Metric E) (hh : BundleDbar.SmoothMetric (r := r) E h) (φ : M.Carrier → ℝ) (hφ : SmoothFn φ)
    (U : ℕ → WeightedTopSection E g μ hμ h hh φ hφ)
    (F : ℕ → WeightedOneSection E g μ hμ h hh φ hφ)
    (u : WeightedTopSection E g μ hμ h hh φ hφ) (f : WeightedOneSection E g μ hμ h hh φ hφ)
    (hU : Tendsto (fun m => realizeWeightedTopSection E g μ hμ h hh φ hφ (U m)) atTop
      (𝓝 (realizeWeightedTopSection E g μ hμ h hh φ hφ u)))
    (hF : Tendsto (fun m => realizeWeightedOneSection E g μ hμ h hh φ hφ (F m)) atTop
      (𝓝 (realizeWeightedOneSection E g μ hμ h hh φ hφ f)))
    (hD : ∀ m, WeakDbar (r := r) E (U m).1 (F m).1) :
    WeakDbar (r := r) E u.1 f.1 := by
  apply (weakDbar_zero_iff_component_tests (r := r) E u.1 f.1).mpr
  refine ⟨u.2.1, f.2.1, ?_⟩
  intro a i α ψ hψ hc hs
  let K := tsupport ψ
  have hK : IsCompact K := hc
  have hψLp := compact_test_memLp ψ hψ.continuous hc K
  let δψ := fun z => wirtBar ψ z (stdVec i)
  have hδc : HasCompactSupport δψ := wirtBar_hasCompactSupport ψ hc (stdVec i)
  have hδcont : Continuous δψ := (wirtBar_contDiff ψ hψ (stdVec i)).continuous
  have hδLp := compact_test_memLp δψ hδcont hδc K
  let LF := weightedOneChartTest E g μ hμ h hh φ hφ a K hK hs ψ hψLp i α
  let LU := weightedTopChartTest E g μ hμ h hh φ hφ a K hK hs δψ hδLp α
  have hEvalF (v : WeightedOneSection E g μ hμ h hh φ hφ) :
      LF (realizeWeightedOneSection E g μ hμ h hh φ hφ v) =
        ∫ z, coefficients (r := r) E v.1 a z (fun _ => i) α * ψ z ∂lebesgueC n :=
    weightedOneChartTest_realize_integral E g μ hμ h hh φ hφ a K hK hs ψ hψLp i α v subset_closure
  have hEvalU (v : WeightedTopSection E g μ hμ h hh φ hφ) :
      LU (realizeWeightedTopSection E g μ hμ h hh φ hφ v) =
        ∫ z, coefficients (r := r) E v.1 a z Fin.elim0 α * wirtBar ψ z (stdVec i) ∂lebesgueC n :=
    weightedTopChartTest_realize_integral E g μ hμ h hh φ hφ a K hK hs δψ hδLp α v
      (support_wirtBar_subset ψ (stdVec i))
  have hTF := (LF.continuous.tendsto (realizeWeightedOneSection E g μ hμ h hh φ hφ f)).comp hF
  have hTU := (LU.continuous.tendsto (realizeWeightedTopSection E g μ hμ h hh φ hφ u)).comp hU
  have hSeq : (fun m => LF (realizeWeightedOneSection E g μ hμ h hh φ hφ (F m))) =
      (fun m => -LU (realizeWeightedTopSection E g μ hμ h hh φ hφ (U m))) := by
    funext m
    have hm := ((weakDbar_zero_iff_component_tests (r := r) E (U m).1 (F m).1).mp (hD m)).2.2 a i α ψ hψ hc hs
    exact (hEvalF (F m)).trans (hm.trans (congrArg (fun z : ℂ => -z) (hEvalU (U m))).symm)
  have hAlt : Tendsto (fun m => LF (realizeWeightedOneSection E g μ hμ h hh φ hφ (F m))) atTop
      (𝓝 (-LU (realizeWeightedTopSection E g μ hμ h hh φ hφ u))) := by
    rw [hSeq]
    exact hTU.neg
  have hEq := tendsto_nhds_unique hTF hAlt
  exact (hEvalF f).symm.trans (hEq.trans (congrArg (fun z : ℂ => -z) (hEvalU u)))

theorem maximalDbarL2Graph_zero_closed_of_weighted_convergence
    (g : Yau.SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (h : Metric E) (hh : BundleDbar.SmoothMetric (r := r) E h) (φ : M.Carrier → ℝ) (hφ : SmoothFn φ)
    (U : ℕ → WeightedTopSection E g μ hμ h hh φ hφ)
    (F : ℕ → WeightedOneSection E g μ hμ h hh φ hφ)
    (u : WeightedTopSection E g μ hμ h hh φ hφ) (f : WeightedOneSection E g μ hμ h hh φ hφ)
    (hU : Tendsto (fun m => realizeWeightedTopSection E g μ hμ h hh φ hφ (U m)) atTop
      (𝓝 (realizeWeightedTopSection E g μ hμ h hh φ hφ u)))
    (hF : Tendsto (fun m => realizeWeightedOneSection E g μ hμ h hh φ hφ (F m)) atTop
      (𝓝 (realizeWeightedOneSection E g μ hμ h hh φ hφ f)))
    (hD : ∀ m, MaximalDbarL2Graph (r := r) (q := 0) E g.form h μ φ
      (Quotient.mk _ (U m)) (Quotient.mk _ (F m))) :
    MaximalDbarL2Graph (r := r) (q := 0) E g.form h μ φ (Quotient.mk _ u) (Quotient.mk _ f) := by
  apply (maximalDbarL2Graph_iff_weakDbar (r := r) (q := 0) E g μ hμ h φ u f).mpr
  apply weakDbar_zero_closed_of_weighted_convergence E g μ hμ h hh φ hφ U F u f hU hF
  intro m
  exact (maximalDbarL2Graph_iff_weakDbar (r := r) (q := 0) E g μ hμ h φ (U m) (F m)).mp (hD m)

end Yau.LeafProofs.L14Aux

namespace Yau.LeafProofs.L14Aux

theorem exists_weightedDbar_distance_cutoffs (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ComplexManifold d) (g : Yau.SmoothMetric N) (o : N.Carrier)
      (R : ℝ), 0 < R →
      ∃ η : N.Carrier → ℝ, SmoothFn η ∧ HasCompactSupport η ∧
        (∀ y, η y ∈ Set.Icc (0 : ℝ) 1) ∧
        (∀ y, inducedDistance g.form o y ≤ R → η y = 1) ∧
        tsupport η ⊆ {y | inducedDistance g.form o y ≤ 2 * R} ∧
        ∀ y, gradNormSq g.form η y ≤ (C / R) ^ 2 / 2 := by
  obtain ⟨C, hC, hη⟩ := L12Aux.exists_quantitative_smooth_distance_cutoffs d
  refine ⟨C, hC, ?_⟩
  intro N g o R hR
  letI := L12Aux.manifold_realSmooth N
  letI : ∀ y : N.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector d) y) :=
    fun y => L12Aux.underlyingRealTangentNormedAddCommGroup g.form y
  letI : ∀ y : N.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector d) y) :=
    fun y => L12Aux.underlyingRealTangentInnerProductSpace g.form y
  obtain ⟨η, hmd, hs, hc, hb, hi, ho, hd⟩ := hη N g o R hR
  refine ⟨η, hs, hc, hb, hi, ho, ?_⟩
  intro y
  have he := L18Aux.scalarGradientPair_le_of_realDifferential_bound g.form hs y
    (div_nonneg hC.le hR.le) (hd y)
  rw [L18Aux.scalarGradientPair_eq_twice_gradNormSq g.form hs y] at he
  linarith


theorem exists_weightedDbar_annular_cutoffs (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ComplexManifold d) (g : Yau.SmoothMetric N) (o : N.Carrier)
      (r R : ℝ), r < R →
      ∃ η : N.Carrier → ℝ, SmoothFn η ∧ HasCompactSupport η ∧
        (∀ y, η y ∈ Set.Icc (0 : ℝ) 1) ∧
        (∀ y, inducedDistance g.form o y ≤ r → η y = 1) ∧
        tsupport η ⊆ {y | inducedDistance g.form o y < R} ∧
        ∀ y, gradNormSq g.form η y ≤ (C / (R - r)) ^ 2 / 2 := by
  obtain ⟨C, hC, hη⟩ := L12Aux.exists_quantitative_smooth_annular_cutoffs d
  refine ⟨C, hC, ?_⟩
  intro N g o r R hrR
  letI := L12Aux.manifold_realSmooth N
  letI : ∀ y : N.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector d) y) :=
    fun y => L12Aux.underlyingRealTangentNormedAddCommGroup g.form y
  letI : ∀ y : N.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector d) y) :=
    fun y => L12Aux.underlyingRealTangentInnerProductSpace g.form y
  obtain ⟨η, hmd, hs, hc, hb, hi, ho, hd⟩ := hη N g o r R hrR
  refine ⟨η, hs, hc, hb, hi, ho, ?_⟩
  intro y
  have he := L18Aux.scalarGradientPair_le_of_realDifferential_bound g.form hs y
    (div_nonneg hC.le (sub_pos.mpr hrR).le) (hd y)
  rw [L18Aux.scalarGradientPair_eq_twice_gradNormSq g.form hs y] at he
  linarith


theorem exists_weightedDbar_cutoff_exhaustion {d : ℕ} (N : ComplexManifold d)
    (g : Yau.SmoothMetric N) (o : N.Carrier) :
    ∃ C : ℝ, 0 < C ∧ ∃ η : ℕ → N.Carrier → ℝ,
      (∀ m, SmoothFn (η m) ∧ HasCompactSupport (η m) ∧
        (∀ y, η m y ∈ Set.Icc (0 : ℝ) 1) ∧
        (∀ y, inducedDistance g.form o y ≤ (m : ℝ) + 1 → η m y = 1) ∧
        tsupport (η m) ⊆ {y | inducedDistance g.form o y ≤ 2 * ((m : ℝ) + 1)} ∧
        ∀ y, gradNormSq g.form (η m) y ≤ (C / ((m : ℝ) + 1)) ^ 2 / 2) ∧
      ∀ x, ∀ᶠ m in Filter.atTop, η m x = 1 := by
  obtain ⟨C, hC, hcut⟩ := exists_weightedDbar_distance_cutoffs d
  have hex (m : ℕ) := hcut N g o ((m : ℝ) + 1) (by positivity)
  choose η hη using hex
  refine ⟨C, hC, η, hη, ?_⟩
  intro x
  obtain ⟨k, hk⟩ := exists_nat_gt (inducedDistance g.form o x)
  filter_upwards [Filter.eventually_ge_atTop k] with m hm
  apply (hη m).2.2.2.1 x
  have hkm : (k : ℝ) ≤ m := by exact_mod_cast hm
  linarith

end Yau.LeafProofs.L14Aux

namespace Yau.LeafProofs.L14Aux
open BundleDbar Filter
variable {n r : ℕ} {M : ComplexManifold n}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

def oneTensorCoordinates (a x : M.Carrier) (hx : x ∈ bundleChartSource (r := r) E a) :
    (antiComplexSubmodule E x 1) →ₗ[ℂ] EuclideanSpace ℂ (Fin n × Fin r) where
  toFun A := WithLp.toLp 2 (fun p =>
    (bundleFrameBasis (r := r) E a x hx.2).repr
      ((A.1 (fun _ => (chartFrameBasis a x hx.1) p.1)) (chartFrameBasis a x hx.1)) p.2)
  map_add' A B := by
    ext p
    change (bundleFrameBasis (r := r) E a x hx.2).repr
      (((A.1 + B.1) (fun _ => (chartFrameBasis a x hx.1) p.1)) (chartFrameBasis a x hx.1)) p.2 =
      (bundleFrameBasis (r := r) E a x hx.2).repr
        ((A.1 (fun _ => (chartFrameBasis a x hx.1) p.1)) (chartFrameBasis a x hx.1)) p.2 +
      (bundleFrameBasis (r := r) E a x hx.2).repr
        ((B.1 (fun _ => (chartFrameBasis a x hx.1) p.1)) (chartFrameBasis a x hx.1)) p.2
    simp only [AlternatingMap.add_apply, map_add, Finsupp.add_apply]
  map_smul' c A := by
    ext p
    change (bundleFrameBasis (r := r) E a x hx.2).repr
      (((c • A.1) (fun _ => (chartFrameBasis a x hx.1) p.1)) (chartFrameBasis a x hx.1)) p.2 =
      c • (bundleFrameBasis (r := r) E a x hx.2).repr
        ((A.1 (fun _ => (chartFrameBasis a x hx.1) p.1)) (chartFrameBasis a x hx.1)) p.2
    simp only [AlternatingMap.smul_apply, map_smul, Finsupp.smul_apply]

theorem oneTensorCoordinates_eq_zero (a x : M.Carrier)
    (hx : x ∈ bundleChartSource (r := r) E a)
    (A : antiComplexSubmodule E x 1) (hA : oneTensorCoordinates E a x hx A = 0) : A = 0 := by
  let b := chartFrameBasis a x hx.1
  let d := bundleFrameBasis (r := r) E a x hx.2
  apply Subtype.ext
  apply antiOne_eq_zero_of_apply_basis_eq_zero b A.1 A.2
  intro i
  apply alternating_eq_zero_of_apply_basis_eq_zero d b
  apply d.ext_elem
  intro α
  have he := congrArg (fun v : EuclideanSpace ℂ (Fin n × Fin r) => v (i, α)) hA
  simpa only [oneTensorCoordinates, LinearMap.coe_mk, AddHom.coe_mk, WithLp.ofLp_toLp, PiLp.zero_apply, map_zero, Finsupp.zero_apply] using he

theorem oneTensorCoordinates_injective (a x : M.Carrier)
    (hx : x ∈ bundleChartSource (r := r) E a) :
    Function.Injective (oneTensorCoordinates E a x hx) := by
  intro A B hAB
  apply sub_eq_zero.mp
  apply oneTensorCoordinates_eq_zero E a x hx
  rw [map_sub, hAB, sub_self]

abbrev oneTensorNormedAddCommGroup (x : M.Carrier) : NormedAddCommGroup (antiComplexSubmodule E x 1) :=
  NormedAddCommGroup.induced _ _
    (oneTensorCoordinates (r := r) E x x ⟨mem_extChartAt_source x, FiberBundle.mem_baseSet_trivializationAt' x⟩)
    (oneTensorCoordinates_injective (r := r) E x x _)

abbrev oneTensorNormedSpace (x : M.Carrier) :
    @NormedSpace ℂ (antiComplexSubmodule E x 1) _ (oneTensorNormedAddCommGroup (r := r) E x).toSeminormedAddCommGroup :=
  NormedSpace.induced ℂ _ _
    (oneTensorCoordinates (r := r) E x x ⟨mem_extChartAt_source x, FiberBundle.mem_baseSet_trivializationAt' x⟩)

theorem oneTensor_finiteDimensional (r : ℕ)
    [TopologicalSpace (TotalSpace (ComplexVector r) E)]
    [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]
    (x : M.Carrier) :
    FiniteDimensional ℂ (antiComplexSubmodule E x 1) :=
  FiniteDimensional.of_injective (oneTensorCoordinates (r := r) E x x
    ⟨mem_extChartAt_source x, FiberBundle.mem_baseSet_trivializationAt' x⟩)
    (oneTensorCoordinates_injective (r := r) E x x _)

theorem oneTensor_complete (x : M.Carrier) :
    letI := oneTensorNormedAddCommGroup (r := r) E x
    CompleteSpace (antiComplexSubmodule E x 1) := by
  letI := oneTensorNormedAddCommGroup (r := r) E x
  letI := oneTensorNormedSpace (r := r) E x
  letI := oneTensor_finiteDimensional E r x
  infer_instance


theorem oneTensorCoordinates_form (u : NQForm E 1) (a : M.Carrier)
    (z : ComplexVector n) (hz : z ∈ localDomain (r := r) E a) (p : Fin n × Fin r) :
    oneTensorCoordinates E a (chartInv a z)
      ⟨(extChartAt (ComplexModel n) a).map_target hz.1, hz.2⟩ (u (chartInv a z)) p =
        coefficients (r := r) E u a z (fun _ => p.1) p.2 := by
  simp only [oneTensorCoordinates, LinearMap.coe_mk, AddHom.coe_mk, WithLp.ofLp_toLp,
    bundleFrameBasis_repr, chartFrameBasis_apply]
  have hb : (chartFrameBasis a (chartInv a z) ((extChartAt (ComplexModel n) a).map_target hz.1)) =
      (fun k => chartVec a (chartInv a z) (stdVec k)) :=
    funext (fun k => chartFrameBasis_apply a (chartInv a z) _ k)
  rw [hb]
  rfl

theorem oneTensorCoordinates_center_form (u : NQForm E 1) (x : M.Carrier)
    (p : Fin n × Fin r) :
    oneTensorCoordinates E x x
      ⟨mem_extChartAt_source x, FiberBundle.mem_baseSet_trivializationAt' x⟩ (u x) p =
        coefficients (r := r) E u x (chartPt x x) (fun _ => p.1) p.2 := by
  rw [coefficients_at_center E u x (fun _ => p.1)]
  simp only [oneTensorCoordinates, LinearMap.coe_mk, AddHom.coe_mk, WithLp.ofLp_toLp,
    bundleFrameBasis_repr, chartFrameBasis_apply]
  have hb : (chartFrameBasis x x (mem_extChartAt_source x)) =
      (fun k => chartVec x x (stdVec k)) :=
    funext (fun k => chartFrameBasis_apply x x _ k)
  rw [hb]


end Yau.LeafProofs.L14Aux

namespace Yau.LeafProofs.L14Aux

open BundleDbar Filter

variable {n r : ℕ} {M : ComplexManifold n}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

def weightedOneAmplitude (g : HermitianField M) (h : Metric E) (φ : M.Carrier → ℝ)
    (u : NQForm E 1) (x : M.Carrier) : ℝ :=
  Real.sqrt (BundleDbar.formNormSq (r := r) E g h u x * Real.exp (-φ x))

theorem weightedOneAmplitude_nonneg (g : HermitianField M) (h : Metric E) (φ : M.Carrier → ℝ)
    (u : NQForm E 1) (x : M.Carrier) : 0 ≤ weightedOneAmplitude (r := r) E g h φ u x :=
  Real.sqrt_nonneg _

theorem weightedOneAmplitude_sq (g : HermitianField M) (h : Metric E) (φ : M.Carrier → ℝ)
    (u : NQForm E 1) (x : M.Carrier) :
    weightedOneAmplitude (r := r) E g h φ u x ^ 2 =
      BundleDbar.formNormSq (r := r) E g h u x * Real.exp (-φ x) :=
  Real.sq_sqrt (mul_nonneg (formNormSq_one_nonneg E g h u x) (Real.exp_pos _).le)

variable (g : Yau.SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
  (h : Metric E) (hh : BundleDbar.SmoothMetric (r := r) E h) (φ : M.Carrier → ℝ) (hφ : SmoothFn φ)

theorem weightedOneAmplitude_memLp
    (g : Yau.SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (h : Metric E) (hh : BundleDbar.SmoothMetric (r := r) E h)
    (φ : M.Carrier → ℝ) (hφ : SmoothFn φ) (u : NQForm E 1) (hu : WeightedL2 (r := r) E g.form h μ φ u) :
    MemLp (weightedOneAmplitude (r := r) E g.form h φ u) 2 μ := by
  have hi := weightedOneNorm_integrable E g μ hμ h hh φ hφ u hu
  have hm : AEStronglyMeasurable (weightedOneAmplitude (r := r) E g.form h φ u) μ :=
    (Real.continuous_sqrt.measurable.comp_aemeasurable hi.aestronglyMeasurable.aemeasurable).aestronglyMeasurable
  apply (memLp_two_iff_integrable_sq_norm hm).mpr
  exact hi.congr (Eventually.of_forall fun x => by
    change BundleDbar.formNormSq (r := r) E g.form h u x * Real.exp (-φ x) =
      ‖weightedOneAmplitude (r := r) E g.form h φ u x‖ ^ 2
    rw [Real.norm_eq_abs, sq_abs, weightedOneAmplitude_sq])

def weightedOneAmplitudeLp (u : WeightedOneSection E g μ hμ h hh φ hφ) : Lp ℝ 2 μ :=
  (weightedOneAmplitude_memLp E g μ hμ h hh φ hφ u.1 u.2).toLp
    (weightedOneAmplitude (r := r) E g.form h φ u.1)

theorem weightedOneAmplitudeLp_ae (u : WeightedOneSection E g μ hμ h hh φ hφ) :
    weightedOneAmplitudeLp E g μ hμ h hh φ hφ u =ᵐ[μ] weightedOneAmplitude (r := r) E g.form h φ u.1 :=
  MemLp.coeFn_toLp _

theorem weightedOneAmplitudeLp_norm (u : WeightedOneSection E g μ hμ h hh φ hφ) :
    ‖weightedOneAmplitudeLp E g μ hμ h hh φ hφ u‖ = ‖u‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [weightedOneAmplitudeLp, real_toLp_norm_sq, weightedOneSection_norm_sq E g μ hμ h hh φ hφ u]
  congr 1
  apply lintegral_congr
  intro x
  rw [Real.norm_eq_abs, sq_abs, weightedOneAmplitude_sq]
  rfl

theorem weightedOneAmplitude_summable_ae
    (v : ℕ → WeightedOneSection E g μ hμ h hh φ hφ) (hv : Summable (fun j => ‖v j‖)) :
    ∀ᵐ x ∂μ, Summable (fun j => weightedOneAmplitude (r := r) E g.form h φ (v j).1 x) := by
  have hsum : (∑' j, eLpNorm (weightedOneAmplitude (r := r) E g.form h φ (v j).1) 2 μ) ≠ ⊤ := by
    have ht := hv.tsum_ofReal_ne_top
    convert ht using 1
    congr 1
    funext j
    rw [← Lp.enorm_toLp (weightedOneAmplitude_memLp E g μ hμ h hh φ hφ (v j).1 (v j).2)]
    change ‖weightedOneAmplitudeLp E g μ hμ h hh φ hφ (v j)‖ₑ = ENNReal.ofReal ‖v j‖
    rw [← ofReal_norm, weightedOneAmplitudeLp_norm E g μ hμ h hh φ hφ]
  have hs := summable_norm_of_tsum_eLpNorm_ne_top (p := 2) (by norm_num : (1 : ℝ≥0∞) ≤ 2) hsum
  filter_upwards [hs] with x hx
  convert hx using 1
  funext j
  exact (Real.norm_of_nonneg (weightedOneAmplitude_nonneg E g.form h φ (v j).1 x)).symm

end Yau.LeafProofs.L14Aux



namespace Yau.LeafProofs.L14Aux
open BundleDbar Filter
variable {n r : ℕ} {M : ComplexManifold n}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

theorem oneTensorCoordinates_amplitude_bound
    (g : HermitianField M) (h : Metric E) (φ : M.Carrier → ℝ) (x : M.Carrier) (p : Fin n × Fin r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : NQForm E 1,
      ‖oneTensorCoordinates E x x
        ⟨mem_extChartAt_source x, FiberBundle.mem_baseSet_trivializationAt' x⟩ (u x) p‖ ≤
          C * weightedOneAmplitude (r := r) E g h φ u x := by
  let z := chartPt x x
  have hz : z ∈ localDomain (r := r) E x := by
    refine ⟨mem_extChartAt_target x, ?_⟩
    change chartInv x (chartPt x x) ∈ (localTriv (r := r) E x).baseSet
    rw [chartInv_chartPt_of_mem x x (mem_chart_source _ _)]
    exact FiberBundle.mem_baseSet_trivializationAt' x
  let K := chartOneMetricMatrix (r := r) E g h x z
  let d := (hMat g x z).det.re
  let c := (K⁻¹ p p).re
  have hK : K.PosDef := chartOneMetricMatrix_posDef (r := r) E g h x z hz
  have hd : 0 < d := (Complex.pos_iff.mp (L18Aux.hMat_posDef g x z hz.1).det_pos).1
  have hc : 0 ≤ c := (Complex.nonneg_iff.mp (hK.inv.posSemidef.diag_nonneg (i := p))).1
  have hC : 0 ≤ c * d * Real.exp (φ x) := mul_nonneg (mul_nonneg hc hd.le) (Real.exp_pos _).le
  refine ⟨Real.sqrt (c * d * Real.exp (φ x)), Real.sqrt_nonneg _, ?_⟩
  intro u
  have he := formNormSq_one_chart_factor E g h u x z hz
  change BundleDbar.formNormSq (r := r) E g h u (chartInv x (chartPt x x)) =
    d⁻¹ * chartOneCoefficientNormSq (r := r) E g h u x z at he
  rw [chartInv_chartPt_of_mem x x (mem_chart_source _ _)] at he
  have hq : chartOneCoefficientNormSq (r := r) E g h u x z =
      d * BundleDbar.formNormSq (r := r) E g h u x := by
    rw [he, ← mul_assoc, mul_inv_cancel₀ hd.ne', one_mul]
  have hsq := one_coefficient_le_inverse_diagonal (r := r) E g h u x z hz p.1 p.2
  rw [hq] at hsq
  rw [oneTensorCoordinates_center_form E u x p]
  apply (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg _) (weightedOneAmplitude_nonneg E g h φ u x))).mp
  calc
    _ ≤ c * (d * BundleDbar.formNormSq (r := r) E g h u x) := hsq
    _ = (Real.sqrt (c * d * Real.exp (φ x)) * weightedOneAmplitude (r := r) E g h φ u x) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hC, weightedOneAmplitude_sq]
      have he : Real.exp (φ x) * Real.exp (-φ x) = 1 := by
        rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
      calc
        _ = (c * (d * BundleDbar.formNormSq (r := r) E g h u x)) *
            (Real.exp (φ x) * Real.exp (-φ x)) := by rw [he, mul_one]
        _ = _ := by ring

end Yau.LeafProofs.L14Aux

namespace Yau.LeafProofs.L14Aux
open BundleDbar Filter
variable {n r : ℕ} {M : ComplexManifold n}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]


theorem euclidean_norm_le_sum_coordinates {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : EuclideanSpace ℂ ι) : ‖v‖ ≤ ∑ i, ‖v i‖ := by
  have hv : (∑ i, PiLp.single 2 i (v i)) = v := by
    ext i
    simp [PiLp.single_apply]
  calc
    ‖v‖ = ‖∑ i, PiLp.single 2 i (v i)‖ := congrArg norm hv.symm
    _ ≤ ∑ i, ‖(PiLp.single 2 i (v i) : EuclideanSpace ℂ ι)‖ :=
      norm_sum_le Finset.univ (fun i => (PiLp.single 2 i (v i) : EuclideanSpace ℂ ι))
    _ = _ := by simp only [PiLp.norm_single]

def oneTensorCoordinatesCLM (a x : M.Carrier) (hx : x ∈ bundleChartSource (r := r) E a) :
    letI := oneTensorNormedAddCommGroup (r := r) E x
    letI := oneTensorNormedSpace (r := r) E x
    (antiComplexSubmodule E x 1) →L[ℂ] EuclideanSpace ℂ (Fin n × Fin r) := by
  letI := oneTensorNormedAddCommGroup (r := r) E x
  letI := oneTensorNormedSpace (r := r) E x
  letI := oneTensor_finiteDimensional E r x
  exact (oneTensorCoordinates (r := r) E a x hx).toContinuousLinearMap

variable (g : Yau.SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
  (h : Metric E) (hh : BundleDbar.SmoothMetric (r := r) E h) (φ : M.Carrier → ℝ) (hφ : SmoothFn φ)

theorem weightedOneSection_series_summable_ae
    (v : ℕ → WeightedOneSection E g μ hμ h hh φ hφ) (hv : Summable (fun j => ‖v j‖)) :
    ∀ᵐ x ∂μ, letI : NormedAddCommGroup {A : MixedTensor E x 1 // AntiComplexLinear E A} :=
    oneTensorNormedAddCommGroup (r := r) E x
      Summable (fun j => ((v j).1 x : antiComplexSubmodule E x 1)) := by
  filter_upwards [weightedOneAmplitude_summable_ae E g μ hμ h hh φ hφ v hv] with x hx
  letI : NormedAddCommGroup {A : MixedTensor E x 1 // AntiComplexLinear E A} :=
    oneTensorNormedAddCommGroup (r := r) E x
  letI := oneTensorNormedSpace (r := r) E x
  letI : CompleteSpace {A : MixedTensor E x 1 // AntiComplexLinear E A} :=
    oneTensor_complete (r := r) E x
  choose C hC hb using fun p : Fin n × Fin r =>
    oneTensorCoordinates_amplitude_bound E g.form h φ x p
  have hsum : Summable (fun j => ∑ p : Fin n × Fin r,
      C p * weightedOneAmplitude (r := r) E g.form h φ (v j).1 x) :=
    summable_sum (fun p _ => hx.mul_left (C p))
  apply hsum.of_norm_bounded
  intro j
  change ‖oneTensorCoordinates (r := r) E x x
    ⟨mem_extChartAt_source x, FiberBundle.mem_baseSet_trivializationAt' x⟩ ((v j).1 x)‖ ≤ _
  exact (euclidean_norm_le_sum_coordinates _).trans
    (Finset.sum_le_sum (fun p _ => hb p (v j).1))

/-- Actual intrinsic `(n,1)` tensor sum in its finite-dimensional coordinate norm. -/
def oneFormTsum (v : ℕ → NQForm E 1) : NQForm E 1 := fun x =>
  letI : NormedAddCommGroup {A : MixedTensor E x 1 // AntiComplexLinear E A} :=
    oneTensorNormedAddCommGroup (r := r) E x
  ∑' j, (v j x : antiComplexSubmodule E x 1)

theorem oneFormTsum_chart_hasSum (v : ℕ → NQForm E 1) (a x : M.Carrier)
    (hx : x ∈ bundleChartSource (r := r) E a)
    (hs : letI : NormedAddCommGroup {A : MixedTensor E x 1 // AntiComplexLinear E A} :=
    oneTensorNormedAddCommGroup (r := r) E x
      Summable (fun j => (v j x : antiComplexSubmodule E x 1))) :
    HasSum (fun j => oneTensorCoordinates (r := r) E a x hx (v j x))
      (oneTensorCoordinates (r := r) E a x hx (oneFormTsum (r := r) E v x)) := by
  letI : NormedAddCommGroup {A : MixedTensor E x 1 // AntiComplexLinear E A} :=
    oneTensorNormedAddCommGroup (r := r) E x
  letI := oneTensorNormedAddCommGroup (r := r) E x
  letI := oneTensorNormedSpace (r := r) E x
  exact (oneTensorCoordinatesCLM E a x hx).hasSum hs.hasSum

theorem oneFormTsum_coefficients_hasSum (v : ℕ → NQForm E 1) (a : M.Carrier)
    (z : ComplexVector n) (hz : z ∈ localDomain (r := r) E a) (i : Fin n) (α : Fin r)
    (hs : letI : NormedAddCommGroup {A : MixedTensor E (chartInv a z) 1 // AntiComplexLinear E A} :=
      oneTensorNormedAddCommGroup (r := r) E (chartInv a z)
      Summable (fun j => (v j (chartInv a z) : antiComplexSubmodule E (chartInv a z) 1))) :
    HasSum (fun j => coefficients (r := r) E (v j) a z (fun _ => i) α)
      (coefficients (r := r) E (oneFormTsum (r := r) E v) a z (fun _ => i) α) := by
  have ht := (PiLp.proj 2 (fun _ : Fin n × Fin r => ℂ) (𝕜 := ℂ) (i, α)).hasSum
    (oneFormTsum_chart_hasSum E v a (chartInv a z)
      ⟨(extChartAt (ComplexModel n) a).map_target hz.1, hz.2⟩ hs)
  convert ht using 1
  · funext j
    exact (oneTensorCoordinates_form E (v j) a z hz (i, α)).symm
  · exact (oneTensorCoordinates_form E (oneFormTsum (r := r) E v) a z hz (i, α)).symm


theorem weightedOneLocalCoefficient_series_enorm
    (v : ℕ → WeightedOneSection E g μ hμ h hh φ hφ) (hv : Summable (fun j => ‖v j‖))
    (a : M.Carrier) (K : Set (ComplexVector n)) (hK : IsCompact K)
    (hsub : K ⊆ localDomain (r := r) E a) (i : Fin n) (α : Fin r) :
    (∑' j, ‖weightedOneLocalCoefficient E g μ hμ h hh φ hφ a K hK hsub i α (v j)‖ₑ) ≠ ⊤ := by
  obtain ⟨C, _, hC⟩ := weightedOneLocalCoefficient_bounded E g μ hμ h hh φ hφ a K hK hsub i α
  have hs : Summable (fun j => ‖weightedOneLocalCoefficient E g μ hμ h hh φ hφ a K hK hsub i α (v j)‖) :=
    Summable.of_nonneg_of_le (fun j => norm_nonneg _) (fun j => hC (v j)) (hv.mul_left C)
  simpa only [ofReal_norm] using hs.tsum_ofReal_ne_top

theorem oneFormTsum_coefficients_ae_localLpTsum
    (v : ℕ → WeightedOneSection E g μ hμ h hh φ hφ) (hv : Summable (fun j => ‖v j‖))
    (a : M.Carrier) (K : Set (ComplexVector n)) (hK : IsCompact K)
    (hsub : K ⊆ localDomain (r := r) E a) (i : Fin n) (α : Fin r) :
    (fun z => coefficients (r := r) E (oneFormTsum (r := r) E (fun j => (v j).1)) a z (fun _ => i) α)
      =ᵐ[(lebesgueC n).restrict K]
        (∑' j, weightedOneLocalCoefficient E g μ hμ h hh φ hφ a K hK hsub i α (v j) : Lp ℂ 2 ((lebesgueC n).restrict K)) := by
  have hpoint := ae_chartInv_of_ae (r := r) E g μ hμ a _
    (weightedOneSection_series_summable_ae E g μ hμ h hh φ hφ v hv)
  have hpointK := hpoint.filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl))
  have hcoefs : ∀ᵐ z ∂(lebesgueC n).restrict K, ∀ j,
      weightedOneLocalCoefficient E g μ hμ h hh φ hφ a K hK hsub i α (v j) z =
        coefficients (r := r) E (v j).1 a z (fun _ => i) α :=
    ae_all_iff.mpr (fun j => weightedOneLocalCoefficient_ae E g μ hμ h hh φ hφ a K hK hsub i α (v j))
  have hsum := Lp.hasSum_coeFn_tsum
    (weightedOneLocalCoefficient_series_enorm E g μ hμ h hh φ hφ v hv a K hK hsub i α)
  filter_upwards [hpointK, hcoefs, hsum, ae_restrict_mem hK.measurableSet] with z hp hc hs hz
  have ht := oneFormTsum_coefficients_hasSum E (fun j => (v j).1) a z (hsub hz) i α hp
  apply ht.unique
  convert hs using 1
  funext j
  exact (hc j).symm

theorem oneFormTsum_coefficients_memLp
    (v : ℕ → WeightedOneSection E g μ hμ h hh φ hφ) (hv : Summable (fun j => ‖v j‖))
    (a : M.Carrier) (K : Set (ComplexVector n)) (hK : IsCompact K)
    (hsub : K ⊆ localDomain (r := r) E a) (i : Fin n) (α : Fin r) :
    MemLp (fun z => coefficients (r := r) E (oneFormTsum (r := r) E (fun j => (v j).1)) a z (fun _ => i) α)
      2 ((lebesgueC n).restrict K) :=
  (memLp_congr_ae (oneFormTsum_coefficients_ae_localLpTsum E g μ hμ h hh φ hφ v hv a K hK hsub i α)).mpr
    (Lp.memLp _)

theorem oneFormTsum_locallyL2
    (v : ℕ → WeightedOneSection E g μ hμ h hh φ hφ) (hv : Summable (fun j => ‖v j‖)) :
    LocallyL2 (r := r) E (oneFormTsum (r := r) E (fun j => (v j).1)) := by
  intro a I α
  let i := I 0
  have hI : I = (fun _ => i) := funext (fun k => congrArg I (Subsingleton.elim k 0))
  rw [hI]
  constructor
  · have hm : AEStronglyMeasurable
        (fun z => coefficients (r := r) E (oneFormTsum (r := r) E (fun j => (v j).1)) a z (fun _ => i) α)
        ((lebesgueC n).restrict (⋃ j, localDomainCompactSet (r := r) E a j)) :=
      AEStronglyMeasurable.iUnion (fun j =>
        (oneFormTsum_coefficients_memLp E g μ hμ h hh φ hφ v hv a (localDomainCompactSet E a j)
          (localDomainCompactSet_isCompact E a j) (localDomainCompactSet_subset E a j) i α).aestronglyMeasurable)
    simpa only [iUnion_localDomainCompactSet E a] using hm
  · intro K hK hsub
    have hf := oneFormTsum_coefficients_memLp E g μ hμ h hh φ hφ v hv a K hK hsub i α
    have hi := (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf
    exact (hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun z => sq_nonneg
      ‖coefficients (r := r) E (oneFormTsum (r := r) E (fun j => (v j).1)) a z (fun _ => i) α‖)).mp hi.2


end Yau.LeafProofs.L14Aux

namespace Yau.LeafProofs.L14Aux
open BundleDbar Filter
variable {n r : ℕ} {M : ComplexManifold n}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]


def oneTensorWeightedQuadratic (g : HermitianField M) (h : Metric E) (φ : M.Carrier → ℝ)
    (x : M.Carrier) (v : EuclideanSpace ℂ (Fin n × Fin r)) : ℝ :=
  ((hMat g x (chartPt x x)).det.re)⁻¹ *
    (star v.ofLp ⬝ᵥ chartOneMetricMatrix (r := r) E g h x (chartPt x x) *ᵥ v.ofLp).re *
      Real.exp (-φ x)

theorem oneTensorWeightedQuadratic_continuous (g : HermitianField M) (h : Metric E)
    (φ : M.Carrier → ℝ) (x : M.Carrier) :
    Continuous (oneTensorWeightedQuadratic (r := r) E g h φ x) := by
  unfold oneTensorWeightedQuadratic dotProduct Matrix.mulVec
  fun_prop

theorem oneTensorWeightedQuadratic_form (g : HermitianField M) (h : Metric E)
    (φ : M.Carrier → ℝ) (u : NQForm E 1) (x : M.Carrier) :
    oneTensorWeightedQuadratic (r := r) E g h φ x
      (oneTensorCoordinates (r := r) E x x
        ⟨mem_extChartAt_source x, FiberBundle.mem_baseSet_trivializationAt' x⟩ (u x)) =
      BundleDbar.formNormSq (r := r) E g h u x * Real.exp (-φ x) := by
  unfold oneTensorWeightedQuadratic
  change ((hMat g x (chartPt x x)).det.re)⁻¹ *
    (star (fun p => oneTensorCoordinates (r := r) E x x
      ⟨mem_extChartAt_source x, FiberBundle.mem_baseSet_trivializationAt' x⟩ (u x) p) ⬝ᵥ
      chartOneMetricMatrix (r := r) E g h x (chartPt x x) *ᵥ
      (fun p => oneTensorCoordinates (r := r) E x x
        ⟨mem_extChartAt_source x, FiberBundle.mem_baseSet_trivializationAt' x⟩ (u x) p)).re *
        Real.exp (-φ x) = _
  simp_rw [oneTensorCoordinates_center_form E u x]
  have hz : chartPt x x ∈ localDomain (r := r) E x := by
    refine ⟨mem_extChartAt_target x, ?_⟩
    change chartInv x (chartPt x x) ∈ (localTriv (r := r) E x).baseSet
    rw [chartInv_chartPt_of_mem x x (mem_chart_source _ _)]
    exact FiberBundle.mem_baseSet_trivializationAt' x
  have he := formNormSq_one_chart_factor E g h u x (chartPt x x) hz
  rw [chartInv_chartPt_of_mem x x (mem_chart_source _ _)] at he
  exact congrArg (fun t : ℝ => t * Real.exp (-φ x)) he.symm

end Yau.LeafProofs.L14Aux

namespace Yau.LeafProofs.L14Aux
open BundleDbar Filter
variable {n r : ℕ} {M : ComplexManifold n}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]



variable (g : Yau.SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
  (h : Metric E) (hh : BundleDbar.SmoothMetric (r := r) E h) (φ : M.Carrier → ℝ) (hφ : SmoothFn φ)

def weightedOneSectionPointCoordinates (x : M.Carrier) :
    WeightedOneSection E g μ hμ h hh φ hφ →ₗ[ℂ] EuclideanSpace ℂ (Fin n × Fin r) where
  toFun u := oneTensorCoordinates (r := r) E x x
    ⟨mem_extChartAt_source x, FiberBundle.mem_baseSet_trivializationAt' x⟩ (u.1 x)
  map_add' u v := (oneTensorCoordinates (r := r) E x x
    ⟨mem_extChartAt_source x, FiberBundle.mem_baseSet_trivializationAt' x⟩).map_add (u.1 x) (v.1 x)
  map_smul' c u := (oneTensorCoordinates (r := r) E x x
    ⟨mem_extChartAt_source x, FiberBundle.mem_baseSet_trivializationAt' x⟩).map_smul c (u.1 x)

theorem weightedOneSectionPointCoordinates_sum {ι : Type*}
    (v : ι → WeightedOneSection E g μ hμ h hh φ hφ) (s : Finset ι) (x : M.Carrier) :
    oneTensorCoordinates (r := r) E x x
      ⟨mem_extChartAt_source x, FiberBundle.mem_baseSet_trivializationAt' x⟩ ((∑ j ∈ s, v j).1 x) =
      ∑ j ∈ s, oneTensorCoordinates (r := r) E x x
        ⟨mem_extChartAt_source x, FiberBundle.mem_baseSet_trivializationAt' x⟩ ((v j).1 x) :=
  map_sum (weightedOneSectionPointCoordinates E g μ hμ h hh φ hφ x) v s

theorem oneFormTsum_weightedQuadratic_tendsto_ae
    (v : ℕ → WeightedOneSection E g μ hμ h hh φ hφ) (hv : Summable (fun j => ‖v j‖)) :
    ∀ᵐ x ∂μ, Tendsto (fun N => ENNReal.ofReal
        (BundleDbar.formNormSq (r := r) E g.form h ((∑ j ∈ Finset.range N, v j).1) x * Real.exp (-φ x)))
      atTop (𝓝 (ENNReal.ofReal (BundleDbar.formNormSq (r := r) E g.form h
        (oneFormTsum (r := r) E (fun j => (v j).1)) x * Real.exp (-φ x)))) := by
  filter_upwards [weightedOneSection_series_summable_ae E g μ hμ h hh φ hφ v hv] with x hx
  have hs : Tendsto (fun N => oneTensorCoordinates (r := r) E x x
        ⟨mem_extChartAt_source x, FiberBundle.mem_baseSet_trivializationAt' x⟩
        ((∑ j ∈ Finset.range N, v j).1 x)) atTop
      (𝓝 (oneTensorCoordinates (r := r) E x x
        ⟨mem_extChartAt_source x, FiberBundle.mem_baseSet_trivializationAt' x⟩
        (oneFormTsum (r := r) E (fun j => (v j).1) x))) := by
    simpa only [weightedOneSectionPointCoordinates_sum E g μ hμ h hh φ hφ] using
      (oneFormTsum_chart_hasSum E (fun j => (v j).1) x x
        ⟨mem_extChartAt_source x, FiberBundle.mem_baseSet_trivializationAt' x⟩ hx).tendsto_sum_nat
  have ht := (ENNReal.continuous_ofReal.comp
    (oneTensorWeightedQuadratic_continuous (r := r) E g.form h φ x)).continuousAt.tendsto.comp hs
  simpa only [Function.comp_def, oneTensorWeightedQuadratic_form (r := r) E g.form h φ] using ht

theorem weightedOneSection_normSq_eq_ofReal (u : WeightedOneSection E g μ hμ h hh φ hφ) :
    weightedNormSq (r := r) E g.form h μ φ u.1 = ENNReal.ofReal (‖u‖ ^ 2) := by
  have hn := weightedOneSection_norm_sq E g μ hμ h hh φ hφ u
  change ‖u‖ ^ 2 = (weightedNormSq (r := r) E g.form h μ φ u.1).toReal at hn
  rw [hn, ENNReal.ofReal_toReal u.2.2.ne]

theorem weightedOneSection_partialNormSq_le
    (v : ℕ → WeightedOneSection E g μ hμ h hh φ hφ) (hv : Summable (fun j => ‖v j‖)) (N : ℕ) :
    weightedNormSq (r := r) E g.form h μ φ (∑ j ∈ Finset.range N, v j).1 ≤
      ENNReal.ofReal ((∑' j, ‖v j‖) ^ 2) := by
  rw [weightedOneSection_normSq_eq_ofReal E g μ hμ h hh φ hφ]
  have hn := (norm_sum_le (Finset.range N) v).trans
    (hv.sum_le_tsum (Finset.range N) (fun j _ => norm_nonneg _))
  have hS : 0 ≤ ∑' j, ‖v j‖ := tsum_nonneg (fun j => norm_nonneg _)
  apply ENNReal.ofReal_le_ofReal
  nlinarith [norm_nonneg (∑ j ∈ Finset.range N, v j)]

theorem oneFormTsum_weightedNormSq_le
    (v : ℕ → WeightedOneSection E g μ hμ h hh φ hφ) (hv : Summable (fun j => ‖v j‖)) :
    weightedNormSq (r := r) E g.form h μ φ (oneFormTsum (r := r) E (fun j => (v j).1)) ≤
      ENNReal.ofReal ((∑' j, ‖v j‖) ^ 2) := by
  let F := fun N x => ENNReal.ofReal (BundleDbar.formNormSq (r := r) E g.form h
    (∑ j ∈ Finset.range N, v j).1 x * Real.exp (-φ x))
  have hw : Measurable (fun x => Real.exp (-φ x)) :=
    (Real.continuous_exp.comp (L18Aux.continuous_of_smoothFn hφ).neg).measurable
  have hm : ∀ N, AEMeasurable (F N) μ := fun N =>
    ENNReal.measurable_ofReal.comp_aemeasurable
      ((formNormSq_one_aemeasurable E g μ hμ h hh (∑ j ∈ Finset.range N, v j).1
        (∑ j ∈ Finset.range N, v j).2.1).mul hw.aemeasurable)
  calc
    _ = ∫⁻ x, liminf (fun N => F N x) atTop ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [oneFormTsum_weightedQuadratic_tendsto_ae E g μ hμ h hh φ hφ v hv] with x hx
      exact hx.liminf_eq.symm
    _ ≤ liminf (fun N => ∫⁻ x, F N x ∂μ) atTop := lintegral_liminf_le' hm
    _ ≤ _ := liminf_le_of_frequently_le' (Eventually.of_forall
      (fun N => weightedOneSection_partialNormSq_le E g μ hμ h hh φ hφ v hv N)).frequently

theorem oneFormTsum_weightedL2
    (v : ℕ → WeightedOneSection E g μ hμ h hh φ hφ) (hv : Summable (fun j => ‖v j‖)) :
    WeightedL2 (r := r) E g.form h μ φ (oneFormTsum (r := r) E (fun j => (v j).1)) :=
  ⟨oneFormTsum_locallyL2 E g μ hμ h hh φ hφ v hv,
    lt_of_le_of_lt (oneFormTsum_weightedNormSq_le E g μ hμ h hh φ hφ v hv) ENNReal.ofReal_lt_top⟩

end Yau.LeafProofs.L14Aux

namespace Yau.LeafProofs.L14Aux

open BundleDbar Filter

variable {n r : ℕ} {M : ComplexManifold n}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]
variable (g : Yau.SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
  (h : Metric E) (hh : BundleDbar.SmoothMetric (r := r) E h) (φ : M.Carrier → ℝ) (hφ : SmoothFn φ)

def weightedOneSectionTsum (v : ℕ → WeightedOneSection E g μ hμ h hh φ hφ)
    (hv : Summable (fun j => ‖v j‖)) : WeightedOneSection E g μ hμ h hh φ hφ :=
  ⟨oneFormTsum (r := r) E (fun j => (v j).1), oneFormTsum_weightedL2 E g μ hμ h hh φ hφ v hv⟩

theorem weightedOneSectionTsum_norm_le (v : ℕ → WeightedOneSection E g μ hμ h hh φ hφ)
    (hv : Summable (fun j => ‖v j‖)) :
    ‖weightedOneSectionTsum E g μ hμ h hh φ hφ v hv‖ ≤ ∑' j, ‖v j‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (tsum_nonneg (fun j => norm_nonneg _))).mp
  have hn := weightedOneSection_norm_sq E g μ hμ h hh φ hφ (weightedOneSectionTsum E g μ hμ h hh φ hφ v hv)
  change ‖weightedOneSectionTsum E g μ hμ h hh φ hφ v hv‖ ^ 2 =
    (weightedNormSq (r := r) E g.form h μ φ (oneFormTsum (r := r) E (fun j => (v j).1))).toReal at hn
  rw [hn]
  simpa only [ENNReal.toReal_ofReal (sq_nonneg _)] using ENNReal.toReal_mono ENNReal.ofReal_ne_top
    (oneFormTsum_weightedNormSq_le E g μ hμ h hh φ hφ v hv)

def weightedOneSectionPointValue (x : M.Carrier) :
    WeightedOneSection E g μ hμ h hh φ hφ →ₗ[ℂ] antiComplexSubmodule E x 1 where
  toFun u := u.1 x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem oneFormTsum_sub_partial_ae
    (v : ℕ → WeightedOneSection E g μ hμ h hh φ hφ) (hv : Summable (fun j => ‖v j‖)) (N : ℕ) :
    ∀ᵐ x ∂μ,
      (oneFormTsum (r := r) E (fun j => (v j).1) - (∑ j ∈ Finset.range N, v j).1) x =
        oneFormTsum (r := r) E (fun j => (v (j+N)).1) x := by
  filter_upwards [weightedOneSection_series_summable_ae E g μ hμ h hh φ hφ v hv] with x hx
  letI : NormedAddCommGroup {A : MixedTensor E x 1 // AntiComplexLinear E A} :=
    oneTensorNormedAddCommGroup (r := r) E x
  have heval : ((∑ j ∈ Finset.range N, v j).1 x : antiComplexSubmodule E x 1) =
      ∑ j ∈ Finset.range N, ((v j).1 x : antiComplexSubmodule E x 1) :=
    map_sum (weightedOneSectionPointValue E g μ hμ h hh φ hφ x) v (Finset.range N)
  change ((∑' j, ((v j).1 x : antiComplexSubmodule E x 1)) -
    (∑ j ∈ Finset.range N, v j).1 x) = ∑' j, ((v (j+N)).1 x : antiComplexSubmodule E x 1)
  rw [heval]
  have ht := hx.sum_add_tsum_nat_add N
  exact sub_eq_iff_eq_add.mpr (ht.symm.trans (add_comm _ _))

theorem weightedOneSectionTsum_norm_sub_partial_le
    (v : ℕ → WeightedOneSection E g μ hμ h hh φ hφ) (hv : Summable (fun j => ‖v j‖)) (N : ℕ) :
    ‖weightedOneSectionTsum E g μ hμ h hh φ hφ v hv - ∑ j ∈ Finset.range N, v j‖ ≤
      ∑' j, ‖v (j+N)‖ := by
  have htail : Summable (fun j => ‖v (j+N)‖) := hv.comp_injective (by intro i j hij; exact Nat.add_right_cancel hij)
  let t := weightedOneSectionTsum E g μ hμ h hh φ hφ (fun j => v (j+N)) htail
  have heq : ‖weightedOneSectionTsum E g μ hμ h hh φ hφ v hv - ∑ j ∈ Finset.range N, v j‖ ^ 2 = ‖t‖ ^ 2 := by
    rw [weightedOneSection_norm_sq E g μ hμ h hh φ hφ, weightedOneSection_norm_sq E g μ hμ h hh φ hφ]
    apply congrArg ENNReal.toReal
    apply weightedNormSq_congr_ae E g.form h μ φ
    exact oneFormTsum_sub_partial_ae E g μ hμ h hh φ hφ v hv N
  have hn := (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp heq
  rw [hn]
  exact weightedOneSectionTsum_norm_le E g μ hμ h hh φ hφ (fun j => v (j+N)) htail

theorem weightedOneSectionTsum_tendsto_partial
    (v : ℕ → WeightedOneSection E g μ hμ h hh φ hφ) (hv : Summable (fun j => ‖v j‖)) :
    Tendsto (fun N => ∑ j ∈ Finset.range N, v j) atTop
      (𝓝 (weightedOneSectionTsum E g μ hμ h hh φ hφ v hv)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun N => norm_nonneg _)
    (fun N => ?_) (tendsto_sum_nat_add (fun j => ‖v j‖))
  rw [norm_sub_rev]
  exact weightedOneSectionTsum_norm_sub_partial_le E g μ hμ h hh φ hφ v hv N

theorem weightedOneSection_complete : CompleteSpace (WeightedOneSection E g μ hμ h hh φ hφ) := by
  apply Metric.complete_of_cauchySeq_tendsto
  intro u hu
  obtain ⟨f, hf₁, hf₂⟩ := Metric.exists_subseq_summable_dist_of_cauchySeq u hu
  simp only [dist_eq_norm] at hf₂
  let v n := u (f (n+1)) - u (f n)
  have hv_sum : (fun n => ∑ i ∈ Finset.range n, v i) = fun n => u (f n) - u (f 0) := by
    funext n
    exact Finset.sum_range_sub (u ∘ f) n
  have ha := weightedOneSectionTsum_tendsto_partial E g μ hμ h hh φ hφ v hf₂
  refine ⟨weightedOneSectionTsum E g μ hμ h hh φ hφ v hf₂ + u (f 0), ?_⟩
  refine tendsto_nhds_of_cauchySeq_of_subseq hu hf₁.tendsto_atTop ?_
  rw [hv_sum] at ha
  have h₁ := Tendsto.add_const (u (f 0)) ha
  simpa only [sub_add_cancel] using! h₁

theorem realizeWeightedOneSection_surjective :
    Function.Surjective (realizeWeightedOneSection E g μ hμ h hh φ hφ) := by
  letI : CompleteSpace (WeightedOneSection E g μ hμ h hh φ hφ) :=
    weightedOneSection_complete E g μ hμ h hh φ hφ
  have hc : IsClosed (Set.range (realizeWeightedOneSection E g μ hμ h hh φ hφ)) :=
    (UniformSpace.Completion.isUniformInducing_coe (WeightedOneSection E g μ hμ h hh φ hφ)).isComplete_range.isClosed
  exact Set.range_eq_univ.mp (hc.closure_eq.symm.trans
    (realizeWeightedOneSection_denseRange E g μ hμ h hh φ hφ).closure_range)

theorem realizeWeightedOneClass_surjective :
    Function.Surjective (realizeWeightedOneClass E g μ hμ h hh φ hφ) := by
  intro u
  obtain ⟨v, hv⟩ := realizeWeightedOneSection_surjective E g μ hμ h hh φ hφ u
  exact ⟨Quotient.mk _ v, hv⟩

theorem realizeWeightedOneClass_bijective :
    Function.Bijective (realizeWeightedOneClass E g μ hμ h hh φ hφ) :=
  ⟨realizeWeightedOneClass_injective E g μ hμ h hh φ hφ,
    realizeWeightedOneClass_surjective E g μ hμ h hh φ hφ⟩

def weightedOneHilbertRepresentative (u : WeightedOneHilbert E g μ hμ h hh φ hφ) :
    WeightedOneSection E g μ hμ h hh φ hφ :=
  (realizeWeightedOneSection_surjective E g μ hμ h hh φ hφ u).choose

theorem weightedOneHilbertRepresentative_realize (u : WeightedOneHilbert E g μ hμ h hh φ hφ) :
    realizeWeightedOneSection E g μ hμ h hh φ hφ (weightedOneHilbertRepresentative E g μ hμ h hh φ hφ u) = u :=
  (realizeWeightedOneSection_surjective E g μ hμ h hh φ hφ u).choose_spec

theorem weightedOneHilbertRepresentative_normSq (u : WeightedOneHilbert E g μ hμ h hh φ hφ) :
    weightedNormSq (r := r) E g.form h μ φ (weightedOneHilbertRepresentative E g μ hμ h hh φ hφ u).1 =
      ENNReal.ofReal (‖u‖ ^ 2) := by
  rw [weightedOneSection_normSq_eq_ofReal E g μ hμ h hh φ hφ]
  have hnorm : ‖realizeWeightedOneSection E g μ hμ h hh φ hφ
      (weightedOneHilbertRepresentative E g μ hμ h hh φ hφ u)‖ =
      ‖weightedOneHilbertRepresentative E g μ hμ h hh φ hφ u‖ := UniformSpace.Completion.norm_coe _
  rw [weightedOneHilbertRepresentative_realize E g μ hμ h hh φ hφ u] at hnorm
  rw [hnorm]

end Yau.LeafProofs.L14Aux

namespace Yau.LeafProofs.L14Aux

open BundleDbar Filter

variable {n r : ℕ} {M : ComplexManifold n}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]
variable (g : Yau.SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
  (h : Metric E) (hh : BundleDbar.SmoothMetric (r := r) E h) (φ : M.Carrier → ℝ) (hφ : SmoothFn φ)

/-- Each coordinate distributional equation is a continuous linear equation
on the actual weighted Hilbert spaces. -/
def weightedDbarHilbertTest (a : M.Carrier) (i : Fin n) (α : Fin r)
    (ψ : ComplexVector n → ℂ) (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ ⊆ localDomain (r := r) E a) :
    (WeightedTopHilbert E g μ hμ h hh φ hφ × WeightedOneHilbert E g μ hμ h hh φ hφ) →L[ℂ] ℂ :=
  (weightedOneChartTest E g μ hμ h hh φ hφ a (tsupport ψ) hc hs ψ
      (compact_test_memLp ψ hψ.continuous hc (tsupport ψ)) i α).comp
      (ContinuousLinearMap.snd ℂ _ _) +
    (weightedTopChartTest E g μ hμ h hh φ hφ a (tsupport ψ) hc hs
      (fun z => wirtBar ψ z (stdVec i))
      (compact_test_memLp _ (wirtBar_contDiff ψ hψ (stdVec i)).continuous
        (wirtBar_hasCompactSupport ψ hc (stdVec i)) (tsupport ψ)) α).comp
      (ContinuousLinearMap.fst ℂ _ _)

theorem weightedDbarHilbertTest_realize (a : M.Carrier) (i : Fin n) (α : Fin r)
    (ψ : ComplexVector n → ℂ) (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ ⊆ localDomain (r := r) E a)
    (u : WeightedTopSection E g μ hμ h hh φ hφ) (f : WeightedOneSection E g μ hμ h hh φ hφ) :
    weightedDbarHilbertTest E g μ hμ h hh φ hφ a i α ψ hψ hc hs
      (realizeWeightedTopSection E g μ hμ h hh φ hφ u,
        realizeWeightedOneSection E g μ hμ h hh φ hφ f) =
      (∫ z, coefficients (r := r) E f.1 a z (fun _ => i) α * ψ z ∂lebesgueC n) +
        ∫ z, coefficients (r := r) E u.1 a z Fin.elim0 α * wirtBar ψ z (stdVec i) ∂lebesgueC n := by
  unfold weightedDbarHilbertTest
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd']
  exact congrArg₂ (· + ·)
    (weightedOneChartTest_realize_integral E g μ hμ h hh φ hφ a (tsupport ψ) hc hs ψ
      (compact_test_memLp ψ hψ.continuous hc (tsupport ψ)) i α f subset_closure)
    (weightedTopChartTest_realize_integral E g μ hμ h hh φ hφ a (tsupport ψ) hc hs
      (fun z => wirtBar ψ z (stdVec i))
      (compact_test_memLp _ (wirtBar_contDiff ψ hψ (stdVec i)).continuous
        (wirtBar_hasCompactSupport ψ hc (stdVec i)) (tsupport ψ)) α u
      (support_wirtBar_subset ψ (stdVec i)))

/-- The maximal `(n,0)` Dolbeault graph, expressed as the common kernel of
its genuine distributional chart tests. No operator or graph is supplied. -/
def weightedMaximalDbarHilbertGraph :
    Submodule ℂ (WeightedTopHilbert E g μ hμ h hh φ hφ × WeightedOneHilbert E g μ hμ h hh φ hφ) where
  carrier := {p | ∀ a i α ψ hψ hc hs,
    weightedDbarHilbertTest E g μ hμ h hh φ hφ a i α ψ hψ hc hs p = 0}
  zero_mem' := by
    intro a i α ψ hψ hc hs
    exact (weightedDbarHilbertTest E g μ hμ h hh φ hφ a i α ψ hψ hc hs).map_zero
  add_mem' := by
    intro p q hp hq a i α ψ hψ hc hs
    rw [map_add, hp a i α ψ hψ hc hs, hq a i α ψ hψ hc hs, add_zero]
  smul_mem' := by
    intro c p hp a i α ψ hψ hc hs
    rw [map_smul, hp a i α ψ hψ hc hs, smul_zero]

theorem weightedMaximalDbarHilbertGraph_realize_iff
    (u : WeightedTopSection E g μ hμ h hh φ hφ) (f : WeightedOneSection E g μ hμ h hh φ hφ) :
    (realizeWeightedTopSection E g μ hμ h hh φ hφ u,
      realizeWeightedOneSection E g μ hμ h hh φ hφ f) ∈
        weightedMaximalDbarHilbertGraph E g μ hμ h hh φ hφ ↔
      WeakDbar (r := r) E u.1 f.1 := by
  rw [weakDbar_zero_iff_component_tests E]
  change (∀ a i α ψ hψ hc hs, _ = 0) ↔ _
  simp_rw [weightedDbarHilbertTest_realize E g μ hμ h hh φ hφ, add_eq_zero_iff_eq_neg]
  exact ⟨fun hw => ⟨u.2.1, f.2.1, hw⟩, fun hw => hw.2.2⟩

theorem weightedMaximalDbarHilbertGraph_isClosed :
    IsClosed (weightedMaximalDbarHilbertGraph E g μ hμ h hh φ hφ :
      Set (WeightedTopHilbert E g μ hμ h hh φ hφ × WeightedOneHilbert E g μ hμ h hh φ hφ)) := by
  change IsClosed {p | ∀ a i α ψ hψ hc hs,
    weightedDbarHilbertTest E g μ hμ h hh φ hφ a i α ψ hψ hc hs p = 0}
  simp only [Set.ofPred_forall]
  exact isClosed_iInter fun a => isClosed_iInter fun i => isClosed_iInter fun α =>
    isClosed_iInter fun ψ => isClosed_iInter fun hψ => isClosed_iInter fun hc =>
      isClosed_iInter fun hs => (weightedDbarHilbertTest E g μ hμ h hh φ hφ a i α ψ hψ hc hs).isClosed_ker

theorem weightedMaximalDbarHilbertGraph_iff_quotient
    (u : WeightedL2Space (r := r) E 0 g.form h μ φ)
    (f : WeightedL2Space (r := r) E 1 g.form h μ φ) :
    (realizeWeightedTopClass E g μ hμ h hh φ hφ u,
      realizeWeightedOneClass E g μ hμ h hh φ hφ f) ∈
        weightedMaximalDbarHilbertGraph E g μ hμ h hh φ hφ ↔
      MaximalDbarL2Graph (r := r) (q := 0) E g.form h μ φ u f := by
  refine Quotient.inductionOn₂ u f ?_
  intro u₀ f₀
  exact (weightedMaximalDbarHilbertGraph_realize_iff E g μ hμ h hh φ hφ u₀ f₀).trans
    (maximalDbarL2Graph_iff_weakDbar E g μ hμ h φ u₀ f₀).symm

theorem weightedMaximalDbarHilbertGraph_iff_representative
    (u : WeightedTopHilbert E g μ hμ h hh φ hφ) (f : WeightedOneHilbert E g μ hμ h hh φ hφ) :
    (u, f) ∈ weightedMaximalDbarHilbertGraph E g μ hμ h hh φ hφ ↔
      WeakDbar (r := r) E
        (weightedTopHilbertRepresentative E g μ hμ h hh φ hφ u).1
        (weightedOneHilbertRepresentative E g μ hμ h hh φ hφ f).1 := by
  have ht := weightedMaximalDbarHilbertGraph_realize_iff E g μ hμ h hh φ hφ
    (weightedTopHilbertRepresentative E g μ hμ h hh φ hφ u)
    (weightedOneHilbertRepresentative E g μ hμ h hh φ hφ f)
  simpa only [weightedTopHilbertRepresentative_realize, weightedOneHilbertRepresentative_realize] using ht

end Yau.LeafProofs.L14Aux

namespace Yau.LeafProofs.L14Aux

open BundleDbar Filter

variable {n r : ℕ} {M : ComplexManifold n}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

theorem locallyL2_coefficients_locallyIntegrableOn {q : ℕ}
    (u : NQForm E q) (hu : LocallyL2 (r := r) E u)
    (a : M.Carrier) (I : Fin q → Fin n) (α : Fin r) :
    LocallyIntegrableOn (fun z => coefficients (r := r) E u a z I α)
      (localDomain (r := r) E a) (lebesgueC n) := by
  apply (locallyIntegrableOn_iff (localDomain_isOpen E a).isLocallyClosed).mpr
  intro K hsub hK
  letI : IsFiniteMeasure ((lebesgueC n).restrict K) := isFiniteMeasure_restrict.mpr (by
    rw [lebesgueC_eq_volume]
    exact hK.measure_lt_top.ne)
  exact (locallyL2_coefficients_memLp E u hu a I α K hK hsub).integrable (by norm_num)

/-- The scalar distribution tests distinguish the actual local L² coefficients. -/
theorem locallyL2_coefficient_ae_zero_of_tests {q : ℕ}
    (u : NQForm E q) (hu : LocallyL2 (r := r) E u)
    (a : M.Carrier) (I : Fin q → Fin n) (α : Fin r)
    (ht : ∀ ψ : ComplexVector n → ℂ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ localDomain (r := r) E a →
        (∫ z, coefficients (r := r) E u a z I α * ψ z ∂lebesgueC n) = 0) :
    (fun z => coefficients (r := r) E u a z I α) =ᵐ[
      (lebesgueC n).restrict (localDomain (r := r) E a)] 0 := by
  apply (ae_restrict_iff' (localDomain_isOpen E a).measurableSet).mpr
  apply (localDomain_isOpen E a).ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (locallyL2_coefficients_locallyIntegrableOn E u hu a I α)
  intro ψ hψ hc hs
  have he := ht (Complex.ofReal ∘ ψ) (Complex.ofRealCLM.contDiff.comp hψ)
    (hc.comp_left Complex.ofReal_zero) ((tsupport_comp_subset Complex.ofReal_zero ψ).trans hs)
  simpa only [Function.comp_apply, Complex.real_smul, mul_comm] using he

theorem ae_of_bundleCharts (g : HermitianField M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g μ) (P : M.Carrier → Prop)
    (hP : ∀ a, ∀ᵐ z ∂(lebesgueC n).restrict (localDomain (r := r) E a), P (chartInv a z)) :
    ∀ᵐ x ∂μ, P x := by
  have hlocal (a : M.Carrier) : ∀ᵐ x ∂μ.restrict (bundleChartSource (r := r) E a), P x := by
    have ht := (chartPtExtension_quasiMeasurePreserving (r := r) E g μ hμ a).ae (hP a)
    filter_upwards [ht, ae_restrict_mem (bundleChartSource_isOpen (r := r) E a).measurableSet] with x hx hxdom
    change P (chartInv a (chartPtExtension a x)) at hx
    rw [chartPtExtension, if_pos hxdom.1,
      chartInv_chartPt_of_mem a x (by simpa only [extChartAt_source] using hxdom.1)] at hx
    exact hx
  obtain ⟨v, hv⟩ := isLindelof_univ.indexed_countable_subcover (bundleChartSource (r := r) E)
    (bundleChartSource_isOpen (r := r) E) (by
      intro y _
      exact Set.mem_iUnion.mpr ⟨y, mem_extChartAt_source y, FiberBundle.mem_baseSet_trivializationAt' y⟩)
  have hcover : (⋃ j, bundleChartSource (r := r) E (v j)) = Set.univ := Set.eq_univ_of_univ_subset hv
  have hp := (ae_restrict_iUnion_iff (fun j => bundleChartSource (r := r) E (v j)) P).mpr
    (fun j => hlocal (v j))
  simpa only [hcover, Measure.restrict_univ] using hp

theorem oneForm_ae_zero_of_coefficients_ae_zero (g : HermitianField M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g μ) (f : NQForm E 1)
    (hf : ∀ a i α, (fun z => coefficients (r := r) E f a z (fun _ => i) α) =ᵐ[
      (lebesgueC n).restrict (localDomain (r := r) E a)] 0) :
    ∀ᵐ x ∂μ, f x = (0 : NQForm E 1) x := by
  apply ae_of_bundleCharts (r := r) E g μ hμ _
  intro a
  have hall : ∀ᵐ z ∂(lebesgueC n).restrict (localDomain (r := r) E a),
      ∀ i α, coefficients (r := r) E f a z (fun _ => i) α = 0 :=
    ae_all_iff.mpr (fun i => ae_all_iff.mpr (fun α => hf a i α))
  filter_upwards [hall, ae_restrict_mem (localDomain_isOpen E a).measurableSet] with z hz hzdom
  apply oneTensorCoordinates_eq_zero E a (chartInv a z)
    ⟨(extChartAt (ComplexModel n) a).map_target hzdom.1, hzdom.2⟩
  ext p
  rw [oneTensorCoordinates_form E f a z hzdom p, hz p.1 p.2]
  rfl

/-- Zero has only the zero distributional Dolbeault derivative, on the
genuine tensor sections and with respect to the prescribed volume law. -/
theorem weakDbar_zero_source_ae_zero (g : HermitianField M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g μ) (f : NQForm E 1)
    (hf : WeakDbar (r := r) E (0 : NQForm E 0) f) :
    ∀ᵐ x ∂μ, f x = (0 : NQForm E 1) x := by
  apply oneForm_ae_zero_of_coefficients_ae_zero (r := r) E g μ hμ f
  intro a i α
  apply locallyL2_coefficient_ae_zero_of_tests E f hf.2.1 a (fun _ => i) α
  intro ψ hψ hc hs
  have he := (weakDbar_zero_iff_component_tests E (0 : NQForm E 0) f).mp hf |>.2.2 a i α ψ hψ hc hs
  simpa only [coefficients_zero, zero_mul, integral_zero, neg_zero] using he

variable (g : Yau.SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
  (h : Metric E) (hh : BundleDbar.SmoothMetric (r := r) E h) (φ : M.Carrier → ℝ) (hφ : SmoothFn φ)

theorem weightedMaximalDbarHilbertGraph_fst_zero
    (p : WeightedTopHilbert E g μ hμ h hh φ hφ × WeightedOneHilbert E g μ hμ h hh φ hφ)
    (hp : p ∈ weightedMaximalDbarHilbertGraph E g μ hμ h hh φ hφ) (hz : p.1 = 0) : p.2 = 0 := by
  let f := weightedOneHilbertRepresentative E g μ hμ h hh φ hφ p.2
  have hmem : (realizeWeightedTopSection E g μ hμ h hh φ hφ 0,
      realizeWeightedOneSection E g μ hμ h hh φ hφ f) ∈
        weightedMaximalDbarHilbertGraph E g μ hμ h hh φ hφ := by
    simpa only [f, weightedOneHilbertRepresentative_realize, realizeWeightedTopSection,
      UniformSpace.Completion.coe_zero, ← hz, Prod.mk.eta] using hp
  have hd := (weightedMaximalDbarHilbertGraph_realize_iff E g μ hμ h hh φ hφ 0 f).mp hmem
  have hae := weakDbar_zero_source_ae_zero E g.form μ hμ f.1 hd
  have hn := (weightedOneSection_norm_eq_zero_iff E g μ hμ h hh φ hφ f).mpr hae
  have hr := weightedOneHilbertRepresentative_realize E g μ hμ h hh φ hφ p.2
  have he : ‖p.2‖ = 0 := by
    rw [← hr]
    change ‖(f : UniformSpace.Completion (WeightedOneSection E g μ hμ h hh φ hφ))‖ = 0
    rw [UniformSpace.Completion.norm_coe, hn]
  exact norm_eq_zero.mp he

/-- The actual maximal Dolbeault operator, recovered from the now proved
single-valued distributional graph. -/
def weightedMaximalDbar :
    WeightedTopHilbert E g μ hμ h hh φ hφ →ₗ.[ℂ] WeightedOneHilbert E g μ hμ h hh φ hφ :=
  (weightedMaximalDbarHilbertGraph E g μ hμ h hh φ hφ).toLinearPMap

theorem weightedMaximalDbar_graph :
    (weightedMaximalDbar E g μ hμ h hh φ hφ).graph =
      weightedMaximalDbarHilbertGraph E g μ hμ h hh φ hφ :=
  Submodule.toLinearPMap_graph_eq _ (weightedMaximalDbarHilbertGraph_fst_zero E g μ hμ h hh φ hφ)

theorem weightedMaximalDbar_isClosed : (weightedMaximalDbar E g μ hμ h hh φ hφ).IsClosed := by
  change IsClosed ((weightedMaximalDbar E g μ hμ h hh φ hφ).graph :
    Set (WeightedTopHilbert E g μ hμ h hh φ hφ × WeightedOneHilbert E g μ hμ h hh φ hφ))
  rw [weightedMaximalDbar_graph]
  exact weightedMaximalDbarHilbertGraph_isClosed E g μ hμ h hh φ hφ

end Yau.LeafProofs.L14Aux

namespace Yau.LeafProofs.L14Aux

open BundleDbar Filter

variable {n r : ℕ} {M : ComplexManifold n}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

/-- Reconstruction of the actual conjugate-linear outer tensor from its
local `(n,1)` coefficient vectors. -/
def oneTensorFromCoefficients (a x : M.Carrier)
    (hx : x ∈ bundleChartSource (r := r) E a) (F : Fin n → ComplexVector r) :
    antiComplexSubmodule E x 1 := by
  let b := chartFrameBasis a x hx.1
  let P := fun i => b.det.smulRight ((localTriv (r := r) E a).symmL ℂ x (F i))
  letI : IsScalarTower ℝ ℂ ((TangentVector M x) [⋀^Fin n]→ₗ[ℂ] E x) := ⟨by
    intro c d A
    ext v
    exact smul_assoc c d (A v)⟩
  let L : TangentVector M x →ₗ[ℝ] ((TangentVector M x) [⋀^Fin n]→ₗ[ℂ] E x) :=
    ((Fintype.linearCombination ℂ P).restrictScalars ℝ).comp
      (LinearMap.pi (fun i => Complex.conjAe.toLinearMap.comp ((b.coord i).restrictScalars ℝ)))
  refine ⟨AlternatingMap.ofSubsingleton ℝ _ _ (0 : Fin 1) L, ?_⟩
  intro v i c
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  change L ((Function.update v 0 (c • v 0)) 0) = star c • L (v 0)
  rw [Function.update_self]
  change (∑ j, star ((b.coord j) (c • v 0)) • P j) =
    star c • ∑ j, star ((b.coord j) (v 0)) • P j
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_smul, smul_eq_mul, star_mul, mul_smul]
  exact smul_comm _ _ _

theorem oneTensorFromCoefficients_basis (a x : M.Carrier)
    (hx : x ∈ bundleChartSource (r := r) E a) (F : Fin n → ComplexVector r) (i : Fin n) :
    ((oneTensorFromCoefficients (r := r) E a x hx F).1
      (fun _ => chartFrameBasis a x hx.1 i)) (chartFrameBasis a x hx.1) =
        (localTriv (r := r) E a).symmL ℂ x (F i) := by
  classical
  change (∑ j, star ((chartFrameBasis a x hx.1).coord j (chartFrameBasis a x hx.1 i)) •
    (chartFrameBasis a x hx.1).det.smulRight ((localTriv (r := r) E a).symmL ℂ x (F j)))
      (chartFrameBasis a x hx.1) = _
  simp [Basis.det_self, Finsupp.single_apply]

theorem oneTensorCoordinates_fromCoefficients (a x : M.Carrier)
    (hx : x ∈ bundleChartSource (r := r) E a) (F : Fin n → ComplexVector r)
    (i : Fin n) (α : Fin r) :
    oneTensorCoordinates (r := r) E a x hx
      (oneTensorFromCoefficients (r := r) E a x hx F) (i, α) = F i α := by
  change (bundleFrameBasis (r := r) E a x hx.2).repr
    (((oneTensorFromCoefficients (r := r) E a x hx F).1
      (fun _ => chartFrameBasis a x hx.1 i)) (chartFrameBasis a x hx.1)) α = _
  rw [oneTensorFromCoefficients_basis, bundleFrameBasis_repr]
  rw [Trivialization.continuousLinearMapAt_symmL _ hx.2]

end Yau.LeafProofs.L14Aux

namespace Yau.LeafProofs.L14Aux

open BundleDbar Filter

variable {n r : ℕ} {M : ComplexManifold n}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

/-- A model top-form coefficient, reconstructed in the actual tangent and
bundle fibres and extended by the actual zero tensor. -/
def topFormPushforward (a : M.Carrier) (F : ComplexVector n → ComplexVector r) : NQForm E 0 := by
  classical
  exact (show (∀ x, antiComplexSubmodule E x 0) from fun x =>
    if hx : x ∈ bundleChartSource (r := r) E a then
      (topTensorCoordinatesEquiv (r := r) E a x hx).symm (F (chartPt a x)) else 0)

theorem topFormPushforward_coefficients (a : M.Carrier) (F : ComplexVector n → ComplexVector r)
    (z : ComplexVector n) (hz : z ∈ localDomain (r := r) E a) :
    coefficients (r := r) E (topFormPushforward (r := r) E a F) a z Fin.elim0 = F z := by
  classical
  have hx : chartInv a z ∈ bundleChartSource (r := r) E a :=
    ⟨(extChartAt (ComplexModel n) a).map_target hz.1, hz.2⟩
  rw [← topTensorCoordinatesEquiv_form E (topFormPushforward (r := r) E a F) a z hz]
  change topTensorCoordinatesEquiv E a (chartInv a z) hx
    (if hy : chartInv a z ∈ bundleChartSource (r := r) E a then
      (topTensorCoordinatesEquiv E a (chartInv a z) hy).symm (F (chartPt a (chartInv a z)))
      else (0 : antiComplexSubmodule E (chartInv a z) 0)) = _
  rw [dif_pos hx, LinearEquiv.apply_symm_apply]
  exact congrArg F ((extChartAt (ComplexModel n) a).right_inv hz.1)

theorem topFormPushforward_support (a : M.Carrier) (F : ComplexVector n → ComplexVector r)
    (hc : HasCompactSupport F) (hs : tsupport F ⊆ localDomain (r := r) E a) :
    closure {x | topFormPushforward (r := r) E a F x ≠ (0 : NQForm E 0) x} ⊆ chartInv a '' tsupport F := by
  classical
  have hK : IsCompact (chartInv a '' tsupport F) := hc.image_of_continuousOn
    ((continuousOn_extChartAt_symm (I := ComplexModel n) a).mono (hs.trans Set.inter_subset_left))
  apply closure_minimal _ hK.isClosed
  intro x hx
  change topFormPushforward (r := r) E a F x ≠ (0 : antiComplexSubmodule E x 0) at hx
  by_cases hxa : x ∈ bundleChartSource (r := r) E a
  · have hn : F (chartPt a x) ≠ 0 := by
      intro hf
      exact hx (by
        simp only [topFormPushforward, dif_pos hxa, hf, map_zero]
        rfl)
    exact ⟨chartPt a x, subset_closure hn,
      chartInv_chartPt_of_mem a x (by simpa only [extChartAt_source] using hxa.1)⟩
  · exact False.elim (hx (by
      simp only [topFormPushforward, dif_neg hxa]
      rfl))

theorem topFormPushforward_support_in_source (a : M.Carrier) (F : ComplexVector n → ComplexVector r)
    (hc : HasCompactSupport F) (hs : tsupport F ⊆ localDomain (r := r) E a) :
    closure {x | topFormPushforward (r := r) E a F x ≠ (0 : NQForm E 0) x} ⊆ bundleChartSource (r := r) E a := by
  apply (topFormPushforward_support E a F hc hs).trans
  rintro x ⟨z, hz, rfl⟩
  exact ⟨(extChartAt (ComplexModel n) a).map_target (hs hz).1, (hs hz).2⟩

end Yau.LeafProofs.L14Aux

namespace Yau.LeafProofs.L14Aux

open BundleDbar Filter

variable {n r : ℕ} {M : ComplexManifold n}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

theorem chartFrameBasis_coord (a x : M.Carrier)
    (hx : x ∈ (extChartAt (ComplexModel n) a).source) (v : TangentVector M x) (i : Fin n) :
    (chartFrameBasis a x hx).coord i v = tangentCoords a x v i := by
  classical
  let b := chartFrameBasis a x hx
  let L : TangentVector M x →ₗ[ℂ] ℂ := (EuclideanSpace.projₗ i).comp
    (mfderiv (ComplexModel n) (ComplexModel n) (extChartAt (ComplexModel n) a) x).toLinearMap
  have hL : b.coord i = L := by
    apply b.ext
    intro j
    have hr : L (b j) = if i = j then 1 else 0 := by
      change tangentCoords a x (chartFrameBasis a x hx j) i = _
      rw [chartFrameBasis_apply, L12Aux.tangentCoords_chartVec a x hx]
      simp [stdVec, PiLp.single_apply, eq_comm]
    have hl : b.coord i (b j) = if i = j then 1 else 0 := by
      simp [Basis.coord_apply, Finsupp.single_apply, eq_comm]
    exact hl.trans hr.symm
  exact LinearMap.congr_fun hL v

set_option backward.isDefEq.respectTransparency false in
theorem chartFrameBasis_toMatrix_fderiv (a b : M.Carrier) (z : ComplexVector n)
    (hz : z ∈ chartTarget b) (hya : chartInv b z ∈ (extChartAt (ComplexModel n) a).source) :
    (chartFrameBasis a (chartInv b z) hya).toMatrix
      (chartFrameBasis b (chartInv b z) ((extChartAt (ComplexModel n) b).map_target hz)) =
      fun i j => fderiv ℂ (fun w => chartPt a (chartInv b w)) z (stdVec j) i := by
  ext i j
  change (chartFrameBasis a (chartInv b z) hya).coord i
    (chartFrameBasis b (chartInv b z) ((extChartAt (ComplexModel n) b).map_target hz) j) = _
  rw [chartFrameBasis_coord, chartFrameBasis_apply]
  exact (congrArg (fun v : ComplexVector n => v i)
    (L18Aux.chartTransition_fderiv b a hz hya (stdVec j))).symm

theorem bundleCoordChange_apply (a b x : M.Carrier)
    (ha : x ∈ (localTriv (r := r) E a).baseSet) (hb : x ∈ (localTriv (r := r) E b).baseSet)
    (v : ComplexVector r) :
    (localTriv (r := r) E a).coordChangeL ℂ (localTriv (r := r) E b) x v =
      (localTriv (r := r) E b).continuousLinearMapAt ℂ x
        ((localTriv (r := r) E a).symmL ℂ x v) := by
  rw [Trivialization.coordChangeL_apply _ _ ⟨ha, hb⟩,
    Trivialization.continuousLinearMapAt_apply_of_mem ℂ _ hb, Trivialization.symmL_apply _ ha]

/-- The actual coefficient transition of `K_M ⊗ E`: its determinant
factor is retained alongside the genuine bundle transition. -/
def topBundleTransition (a b : M.Carrier) (z : ComplexVector n) : ComplexVector r →L[ℂ] ComplexVector r :=
  Matrix.det (fun i j : Fin n => fderiv ℂ (fun w => chartPt a (chartInv b w)) z (stdVec j) i) •
    ((localTriv (r := r) E a).coordChangeL ℂ (localTriv (r := r) E b) (chartInv b z) :
      ComplexVector r →L[ℂ] ComplexVector r)

set_option backward.isDefEq.respectTransparency false in
theorem topFormPushforward_coefficients_inChart (a b : M.Carrier)
    (F : ComplexVector n → ComplexVector r) (z : ComplexVector n)
    (hz : z ∈ localDomain (r := r) E b)
    (hya : chartInv b z ∈ bundleChartSource (r := r) E a) :
    coefficients (r := r) E (topFormPushforward (r := r) E a F) b z Fin.elim0 =
      topBundleTransition (r := r) E a b z (F (chartPt a (chartInv b z))) := by
  classical
  let y := chartInv b z
  have hyb : y ∈ bundleChartSource (r := r) E b :=
    ⟨(extChartAt (ComplexModel n) b).map_target hz.1, hz.2⟩
  rw [← topTensorCoordinatesEquiv_form E (topFormPushforward (r := r) E a F) b z hz]
  have hu : (topFormPushforward (r := r) E a F y : antiComplexSubmodule E y 0) =
      (topTensorCoordinatesEquiv E a y hya).symm (F (chartPt a y)) := by
    change (if hx : y ∈ bundleChartSource (r := r) E a then
      (topTensorCoordinatesEquiv E a y hx).symm (F (chartPt a y)) else 0) = _
    exact dif_pos hya
  change topTensorCoordinatesEquiv E b y hyb (topFormPushforward (r := r) E a F y) = _
  rw [hu, topTensorCoordinatesEquiv_transition E a b y hya hyb,
    chartFrameBasis_toMatrix_fderiv a b z hz.1 hya.1]
  rw [← bundleCoordChange_apply E a b y hya.2 hyb.2]
  rfl

end Yau.LeafProofs.L14Aux

namespace Yau.LeafProofs.L14Aux

open BundleDbar Filter

variable {n r : ℕ} {M : ComplexManifold n}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

set_option backward.isDefEq.respectTransparency false in
theorem topBundleTransition_contDiffAt (hE : Holomorphic (r := r) E)
    (a b : M.Carrier) (z : ComplexVector n) (hz : z ∈ localDomain (r := r) E b)
    (hya : chartInv b z ∈ bundleChartSource (r := r) E a) :
    ContDiffAt ℂ ∞ (topBundleTransition (r := r) E a b) z := by
  letI : ContMDiffVectorBundle ⊤ (ComplexVector r) E (ComplexModel n) := hE
  let T := fun w => chartPt a (chartInv b w)
  have hT : ContDiffAt ℂ ∞ T z := L18Aux.chartTransition_contDiffAt b a hz.1 hya.1
  have hD : ContDiffAt ℂ ∞ (fderiv ℂ T) z := hT.fderiv_right (m := ∞) (by simp)
  have hJ (i j : Fin n) : ContDiffAt ℂ ∞ (fun t => fderiv ℂ T t (stdVec j) i) z := by
    have hv : ContDiffAt ℂ ∞ (fun t => fderiv ℂ T t (stdVec j)) z := hD.clm_apply contDiffAt_const
    exact (contDiffAt_piLp 2).mp hv i
  have hdet : ContDiffAt ℂ ∞ (fun t => Matrix.det (fun i j : Fin n => fderiv ℂ T t (stdVec j) i)) z := by
    simp_rw [Matrix.det_apply']
    exact ContDiffAt.sum fun σ _ => contDiffAt_const.mul (contDiffAt_prod fun i _ => hJ (σ i) i)
  have hi : ContMDiffAt 𝓘(ℂ, ComplexVector n) (ComplexModel n) ∞ (chartInv b) z :=
    (contMDiffOn_extChartAt_symm (I := ComplexModel n) b).contMDiffAt
      ((isOpen_extChartAt_target (I := ComplexModel n) b).mem_nhds hz.1)
  have hC : ContMDiffAt (ComplexModel n) 𝓘(ℂ, ComplexVector r →L[ℂ] ComplexVector r) ∞
      (fun x => ((localTriv (r := r) E a).coordChangeL ℂ (localTriv (r := r) E b) x :
        ComplexVector r →L[ℂ] ComplexVector r)) (chartInv b z) :=
    contMDiffAt_coordChangeL hya.2 hz.2
  exact hdet.smul (hC.comp z hi).contDiffAt

/-- Compact model tests give smooth genuine top forms in every atlas chart,
including at the boundary of their actual zero extension. -/
theorem topFormPushforward_smooth (hE : Holomorphic (r := r) E)
    (a : M.Carrier) (F : ComplexVector n → ComplexVector r)
    (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    (hs : tsupport F ⊆ localDomain (r := r) E a) :
    SmoothForm (r := r) E (topFormPushforward (r := r) E a F) := by
  classical
  intro b I α z hz
  have hI : I = (Fin.elim0 : Fin 0 → Fin n) := Subsingleton.elim _ _
  subst I
  have hi : ContinuousAt (chartInv b) z := continuousAt_extChartAt_symm'' (I := ComplexModel n) hz.1
  by_cases hya : chartInv b z ∈ bundleChartSource (r := r) E a
  · have hT := (L18Aux.chartTransition_contDiffAt b a hz.1 hya.1).restrict_scalars ℝ
    have hC := (topBundleTransition_contDiffAt E hE a b z hz hya).restrict_scalars ℝ
    have hCR : ContDiffAt ℝ ∞ (fun t => (topBundleTransition (r := r) E a b t).restrictScalars ℝ) z :=
      (ContinuousLinearMap.restrictScalarsL ℂ (ComplexVector r) (ComplexVector r) ℝ ℝ).contDiff.contDiffAt.comp z hC
    have hCF := hCR.clm_apply (hF.contDiffAt.comp z hT)
    have hm : ContDiffAt ℝ ∞
        (fun t => topBundleTransition (r := r) E a b t (F (chartPt a (chartInv b t))) α) z :=
      (contDiffAt_piLp 2).mp hCF α
    have heq : (fun t => coefficients (r := r) E (topFormPushforward (r := r) E a F) b t Fin.elim0 α) =ᶠ[𝓝 z]
        (fun t => topBundleTransition (r := r) E a b t (F (chartPt a (chartInv b t))) α) := by
      filter_upwards [(localDomain_isOpen E b).mem_nhds hz,
        hi.tendsto.eventually ((bundleChartSource_isOpen (r := r) E a).mem_nhds hya)] with t htb hta
      exact congrArg (fun v : ComplexVector r => v α)
        (topFormPushforward_coefficients_inChart E a b F t htb hta)
    exact (hm.congr_of_eventuallyEq heq).contDiffWithinAt
  · let u := topFormPushforward (r := r) E a F
    let K := closure {x | u x ≠ (0 : NQForm E 0) x}
    have hsource : K ⊆ bundleChartSource (r := r) E a := topFormPushforward_support_in_source E a F hc hs
    have hout : chartInv b z ∉ K := fun h => hya (hsource h)
    have hzero : ∀ᶠ y in 𝓝 (chartInv b z), u y = (0 : NQForm E 0) y := by
      filter_upwards [isClosed_closure.compl_mem_nhds hout] with y hy
      by_contra hn
      exact hy (subset_closure hn)
    have heq : (fun t => coefficients (r := r) E u b t Fin.elim0 α) =ᶠ[𝓝 z] (fun _ => 0) := by
      filter_upwards [hi.tendsto.eventually hzero] with t ht
      have hcoeff : coefficients (r := r) E u b t Fin.elim0 α =
          coefficients (r := r) E (0 : NQForm E 0) b t Fin.elim0 α := by
        unfold coefficients
        rw [ht]
      exact hcoeff.trans (coefficients_zero E b t Fin.elim0 α)
    have hm : ContDiffAt ℝ ∞ (fun _ : ComplexVector n => (0 : ℂ)) z := contDiffAt_const
    exact (hm.congr_of_eventuallyEq heq).contDiffWithinAt

end Yau.LeafProofs.L14Aux

namespace Yau.LeafProofs.L14Aux

open BundleDbar Filter

variable {n r : ℕ} {M : ComplexManifold n}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

theorem smoothForm_locallyL2 {q : ℕ} (u : NQForm E q) (hu : SmoothForm (r := r) E u) :
    LocallyL2 (r := r) E u := by
  letI : IsLocallyFiniteMeasure (lebesgueC n) := by rw [lebesgueC_eq_volume]; infer_instance
  intro a I α
  refine ⟨(hu a I α).continuousOn.aestronglyMeasurable (localDomain_isOpen E a).measurableSet, ?_⟩
  intro K hK hsub
  have hi : IntegrableOn (fun z => ‖coefficients (r := r) E u a z I α‖ ^ 2) K (lebesgueC n) :=
    (((hu a I α).continuousOn.norm.pow 2).mono hsub).integrableOn_compact hK
  exact (hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun z => sq_nonneg
    ‖coefficients (r := r) E u a z I α‖)).mp hi.2

theorem formNormSq_top_continuous (g : Yau.SmoothMetric M) (h : Metric E)
    (hh : BundleDbar.SmoothMetric (r := r) E h) (u : NQForm E 0) (hu : SmoothForm (r := r) E u) :
    Continuous (BundleDbar.formNormSq (r := r) E g.form h u) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  let O := localDomain (r := r) E x
  have hself : x ∈ bundleChartSource (r := r) E x :=
    ⟨mem_extChartAt_source x, FiberBundle.mem_baseSet_trivializationAt' x⟩
  have hz : chartPt x x ∈ O := by
    refine ⟨(extChartAt (ComplexModel n) x).map_source hself.1, ?_⟩
    change chartInv x (chartPt x x) ∈ (localTriv (r := r) E x).baseSet
    rw [chartInv_chartPt_of_mem x x (mem_chart_source _ _)]
    exact hself.2
  have hd : ContinuousOn (fun z => ((hMat g.form x z).det.re)⁻¹) O :=
    ((Complex.continuous_re.comp_continuousOn
      (L18Aux.contDiffOn_matrix_det (L18Aux.hMat_contDiffOn g x)).continuousOn).inv₀
        (fun z hz => ne_of_gt (L18Aux.hMat_det_re_pos g.form x hz))).mono Set.inter_subset_left
  have hQ : ContinuousOn (chartTopCoefficientNormSq (r := r) E h u x) O := by
    unfold chartTopCoefficientNormSq
    apply Complex.continuous_re.comp_continuousOn
    apply continuousOn_finset_sum
    intro α _
    apply continuousOn_finset_sum
    intro β _
    exact ((continuous_star.comp_continuousOn (hu x Fin.elim0 α).continuousOn).mul
      (hh x α β).continuousOn).mul (hu x Fin.elim0 β).continuousOn
  let J := fun z => ((hMat g.form x z).det.re)⁻¹ * chartTopCoefficientNormSq (r := r) E h u x z
  have hJ : ContinuousAt J (chartPt x x) := (hd.mul hQ).continuousAt ((localDomain_isOpen E x).mem_nhds hz)
  have hchart : ContinuousAt (chartPt x) x :=
    (continuousOn_extChartAt (I := ComplexModel n) x).continuousAt
      ((isOpen_extChartAt_source (I := ComplexModel n) x).mem_nhds hself.1)
  have heq : BundleDbar.formNormSq (r := r) E g.form h u =ᶠ[𝓝 x] (fun y => J (chartPt x y)) := by
    filter_upwards [(bundleChartSource_isOpen (r := r) E x).mem_nhds hself] with y hy
    have hzy : chartPt x y ∈ O := by
      refine ⟨(extChartAt (ComplexModel n) x).map_source hy.1, ?_⟩
      change chartInv x (chartPt x y) ∈ (localTriv (r := r) E x).baseSet
      rw [chartInv_chartPt_of_mem x y (by simpa only [extChartAt_source] using hy.1)]
      exact hy.2
    have hf := formNormSq_top_inChart E g.form h u x (chartPt x y) hzy
    rw [chartInv_chartPt_of_mem x y (by simpa only [extChartAt_source] using hy.1)] at hf
    exact hf
  exact (hJ.comp hchart).congr_of_eventuallyEq heq

theorem smooth_compact_weightedL2_top (g : Yau.SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (h : Metric E) (hh : BundleDbar.SmoothMetric (r := r) E h)
    (φ : M.Carrier → ℝ) (hφ : SmoothFn φ) (u : NQForm E 0) (hu : SmoothForm (r := r) E u)
    (hc : IsCompact (closure {x | u x ≠ (0 : NQForm E 0) x})) :
    WeightedL2 (r := r) E g.form h μ φ u := by
  letI : IsLocallyFiniteMeasure μ := L18Aux.riemannianVolume_locallyFinite g μ hμ
  let F := fun x => BundleDbar.formNormSq (r := r) E g.form h u x * Real.exp (-φ x)
  have hF : Continuous F := (formNormSq_top_continuous E g h hh u hu).mul
    (Real.continuous_exp.comp (L18Aux.continuous_of_smoothFn hφ).neg)
  have hs : Function.support F ⊆ {x | u x ≠ (0 : NQForm E 0) x} := by
    intro x hx hz
    apply hx
    change BundleDbar.formNormSq (r := r) E g.form h u x * Real.exp (-φ x) = 0
    rw [formNormSq_congr_at E g.form h u (0 : NQForm E 0) x hz, formNormSq_zero, zero_mul]
  have hcF : HasCompactSupport F := hc.of_isClosed_subset isClosed_closure (closure_mono hs)
  have hi : Integrable F μ := hF.integrable_of_hasCompactSupport hcF
  exact ⟨smoothForm_locallyL2 E u hu,
    (hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun x =>
      mul_nonneg (formNormSq_top_nonneg E g.form h u x) (Real.exp_pos _).le)).mp hi.2⟩

theorem topFormPushforward_weightedL2 (g : Yau.SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (h : Metric E) (hh : BundleDbar.SmoothMetric (r := r) E h)
    (φ : M.Carrier → ℝ) (hφ : SmoothFn φ) (hE : Holomorphic (r := r) E)
    (a : M.Carrier) (F : ComplexVector n → ComplexVector r)
    (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    (hs : tsupport F ⊆ localDomain (r := r) E a) :
    WeightedL2 (r := r) E g.form h μ φ (topFormPushforward (r := r) E a F) := by
  apply smooth_compact_weightedL2_top E g μ hμ h hh φ hφ _
    (topFormPushforward_smooth E hE a F hF hc hs)
  have hK : IsCompact (chartInv a '' tsupport F) := hc.image_of_continuousOn
    ((continuousOn_extChartAt_symm (I := ComplexModel n) a).mono (hs.trans Set.inter_subset_left))
  exact hK.of_isClosed_subset isClosed_closure (topFormPushforward_support E a F hc hs)

end Yau.LeafProofs.L14Aux

namespace Yau.LeafProofs.L14Aux

open BundleDbar Filter

variable {n r : ℕ} {M : ComplexManifold n}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

set_option backward.isDefEq.respectTransparency false in
theorem oneTensorFromCoefficients_apply_basis (a x : M.Carrier)
    (hx : x ∈ bundleChartSource (r := r) E a) (F : Fin n → ComplexVector r)
    (v : TangentVector M x) (c : Basis (Fin n) ℂ (TangentVector M x)) :
    ((oneTensorFromCoefficients (r := r) E a x hx F).1 (fun _ => v)) c =
      ((chartFrameBasis a x hx.1).toMatrix c).det •
        ∑ i, star ((chartFrameBasis a x hx.1).coord i v) •
          (localTriv (r := r) E a).symmL ℂ x (F i) := by
  change x ∈ (extChartAt (ComplexModel n) a).source ∧ x ∈ (localTriv (r := r) E a).baseSet at hx
  let A := oneTensorFromCoefficients (r := r) E a x hx F
  let b := chartFrameBasis a x hx.1
  have he := congrArg (fun P : (TangentVector M x) [⋀^Fin n]→ₗ[ℂ] E x => P c)
    (antiOne_apply_basis_expansion b A.1 A.2 v)
  simp only [sum_apply, AlternatingMap.smul_apply] at he
  rw [he]
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hbase : (A.1 (fun _ => b i)) b = (localTriv (r := r) E a).symmL ℂ x (F i) :=
    oneTensorFromCoefficients_basis E a x hx F i
  have hvalue : (A.1 (fun _ => b i)) c =
      (b.toMatrix c).det • (localTriv (r := r) E a).symmL ℂ x (F i) :=
    (alternating_apply_basis_change (bundleFrameBasis (r := r) E a x hx.2) b c (A.1 (fun _ => b i))).trans
      (congrArg (fun w : E x => (b.toMatrix c).det • w) hbase)
  calc
    _ = star (b.repr v i) • ((b.toMatrix c).det • (localTriv (r := r) E a).symmL ℂ x (F i)) :=
      congrArg (fun w : E x => star (b.repr v i) • w) hvalue
    _ = _ := smul_comm _ _ _

def oneFormPushforward (a : M.Carrier) (F : ComplexVector n → Fin n → ComplexVector r) : NQForm E 1 := by
  classical
  exact (show (∀ x, antiComplexSubmodule E x 1) from fun x =>
    if hx : x ∈ bundleChartSource (r := r) E a then
      oneTensorFromCoefficients (r := r) E a x hx (F (chartPt a x)) else 0)

set_option backward.isDefEq.respectTransparency false in
theorem oneFormPushforward_coefficients (a : M.Carrier)
    (F : ComplexVector n → Fin n → ComplexVector r) (z : ComplexVector n)
    (hz : z ∈ localDomain (r := r) E a) (i : Fin n) (α : Fin r) :
    coefficients (r := r) E (oneFormPushforward (r := r) E a F) a z (fun _ => i) α = F z i α := by
  classical
  have hx : chartInv a z ∈ bundleChartSource (r := r) E a :=
    ⟨(extChartAt (ComplexModel n) a).map_target hz.1, hz.2⟩
  rw [← oneTensorCoordinates_form E (oneFormPushforward (r := r) E a F) a z hz (i, α)]
  have hu : (oneFormPushforward (r := r) E a F (chartInv a z) : antiComplexSubmodule E (chartInv a z) 1) =
      oneTensorFromCoefficients (r := r) E a (chartInv a z) hx (F (chartPt a (chartInv a z))) := by
    change (if hy : chartInv a z ∈ bundleChartSource (r := r) E a then
      oneTensorFromCoefficients (r := r) E a (chartInv a z) hy (F (chartPt a (chartInv a z))) else 0) = _
    exact dif_pos hx
  rw [hu, oneTensorCoordinates_fromCoefficients]
  exact congrArg (fun w => F w i α) ((extChartAt (ComplexModel n) a).right_inv hz.1)

set_option backward.isDefEq.respectTransparency false in
theorem oneFormPushforward_coefficients_inChart (a b : M.Carrier)
    (F : ComplexVector n → Fin n → ComplexVector r) (z : ComplexVector n)
    (hz : z ∈ localDomain (r := r) E b)
    (hya : chartInv b z ∈ bundleChartSource (r := r) E a) (j : Fin n) :
    coefficients (r := r) E (oneFormPushforward (r := r) E a F) b z (fun _ => j) =
      topBundleTransition (r := r) E a b z
        (∑ i, star (fderiv ℂ (fun w => chartPt a (chartInv b w)) z (stdVec j) i) •
          F (chartPt a (chartInv b z)) i) := by
  classical
  let y := chartInv b z
  have hyb : y ∈ bundleChartSource (r := r) E b :=
    ⟨(extChartAt (ComplexModel n) b).map_target hz.1, hz.2⟩
  let d := chartFrameBasis b y hyb.1
  have hu : (oneFormPushforward (r := r) E a F y : antiComplexSubmodule E y 1) =
      oneTensorFromCoefficients (r := r) E a y hya (F (chartPt a y)) := by
    change (if hx : y ∈ bundleChartSource (r := r) E a then
      oneTensorFromCoefficients (r := r) E a y hx (F (chartPt a y)) else 0) = _
    exact dif_pos hya
  have hd : (fun k => chartVec b y (stdVec k)) = d :=
    funext (fun k => (chartFrameBasis_apply b y hyb.1 k).symm)
  have hdj : (fun _ : Fin 1 => chartVec b y (stdVec j)) = (fun _ => d j) :=
    funext (fun _ => (chartFrameBasis_apply b y hyb.1 j).symm)
  change (localTriv (r := r) E b).continuousLinearMapAt ℂ y
    (((oneFormPushforward (r := r) E a F y).1 (fun _ => chartVec b y (stdVec j)))
      (fun k => chartVec b y (stdVec k))) = _
  rw [hd, hdj, hu, oneTensorFromCoefficients_apply_basis E a y hya]
  simp_rw [chartFrameBasis_coord]
  have hj (i : Fin n) : tangentCoords a y (d j) i =
      fderiv ℂ (fun w => chartPt a (chartInv b w)) z (stdVec j) i := by
    rw [show d j = chartVec b y (stdVec j) from chartFrameBasis_apply b y hyb.1 j]
    exact (congrArg (fun v : ComplexVector n => v i)
      (L18Aux.chartTransition_fderiv b a hz.1 hya.1 (stdVec j))).symm
  simp_rw [hj]
  rw [chartFrameBasis_toMatrix_fderiv a b z hz.1 hya.1, map_smul]
  unfold topBundleTransition
  simp only [ContinuousLinearMap.smul_apply]
  congr 1
  change (localTriv (r := r) E b).continuousLinearMapAt ℂ y
      (∑ i, star (fderiv ℂ (fun w => chartPt a (chartInv b w)) z (stdVec j) i) •
        (localTriv (r := r) E a).symmL ℂ y (F (chartPt a y) i)) =
    (localTriv (r := r) E a).coordChangeL ℂ (localTriv (r := r) E b) y
      (∑ i, star (fderiv ℂ (fun w => chartPt a (chartInv b w)) z (stdVec j) i) • F (chartPt a y) i)
  rw [bundleCoordChange_apply E a b y hya.2 hyb.2]
  congr 1
  simp only [map_sum, map_smul]

end Yau.LeafProofs.L14Aux

namespace Yau.LeafProofs.L14Aux

open BundleDbar Filter

variable {n r : ℕ} {M : ComplexManifold n}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

theorem formNormSq_one_continuous (g : Yau.SmoothMetric M) (h : Metric E)
    (hh : BundleDbar.SmoothMetric (r := r) E h) (u : NQForm E 1) (hu : SmoothForm (r := r) E u) :
    Continuous (BundleDbar.formNormSq (r := r) E g.form h u) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  let O := localDomain (r := r) E x
  have hself : x ∈ bundleChartSource (r := r) E x :=
    ⟨mem_extChartAt_source x, FiberBundle.mem_baseSet_trivializationAt' x⟩
  have hz : chartPt x x ∈ O := by
    refine ⟨(extChartAt (ComplexModel n) x).map_source hself.1, ?_⟩
    change chartInv x (chartPt x x) ∈ (localTriv (r := r) E x).baseSet
    rw [chartInv_chartPt_of_mem x x (mem_chart_source _ _)]
    exact hself.2
  have hd : ContinuousOn (fun z => ((hMat g.form x z).det.re)⁻¹) O :=
    ((Complex.continuous_re.comp_continuousOn
      (L18Aux.contDiffOn_matrix_det (L18Aux.hMat_contDiffOn g x)).continuousOn).inv₀
        (fun z hz => ne_of_gt (L18Aux.hMat_det_re_pos g.form x hz))).mono Set.inter_subset_left
  have hQ : ContinuousOn (chartOneCoefficientNormSq (r := r) E g.form h u x) O := by
    unfold chartOneCoefficientNormSq
    simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum]
    apply Complex.continuous_re.comp_continuousOn
    apply continuousOn_finset_sum
    intro p _
    apply continuousOn_finset_sum
    intro q _
    exact (continuous_star.comp_continuousOn (hu x (fun _ => p.1) p.2).continuousOn).mul
      ((chartOneMetricMatrix_contDiffOn (r := r) E g h hh x p q).continuousOn.mul
        (hu x (fun _ => q.1) q.2).continuousOn)
  let J := fun z => ((hMat g.form x z).det.re)⁻¹ * chartOneCoefficientNormSq (r := r) E g.form h u x z
  have hJ : ContinuousAt J (chartPt x x) := (hd.mul hQ).continuousAt ((localDomain_isOpen E x).mem_nhds hz)
  have hchart : ContinuousAt (chartPt x) x :=
    (continuousOn_extChartAt (I := ComplexModel n) x).continuousAt
      ((isOpen_extChartAt_source (I := ComplexModel n) x).mem_nhds hself.1)
  have heq : BundleDbar.formNormSq (r := r) E g.form h u =ᶠ[𝓝 x] (fun y => J (chartPt x y)) := by
    filter_upwards [(bundleChartSource_isOpen (r := r) E x).mem_nhds hself] with y hy
    have hzy : chartPt x y ∈ O := by
      refine ⟨(extChartAt (ComplexModel n) x).map_source hy.1, ?_⟩
      change chartInv x (chartPt x y) ∈ (localTriv (r := r) E x).baseSet
      rw [chartInv_chartPt_of_mem x y (by simpa only [extChartAt_source] using hy.1)]
      exact hy.2
    have hf := formNormSq_one_chart_factor E g.form h u x (chartPt x y) hzy
    rw [chartInv_chartPt_of_mem x y (by simpa only [extChartAt_source] using hy.1)] at hf
    exact hf
  exact (hJ.comp hchart).congr_of_eventuallyEq heq

theorem smooth_compact_weightedL2_one (g : Yau.SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (h : Metric E) (hh : BundleDbar.SmoothMetric (r := r) E h)
    (φ : M.Carrier → ℝ) (hφ : SmoothFn φ) (u : NQForm E 1) (hu : SmoothForm (r := r) E u)
    (hc : IsCompact (closure {x | u x ≠ (0 : NQForm E 1) x})) :
    WeightedL2 (r := r) E g.form h μ φ u := by
  letI : IsLocallyFiniteMeasure μ := L18Aux.riemannianVolume_locallyFinite g μ hμ
  let F := fun x => BundleDbar.formNormSq (r := r) E g.form h u x * Real.exp (-φ x)
  have hF : Continuous F := (formNormSq_one_continuous E g h hh u hu).mul
    (Real.continuous_exp.comp (L18Aux.continuous_of_smoothFn hφ).neg)
  have hs : Function.support F ⊆ {x | u x ≠ (0 : NQForm E 1) x} := by
    intro x hx hz
    apply hx
    change BundleDbar.formNormSq (r := r) E g.form h u x * Real.exp (-φ x) = 0
    rw [formNormSq_congr_at E g.form h u (0 : NQForm E 1) x hz, formNormSq_zero, zero_mul]
  have hcF : HasCompactSupport F := hc.of_isClosed_subset isClosed_closure (closure_mono hs)
  have hi : Integrable F μ := hF.integrable_of_hasCompactSupport hcF
  exact ⟨smoothForm_locallyL2 E u hu,
    (hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun x =>
      mul_nonneg (formNormSq_one_nonneg (r := r) E g.form h u x) (Real.exp_pos _).le)).mp hi.2⟩

end Yau.LeafProofs.L14Aux

namespace Yau.LeafProofs.L14Aux

variable {V U : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedAddCommGroup U] [NormedSpace ℂ U]

theorem wirtBar_mul_rule (f g : V → ℂ) (z v : V)
    (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) :
    wirtBar (fun x => f x * g x) z v = wirtBar f z v * g z + f z * wirtBar g z v := by
  unfold wirtBar
  rw [fderiv_fun_mul hf hg]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

theorem wirtBar_eq_zero_of_complex_differentiable (f : V → ℂ) (z v : V)
    (hf : DifferentiableAt ℂ f z) : wirtBar f z v = 0 := by
  unfold wirtBar
  rw [hf.fderiv_restrictScalars (𝕜 := ℝ)]
  change (1 / 2 : ℂ) * (fderiv ℂ f z v + Complex.I * fderiv ℂ f z (Complex.I • v)) = 0
  rw [map_smul, smul_eq_mul, ← mul_assoc, Complex.I_mul_I]
  ring

theorem wirtBar_comp_complex_differentiable (T : V → U) (f : U → ℂ) (z v : V)
    (hT : DifferentiableAt ℂ T z) (hf : DifferentiableAt ℝ f (T z)) :
    wirtBar (fun x => f (T x)) z v = wirtBar f (T z) (fderiv ℂ T z v) := by
  unfold wirtBar
  have hd : fderiv ℝ (fun x => f (T x)) z =
      (fderiv ℝ f (T z)).comp (fderiv ℝ T z) := fderiv_comp z hf (hT.restrictScalars ℝ)
  rw [hd, hT.fderiv_restrictScalars (𝕜 := ℝ)]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars']
  rw [map_smul]

theorem realLinear_complex_smul (L : V →L[ℝ] ℂ) (c : ℂ) (v : V) :
    L (c • v) = (c.re : ℂ) * L v + (c.im : ℂ) * L (Complex.I • v) := by
  have he : c • v = c.re • v + c.im • (Complex.I • v) := by
    calc
      c • v = ((c.re : ℂ) + (c.im : ℂ) * Complex.I) • v :=
        congrArg (fun t : ℂ => t • v) (Complex.re_add_im c).symm
      _ = _ := by
        rw [add_smul, mul_smul]
        exact congrArg₂ (· + ·) (algebraMap_smul ℂ c.re v)
          (algebraMap_smul ℂ c.im (Complex.I • v))
  rw [he, map_add, map_smul, map_smul, Complex.real_smul, Complex.real_smul]

theorem wirtBar_add_direction (f : V → ℂ) (z v w : V) :
    wirtBar f z (v + w) = wirtBar f z v + wirtBar f z w := by
  unfold wirtBar
  rw [map_add, smul_add, map_add]
  ring

theorem wirtBar_smul_direction (f : V → ℂ) (z v : V) (c : ℂ) :
    wirtBar f z (c • v) = star c * wirtBar f z v := by
  have he : Complex.I • (c • v) = (Complex.I * c) • v := (mul_smul _ _ _).symm
  unfold wirtBar
  rw [realLinear_complex_smul (fderiv ℝ f z) c v, he,
    realLinear_complex_smul (fderiv ℝ f z) (Complex.I * c) v]
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im, Complex.star_def] <;> ring

theorem wirtBar_sum_direction {ι : Type*} (f : V → ℂ) (z : V)
    (s : Finset ι) (w : ι → V) :
    wirtBar f z (∑ i ∈ s, w i) = ∑ i ∈ s, wirtBar f z (w i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [wirtBar]
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi, wirtBar_add_direction, ih]

theorem wirtBar_direction_coordinates {n : ℕ} (f : ComplexVector n → ℂ) (z v : ComplexVector n) :
    wirtBar f z v = ∑ i : Fin n, star (v i) * wirtBar f z (stdVec i) := by
  have hv : (∑ i : Fin n, v i • stdVec i) = v := by
    ext j
    simp [stdVec, PiLp.single_apply, Pi.single_apply, Finset.sum_apply', PiLp.smul_apply, eq_comm]
  calc
    wirtBar f z v = wirtBar f z (∑ i : Fin n, v i • stdVec i) := congrArg (wirtBar f z) hv.symm
    _ = ∑ i : Fin n, wirtBar f z (v i • stdVec i) := wirtBar_sum_direction f z Finset.univ _
    _ = _ := Finset.sum_congr rfl (fun i _ => wirtBar_smul_direction f z (stdVec i) (v i))

theorem wirtBar_sum_fun {ι : Type*} (s : Finset ι) (f : ι → V → ℂ) (z v : V)
    (hf : ∀ i ∈ s, DifferentiableAt ℝ (f i) z) :
    wirtBar (fun x => ∑ i ∈ s, f i x) z v = ∑ i ∈ s, wirtBar (f i) z v := by
  unfold wirtBar
  have hd : fderiv ℝ (fun x => ∑ i ∈ s, f i x) z = ∑ i ∈ s, fderiv ℝ (f i) z :=
    fderiv_fun_sum hf
  rw [hd]
  simp only [sum_apply, Finset.mul_sum, mul_add, Finset.sum_add_distrib, mul_assoc]

theorem complexLinear_apply_coordinates {r : ℕ}
    (L : ComplexVector r →L[ℂ] ComplexVector r) (v : ComplexVector r) (α : Fin r) :
    L v α = ∑ β, L (stdVec β) α * v β := by
  have hv : (∑ β : Fin r, v β • stdVec β) = v := by
    ext j
    simp [stdVec, PiLp.single_apply, Pi.single_apply, Finset.sum_apply', PiLp.smul_apply]
  let Lα : ComplexVector r →ₗ[ℂ] ℂ := (EuclideanSpace.projₗ α).comp L.toLinearMap
  have he := congrArg Lα hv
  simp only [map_sum, map_smul, smul_eq_mul] at he
  change Lα v = _
  exact he.symm.trans (Finset.sum_congr rfl (fun β _ => mul_comm _ _))

theorem wirtBar_holomorphic_matrix_apply_comp {n r : ℕ}
    (P : ComplexVector n → ComplexVector r →L[ℂ] ComplexVector r)
    (T : ComplexVector n → ComplexVector n) (F : ComplexVector n → ComplexVector r)
    (z v : ComplexVector n) (α : Fin r)
    (hP : ContDiffAt ℂ ∞ P z) (hT : ContDiffAt ℂ ∞ T z)
    (hF : ContDiffAt ℝ ∞ F (T z)) :
    wirtBar (fun x => P x (F (T x)) α) z v =
      ∑ i : Fin n, star (fderiv ℂ T z v i) *
        P z (WithLp.toLp 2 (fun β => wirtBar (fun w => F w β) (T z) (stdVec i))) α := by
  have hfun : (fun x => P x (F (T x)) α) =
      (fun x => ∑ β : Fin r, P x (stdVec β) α * F (T x) β) :=
    funext (fun x => complexLinear_apply_coordinates (P x) (F (T x)) α)
  have hPβ (β : Fin r) : DifferentiableAt ℂ (fun x => P x (stdVec β) α) z := by
    have hv : ContDiffAt ℂ ∞ (fun x => P x (stdVec β)) z := hP.clm_apply contDiffAt_const
    exact ((contDiffAt_piLp 2).mp hv α).differentiableAt (by simp)
  have hFβ (β : Fin r) : DifferentiableAt ℝ (fun x => F x β) (T z) :=
    ((contDiffAt_piLp 2).mp hF β).differentiableAt (by simp)
  have hTd : DifferentiableAt ℂ T z := hT.differentiableAt (by simp)
  have hFd (β : Fin r) : DifferentiableAt ℝ (fun x => F (T x) β) z :=
    (hFβ β).comp z (hTd.restrictScalars ℝ)
  rw [hfun, wirtBar_sum_fun Finset.univ
    (fun β x => P x (stdVec β) α * F (T x) β) z v
    (fun β _ => ((hPβ β).restrictScalars ℝ).mul (hFd β))]
  have hterm (β : Fin r) :
      wirtBar (fun x => P x (stdVec β) α * F (T x) β) z v =
        P z (stdVec β) α * ∑ i : Fin n,
          star (fderiv ℂ T z v i) * wirtBar (fun w => F w β) (T z) (stdVec i) := by
    rw [wirtBar_mul_rule _ _ z v ((hPβ β).restrictScalars ℝ) (hFd β),
      wirtBar_eq_zero_of_complex_differentiable _ z v (hPβ β), zero_mul, zero_add,
      wirtBar_comp_complex_differentiable T (fun w => F w β) z v hTd (hFβ β),
      wirtBar_direction_coordinates]
  simp_rw [hterm]
  have hright :
      (∑ i : Fin n, star (fderiv ℂ T z v i) *
        P z (WithLp.toLp 2 (fun β => wirtBar (fun w => F w β) (T z) (stdVec i))) α) =
      ∑ i : Fin n, star (fderiv ℂ T z v i) *
        ∑ β : Fin r, P z (stdVec β) α * wirtBar (fun w => F w β) (T z) (stdVec i) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [complexLinear_apply_coordinates (P z)
      (WithLp.toLp 2 (fun β => wirtBar (fun w => F w β) (T z) (stdVec i))) α]
  rw [hright]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro β _
  ring

end Yau.LeafProofs.L14Aux

namespace Yau.LeafProofs.L14Aux

open BundleDbar Filter

variable {n r : ℕ} {M : ComplexManifold n}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

def modelTopDbar (F : ComplexVector n → ComplexVector r) (z : ComplexVector n)
    (i : Fin n) : ComplexVector r :=
  WithLp.toLp 2 (fun α => wirtBar (fun w => F w α) z (stdVec i))

set_option backward.isDefEq.respectTransparency false in
theorem topFormPushforward_isDbarOf (hE : Holomorphic (r := r) E)
    (a : M.Carrier) (F : ComplexVector n → ComplexVector r)
    (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    (hs : tsupport F ⊆ localDomain (r := r) E a) :
    IsDbarOf (r := r) E (topFormPushforward (r := r) E a F)
      (oneFormPushforward (r := r) E a (modelTopDbar F)) := by
  classical
  intro b z hz I α
  let j := I 0
  have hI : I = (fun _ => j) := funext (fun k => congrArg I (Subsingleton.elim k 0))
  rw [hI]
  have hJ : (fun _ : Fin 0 => j) = (Fin.elim0 : Fin 0 → Fin n) := Subsingleton.elim _ _
  simp only [dbarCoefficients, hJ]
  change coefficients (r := r) E (oneFormPushforward (r := r) E a (modelTopDbar F)) b z (fun _ => j) α =
    ∑ k : Fin 1, (-1 : ℂ) ^ k.val *
      wirtBar (fun w => coefficients (r := r) E (topFormPushforward (r := r) E a F) b w Fin.elim0 α)
        z (stdVec j)
  simp only [Fin.sum_univ_one, Fin.val_zero, pow_zero, one_mul]
  let y := chartInv b z
  let u := topFormPushforward (r := r) E a F
  let f := oneFormPushforward (r := r) E a (modelTopDbar F)
  have hi : ContinuousAt (chartInv b) z := continuousAt_extChartAt_symm'' (I := ComplexModel n) hz.1
  by_cases hya : y ∈ bundleChartSource (r := r) E a
  · let T := fun t => chartPt a (chartInv b t)
    let P := topBundleTransition (r := r) E a b
    have hP : ContDiffAt ℂ ∞ P z := topBundleTransition_contDiffAt E hE a b z hz hya
    have hT : ContDiffAt ℂ ∞ T z := L18Aux.chartTransition_contDiffAt b a hz.1 hya.1
    have heq : (fun t => coefficients (r := r) E u b t Fin.elim0 α) =ᶠ[𝓝 z]
        (fun t => P t (F (T t)) α) := by
      filter_upwards [(localDomain_isOpen E b).mem_nhds hz,
        hi.tendsto.eventually ((bundleChartSource_isOpen (r := r) E a).mem_nhds hya)] with t htb hta
      exact congrArg (fun v : ComplexVector r => v α)
        (topFormPushforward_coefficients_inChart E a b F t htb hta)
    have hw : wirtBar (fun t => coefficients (r := r) E u b t Fin.elim0 α) z (stdVec j) =
        wirtBar (fun t => P t (F (T t)) α) z (stdVec j) := by
      unfold wirtBar
      rw [heq.fderiv_eq]
    have hn := wirtBar_holomorphic_matrix_apply_comp P T F z (stdVec j) α hP hT hF.contDiffAt
    have hfchart := congrArg (fun v : ComplexVector r => v α)
      (oneFormPushforward_coefficients_inChart E a b (modelTopDbar F) z hz hya j)
    calc
      coefficients (r := r) E f b z (fun _ => j) α =
          P z (∑ i, star (fderiv ℂ T z (stdVec j) i) • modelTopDbar F (T z) i) α := hfchart
      _ = ∑ i, star (fderiv ℂ T z (stdVec j) i) * P z (modelTopDbar F (T z) i) α := by
        let Lα : ComplexVector r →ₗ[ℂ] ℂ := (EuclideanSpace.projₗ α).comp (P z).toLinearMap
        change Lα (∑ i, star (fderiv ℂ T z (stdVec j) i) • modelTopDbar F (T z) i) =
          ∑ i, star (fderiv ℂ T z (stdVec j) i) * Lα (modelTopDbar F (T z) i)
        simp only [map_sum, map_smul, smul_eq_mul]
      _ = wirtBar (fun t => P t (F (T t)) α) z (stdVec j) := hn.symm
      _ = wirtBar (fun t => coefficients (r := r) E u b t Fin.elim0 α) z (stdVec j) := hw.symm
  · have hfzero : (f y : antiComplexSubmodule E y 1) = (0 : antiComplexSubmodule E y 1) := by
      change (if hx : y ∈ bundleChartSource (r := r) E a then
        oneTensorFromCoefficients (r := r) E a y hx (modelTopDbar F (chartPt a y))
        else (0 : antiComplexSubmodule E y 1)) = (0 : antiComplexSubmodule E y 1)
      exact dif_neg hya
    have hfc : coefficients (r := r) E f b z (fun _ => j) α = 0 := by
      have he : coefficients (r := r) E f b z (fun _ => j) α =
          coefficients (r := r) E (0 : NQForm E 1) b z (fun _ => j) α := by
        unfold coefficients
        rw [hfzero]
        rfl
      exact he.trans (coefficients_zero E b z (fun _ => j) α)
    let K := closure {x | u x ≠ (0 : NQForm E 0) x}
    have hsource : K ⊆ bundleChartSource (r := r) E a := topFormPushforward_support_in_source E a F hc hs
    have hout : y ∉ K := fun h => hya (hsource h)
    have hzero : ∀ᶠ x in 𝓝 y, u x = (0 : NQForm E 0) x := by
      filter_upwards [isClosed_closure.compl_mem_nhds hout] with x hx
      by_contra hn
      exact hx (subset_closure hn)
    have heq : (fun t => coefficients (r := r) E u b t Fin.elim0 α) =ᶠ[𝓝 z] (fun _ => 0) := by
      filter_upwards [hi.tendsto.eventually hzero] with t ht
      have he : coefficients (r := r) E u b t Fin.elim0 α =
          coefficients (r := r) E (0 : NQForm E 0) b t Fin.elim0 α := by
        unfold coefficients
        rw [ht]
      exact he.trans (coefficients_zero E b t Fin.elim0 α)
    have hw : wirtBar (fun t => coefficients (r := r) E u b t Fin.elim0 α) z (stdVec j) = 0 := by
      unfold wirtBar
      rw [heq.fderiv_eq]
      simp
    exact hfc.trans hw.symm

end Yau.LeafProofs.L14Aux

namespace Yau.LeafProofs.L14Aux

open BundleDbar Filter

theorem modelTopDbar_smooth {n r : ℕ} (F : ComplexVector n → ComplexVector r)
    (hF : ContDiff ℝ ∞ F) : ContDiff ℝ ∞ (modelTopDbar F) := by
  apply contDiff_pi.mpr
  intro i
  apply (contDiff_piLp 2).mpr
  intro α
  exact wirtBar_contDiff (fun w => F w α) ((contDiff_piLp 2).mp hF α) (stdVec i)

theorem tsupport_modelTopDbar_subset {n r : ℕ} (F : ComplexVector n → ComplexVector r) :
    tsupport (modelTopDbar F) ⊆ tsupport F := by
  apply closure_minimal _ (isClosed_tsupport F)
  intro z hz
  by_contra hn
  apply hz
  funext i
  ext α
  change wirtBar (fun w => F w α) z (stdVec i) = 0
  have hα : tsupport (fun w => F w α) ⊆ tsupport F :=
    tsupport_comp_subset (g := fun v : ComplexVector r => v α) (by rfl) F
  by_contra hd
  exact hn (hα (support_wirtBar_subset (fun w => F w α) (stdVec i) hd))

variable {n r : ℕ} {M : ComplexManifold n}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

theorem smoothForm_of_isDbarOf (u : NQForm E 0) (f : NQForm E 1)
    (hu : SmoothForm (r := r) E u) (hD : IsDbarOf (r := r) E u f) :
    SmoothForm (r := r) E f := by
  intro a I α
  have hd : ContDiffOn ℝ ∞ (fun z => dbarCoefficients (r := r) E u a z I α)
      (localDomain (r := r) E a) := by
    unfold dbarCoefficients
    apply ContDiffOn.sum
    intro k _
    exact contDiffOn_const.mul (wirtBar_contDiffOn (localDomain_isOpen E a) _
      (hu a (fun l => I (k.succAbove l)) α) (stdVec (I k)))
  exact hd.congr (fun z hz => hD a z hz I α)

theorem oneTensorFromCoefficients_zero (a x : M.Carrier)
    (hx : x ∈ bundleChartSource (r := r) E a) :
    oneTensorFromCoefficients (r := r) E a x hx (0 : Fin n → ComplexVector r) = 0 := by
  apply oneTensorCoordinates_injective E a x hx
  ext p
  rcases p with ⟨i, α⟩
  rw [oneTensorCoordinates_fromCoefficients, map_zero]
  rfl

theorem oneFormPushforward_support (a : M.Carrier) (F : ComplexVector n → Fin n → ComplexVector r)
    (hc : HasCompactSupport F) (hs : tsupport F ⊆ localDomain (r := r) E a) :
    closure {x | oneFormPushforward (r := r) E a F x ≠ (0 : NQForm E 1) x} ⊆ chartInv a '' tsupport F := by
  classical
  have hK : IsCompact (chartInv a '' tsupport F) := hc.image_of_continuousOn
    ((continuousOn_extChartAt_symm (I := ComplexModel n) a).mono (hs.trans Set.inter_subset_left))
  apply closure_minimal _ hK.isClosed
  intro x hx
  change oneFormPushforward (r := r) E a F x ≠ (0 : antiComplexSubmodule E x 1) at hx
  by_cases hxa : x ∈ bundleChartSource (r := r) E a
  · have hn : F (chartPt a x) ≠ 0 := by
      intro hf
      apply hx
      change (if h : x ∈ bundleChartSource (r := r) E a then
        oneTensorFromCoefficients (r := r) E a x h (F (chartPt a x)) else 0) = 0
      rw [dif_pos hxa, hf, oneTensorFromCoefficients_zero]
    exact ⟨chartPt a x, subset_closure hn,
      chartInv_chartPt_of_mem a x (by simpa only [extChartAt_source] using hxa.1)⟩
  · apply False.elim
    apply hx
    change (if h : x ∈ bundleChartSource (r := r) E a then
      oneTensorFromCoefficients (r := r) E a x h (F (chartPt a x)) else 0) = 0
    exact dif_neg hxa

end Yau.LeafProofs.L14Aux

namespace Yau.LeafProofs.L14Aux

open BundleDbar Filter

theorem integrable_compactTest_mul_complex {n : ℕ}
    {O : Set (ComplexVector n)} (hO : IsOpen O) {ψ u : ComplexVector n → ℂ}
    (hψ : Continuous ψ) (hc : HasCompactSupport ψ) (hs : tsupport ψ ⊆ O)
    (hu : ContinuousOn u O) : Integrable (fun x => ψ x * u x) (lebesgueC n) := by
  letI : IsLocallyFiniteMeasure (lebesgueC n) := by rw [lebesgueC_eq_volume]; infer_instance
  have hcont : Continuous (fun x => ψ x * u x) := by
    rw [continuous_iff_continuousAt]
    intro x
    by_cases hx : x ∈ tsupport ψ
    · exact hψ.continuousAt.mul (hu.continuousAt (hO.mem_nhds (hs hx)))
    · have heq : (fun y => ψ y * u y) =ᶠ[𝓝 x] (fun _ => 0) := by
        filter_upwards [(isClosed_tsupport ψ).isOpen_compl.mem_nhds hx] with y hy
        simp only [image_eq_zero_of_notMem_tsupport hy, zero_mul]
      exact continuousAt_const.congr heq.symm
  exact hcont.integrable_of_hasCompactSupport hc.mul_right

theorem integral_compactTest_direction_complex_on {n : ℕ}
    {O : Set (ComplexVector n)} (hO : IsOpen O) {ψ u : ComplexVector n → ℂ}
    (hψ : ContDiff ℝ 1 ψ) (hc : HasCompactSupport ψ) (hs : tsupport ψ ⊆ O)
    (hu : ContDiffOn ℝ 1 u O) (v : ComplexVector n) :
    (∫ x, ψ x * fderiv ℝ u x v ∂lebesgueC n) =
      -(∫ x, fderiv ℝ ψ x v * u x ∂lebesgueC n) := by
  letI : (lebesgueC n).IsAddHaarMeasure := by rw [lebesgueC_eq_volume]; infer_instance
  have hdψ : Continuous (fun x => fderiv ℝ ψ x v) :=
    (hψ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hdψO : tsupport (fun x => fderiv ℝ ψ x v) ⊆ O :=
    (tsupport_fderiv_apply_subset ℝ v).trans hs
  have hdu : ContinuousOn (fun x => fderiv ℝ u x v) O :=
    (hu.continuousOn_fderiv_of_isOpen hO le_rfl).clm_apply continuousOn_const
  exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (integrable_compactTest_mul_complex hO hdψ (hc.fderiv_apply ℝ v) hdψO hu.continuousOn)
    (integrable_compactTest_mul_complex hO hψ.continuous hc hs hdu)
    (integrable_compactTest_mul_complex hO hψ.continuous hc hs hu.continuousOn)
    (fun x _ => hψ.differentiable one_ne_zero x)
    (fun x hx => (hu.contDiffAt (hO.mem_nhds (hs hx))).differentiableAt one_ne_zero)

theorem integral_compactTest_wirtBar_on {n : ℕ}
    {O : Set (ComplexVector n)} (hO : IsOpen O) {ψ u : ComplexVector n → ℂ}
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ) (hs : tsupport ψ ⊆ O)
    (hu : ContDiffOn ℝ ∞ u O) (v : ComplexVector n) :
    (∫ x, wirtBar u x v * ψ x ∂lebesgueC n) =
      -(∫ x, u x * wirtBar ψ x v ∂lebesgueC n) := by
  have hψ₁ : ContDiff ℝ 1 ψ := hψ.of_le (by simp)
  have hu₁ : ContDiffOn ℝ 1 u O := hu.of_le (by simp)
  have hL (w : ComplexVector n) : Integrable (fun x => ψ x * fderiv ℝ u x w) (lebesgueC n) :=
    integrable_compactTest_mul_complex hO hψ.continuous hc hs
      ((hu₁.continuousOn_fderiv_of_isOpen hO le_rfl).clm_apply continuousOn_const)
  have hR (w : ComplexVector n) : Integrable (fun x => fderiv ℝ ψ x w * u x) (lebesgueC n) :=
    integrable_compactTest_mul_complex hO
      ((hψ₁.continuous_fderiv one_ne_zero).clm_apply continuous_const)
      (hc.fderiv_apply ℝ w) ((tsupport_fderiv_apply_subset ℝ w).trans hs) hu.continuousOn
  have hleft : (∫ x, wirtBar u x v * ψ x ∂lebesgueC n) =
      (1 / 2 : ℂ) * ((∫ x, ψ x * fderiv ℝ u x v ∂lebesgueC n) +
        Complex.I * ∫ x, ψ x * fderiv ℝ u x (Complex.I • v) ∂lebesgueC n) := by
    calc
      _ = ∫ x, (1 / 2 : ℂ) * (ψ x * fderiv ℝ u x v +
          Complex.I * (ψ x * fderiv ℝ u x (Complex.I • v))) ∂lebesgueC n :=
        integral_congr_ae (Eventually.of_forall fun x => by unfold wirtBar; ring)
      _ = _ := by
        rw [integral_const_mul, integral_add (hL v) ((hL (Complex.I • v)).const_mul Complex.I), integral_const_mul]
  have hright : (∫ x, u x * wirtBar ψ x v ∂lebesgueC n) =
      (1 / 2 : ℂ) * ((∫ x, fderiv ℝ ψ x v * u x ∂lebesgueC n) +
        Complex.I * ∫ x, fderiv ℝ ψ x (Complex.I • v) * u x ∂lebesgueC n) := by
    calc
      _ = ∫ x, (1 / 2 : ℂ) * (fderiv ℝ ψ x v * u x +
          Complex.I * (fderiv ℝ ψ x (Complex.I • v) * u x)) ∂lebesgueC n :=
        integral_congr_ae (Eventually.of_forall fun x => by unfold wirtBar; ring)
      _ = _ := by
        rw [integral_const_mul, integral_add (hR v) ((hR (Complex.I • v)).const_mul Complex.I), integral_const_mul]
  rw [hleft, hright,
    integral_compactTest_direction_complex_on hO hψ₁ hc hs hu₁ v,
    integral_compactTest_direction_complex_on hO hψ₁ hc hs hu₁ (Complex.I • v)]
  ring

variable {n r : ℕ} {M : ComplexManifold n}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

theorem weakDbar_of_smooth_isDbarOf (u : NQForm E 0) (f : NQForm E 1)
    (hu : SmoothForm (r := r) E u) (hf : SmoothForm (r := r) E f)
    (hD : IsDbarOf (r := r) E u f) : WeakDbar (r := r) E u f := by
  apply (weakDbar_zero_iff_component_tests E u f).mpr
  refine ⟨smoothForm_locallyL2 E u hu, smoothForm_locallyL2 E f hf, ?_⟩
  intro a i α ψ hψ hc hs
  have hJ : (fun _ : Fin 0 => i) = (Fin.elim0 : Fin 0 → Fin n) := Subsingleton.elim _ _
  have hco (z : ComplexVector n) (hz : z ∈ localDomain (r := r) E a) :
      coefficients (r := r) E f a z (fun _ => i) α =
        wirtBar (fun w => coefficients (r := r) E u a w Fin.elim0 α) z (stdVec i) := by
    have he := hD a z hz (fun _ => i) α
    simp only [dbarCoefficients, hJ] at he
    change coefficients (r := r) E f a z (fun _ => i) α =
      ∑ k : Fin 1, (-1 : ℂ) ^ k.val *
        wirtBar (fun w => coefficients (r := r) E u a w Fin.elim0 α) z (stdVec i) at he
    simpa only [Fin.sum_univ_one, Fin.val_zero, pow_zero, one_mul] using he
  calc
    _ = ∫ z, wirtBar (fun w => coefficients (r := r) E u a w Fin.elim0 α) z (stdVec i) * ψ z ∂lebesgueC n := by
      apply integral_congr_ae
      apply Eventually.of_forall
      intro z
      by_cases hz : z ∈ localDomain (r := r) E a
      · exact congrArg (fun c : ℂ => c * ψ z) (hco z hz)
      · have hzψ : ψ z = 0 := by
          by_contra hn
          exact hz (hs (subset_tsupport ψ hn))
        simp only [hzψ, mul_zero]
    _ = _ := integral_compactTest_wirtBar_on (localDomain_isOpen E a) hψ hc hs (hu a Fin.elim0 α) (stdVec i)

end Yau.LeafProofs.L14Aux

namespace Yau.LeafProofs.L14Aux

open BundleDbar Filter

variable {n r : ℕ} {M : ComplexManifold n}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]
variable (g : Yau.SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
  (h : Metric E) (hh : BundleDbar.SmoothMetric (r := r) E h) (φ : M.Carrier → ℝ) (hφ : SmoothFn φ)
  (hE : Holomorphic (r := r) E)

include hμ hh hφ hE

theorem topFormPushforward_maximalDbarGraph
    (a : M.Carrier) (F : ComplexVector n → ComplexVector r)
    (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    (hs : tsupport F ⊆ localDomain (r := r) E a) :
    MaximalDbarGraph (r := r) E g.form h μ φ
      (topFormPushforward (r := r) E a F) (oneFormPushforward (r := r) E a (modelTopDbar F)) := by
  let u := topFormPushforward (r := r) E a F
  let f := oneFormPushforward (r := r) E a (modelTopDbar F)
  have hu : SmoothForm (r := r) E u := topFormPushforward_smooth E hE a F hF hc hs
  have hD : IsDbarOf (r := r) E u f := topFormPushforward_isDbarOf E hE a F hF hc hs
  have hf : SmoothForm (r := r) E f := smoothForm_of_isDbarOf E u f hu hD
  have hcD : HasCompactSupport (modelTopDbar F) :=
    hc.of_isClosed_subset (isClosed_tsupport _) (tsupport_modelTopDbar_subset F)
  have hsD : tsupport (modelTopDbar F) ⊆ localDomain (r := r) E a :=
    (tsupport_modelTopDbar_subset F).trans hs
  have hK : IsCompact (chartInv a '' tsupport (modelTopDbar F)) := hcD.image_of_continuousOn
    ((continuousOn_extChartAt_symm (I := ComplexModel n) a).mono (hsD.trans Set.inter_subset_left))
  have hcf : IsCompact (closure {x | f x ≠ (0 : NQForm E 1) x}) :=
    hK.of_isClosed_subset isClosed_closure (oneFormPushforward_support E a (modelTopDbar F) hcD hsD)
  exact ⟨topFormPushforward_weightedL2 E g μ hμ h hh φ hφ hE a F hF hc hs,
    smooth_compact_weightedL2_one E g μ hμ h hh φ hφ f hf hcf,
    weakDbar_of_smooth_isDbarOf E u f hu hf hD⟩

def weightedTopChartSection (a : M.Carrier) (F : ComplexVector n → ComplexVector r)
    (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    (hs : tsupport F ⊆ localDomain (r := r) E a) : WeightedTopSection E g μ hμ h hh φ hφ :=
  ⟨topFormPushforward (r := r) E a F, topFormPushforward_weightedL2 E g μ hμ h hh φ hφ hE a F hF hc hs⟩

theorem weightedTopChartSection_mem_domain (a : M.Carrier) (F : ComplexVector n → ComplexVector r)
    (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    (hs : tsupport F ⊆ localDomain (r := r) E a) :
    realizeWeightedTopSection E g μ hμ h hh φ hφ
      (weightedTopChartSection E g μ hμ h hh φ hφ hE a F hF hc hs) ∈
        (weightedMaximalDbar E g μ hμ h hh φ hφ).domain := by
  have hg := topFormPushforward_maximalDbarGraph E g μ hμ h hh φ hφ hE a F hF hc hs
  let U : WeightedTopSection E g μ hμ h hh φ hφ :=
    ⟨topFormPushforward (r := r) E a F, hg.1⟩
  let V : WeightedOneSection E g μ hμ h hh φ hφ :=
    ⟨oneFormPushforward (r := r) E a (modelTopDbar F), hg.2.1⟩
  have hmem : (realizeWeightedTopSection E g μ hμ h hh φ hφ U,
      realizeWeightedOneSection E g μ hμ h hh φ hφ V) ∈
        weightedMaximalDbarHilbertGraph E g μ hμ h hh φ hφ :=
    (weightedMaximalDbarHilbertGraph_realize_iff E g μ hμ h hh φ hφ U V).mpr hg.2.2
  change realizeWeightedTopSection E g μ hμ h hh φ hφ U ∈
    (weightedMaximalDbarHilbertGraph E g μ hμ h hh φ hφ).map
      (LinearMap.fst ℂ (WeightedTopHilbert E g μ hμ h hh φ hφ) (WeightedOneHilbert E g μ hμ h hh φ hφ))
  exact ⟨(realizeWeightedTopSection E g μ hμ h hh φ hφ U,
    realizeWeightedOneSection E g μ hμ h hh φ hφ V), hmem, rfl⟩

end Yau.LeafProofs.L14Aux

namespace Yau.LeafProofs.L14Aux

open BundleDbar Filter

variable {n r : ℕ} {M : ComplexManifold n}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

theorem weightedTopPairing_eq_zero_of_left_zero (g : HermitianField M) (h : Metric E)
    (φ : M.Carrier → ℝ) (u v : NQForm E 0) (x : M.Carrier)
    (hx : u x = (0 : NQForm E 0) x) : weightedTopPairing E g h φ u v x = 0 := by
  have hu : topFormValue E u x x = 0 := by
    unfold topFormValue
    rw [hx]
    rfl
  have hh := (h x).map_smul_left (0 : ℂ) (0 : E x) (topFormValue E v x x)
  simp only [zero_smul, star_zero, zero_mul] at hh
  unfold weightedTopPairing topFormPairing
  rw [hu, hh, mul_zero, zero_mul]

variable (g : Yau.SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
  (h : Metric E) (hh : BundleDbar.SmoothMetric (r := r) E h) (φ : M.Carrier → ℝ) (hφ : SmoothFn φ)
  (hE : Holomorphic (r := r) E)

include hE

set_option backward.isDefEq.respectTransparency false in
theorem weightedTopInner_topFormPushforward_re
    (a : M.Carrier) (F : ComplexVector n → ComplexVector r)
    (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    (hs : tsupport F ⊆ localDomain (r := r) E a)
    (v : WeightedTopSection E g μ hμ h hh φ hφ) :
    (weightedTopInner E g.form μ h φ (topFormPushforward (r := r) E a F) v.1).re =
      (2 : ℝ) ^ n * ∫ z,
        (∑ α, ∑ β, star (F z α) * BundleDbar.metricMatrix (r := r) E h a z α β *
          coefficients (r := r) E v.1 a z Fin.elim0 β).re * Real.exp (-φ (chartInv a z)) ∂lebesgueC n := by
  classical
  let u := topFormPushforward (r := r) E a F
  let P := weightedTopPairing E g.form h φ u v.1
  let Q := fun z =>
    (∑ α, ∑ β, star (F z α) * BundleDbar.metricMatrix (r := r) E h a z α β *
      coefficients (r := r) E v.1 a z Fin.elim0 β).re * Real.exp (-φ (chartInv a z))
  have hu : WeightedL2 (r := r) E g.form h μ φ u :=
    topFormPushforward_weightedL2 E g μ hμ h hh φ hφ hE a F hF hc hs
  have hP : Integrable P μ := weightedTopPairing_integrable E g μ hμ h hh φ hφ u v.1 hu v.2
  have hPzero (x : M.Carrier) (hx : x ∉ bundleChartSource (r := r) E a) : P x = 0 := by
    apply weightedTopPairing_eq_zero_of_left_zero E g.form h φ u v.1 x
    change (if hy : x ∈ bundleChartSource (r := r) E a then
      (topTensorCoordinatesEquiv (r := r) E a x hy).symm (F (chartPt a x))
      else (0 : antiComplexSubmodule E x 0)) = (0 : antiComplexSubmodule E x 0)
    exact dif_neg hx
  have hFrestrict (z : ComplexVector n) (hz : z ∉ localDomain (r := r) E a) : F z = 0 := by
    by_contra hn
    exact hz (hs (subset_tsupport F hn))
  have hQzero (z : ComplexVector n) (hz : z ∉ chartTarget a) : Q z = 0 := by
    have hFzero := hFrestrict z (fun h => hz h.1)
    dsimp only [Q]
    rw [hFzero]
    simp only [PiLp.zero_apply, star_zero, zero_mul, Finset.sum_const_zero, Complex.zero_re]
  have hlocal (z : ComplexVector n) (hz : z ∈ chartTarget a) :
      Real.sqrt (realMetricFn g.form a z).det * (P (chartInv a z)).re = (2 : ℝ) ^ n * Q z := by
    by_cases hzo : z ∈ localDomain (r := r) E a
    · have he := topFormPairing_re_inChart E g.form h u v.1 a z hzo
      have hcf : coefficients (r := r) E u a z Fin.elim0 = F z :=
        topFormPushforward_coefficients E a F z hzo
      rw [hcf] at he
      change Real.sqrt (realMetricFn g.form a z).det *
        (topFormPairing E g.form h u v.1 (chartInv a z) * (Real.exp (-φ (chartInv a z)) : ℂ)).re = _
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
      rw [he, realMetricFn_sqrt_det g.form a z hz]
      dsimp only [Q]
      have hd : (hMat g.form a z).det.re ≠ 0 := ne_of_gt (L18Aux.hMat_det_re_pos g.form a hz)
      field_simp [hd] <;> ring
    · have hout : chartInv a z ∉ bundleChartSource (r := r) E a := fun hy => hzo ⟨hz, hy.2⟩
      rw [hPzero (chartInv a z) hout]
      dsimp only [Q]
      rw [hFrestrict z hzo]
      simp only [Complex.zero_re, mul_zero, PiLp.zero_apply, star_zero, zero_mul, Finset.sum_const_zero]
  have hm : AEStronglyMeasurable (fun x => (P x).re)
      (μ.restrict (extChartAt (ComplexModel n) a).source) :=
    hP.re.aestronglyMeasurable.mono_measure Measure.restrict_le_self
  have hrestrict : (∫ x in (extChartAt (ComplexModel n) a).source, (P x).re ∂μ) =
      ∫ x, (P x).re ∂μ :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
      rw [hPzero x (fun hy => hx hy.1)]
      rfl)
  calc
    _ = ∫ x, (P x).re ∂μ := by
      change (∫ x, P x ∂μ).re = _
      simpa only [RCLike.re_eq_complex_re] using (integral_re (𝕜 := ℂ) hP).symm
    _ = ∫ x in (extChartAt (ComplexModel n) a).source, (P x).re ∂μ := hrestrict.symm
    _ = ∫ z in chartTarget a, Real.sqrt (realMetricFn g.form a z).det * (P (chartInv a z)).re ∂lebesgueC n := by
      simpa only [smul_eq_mul] using L18Aux.integral_chart_volume_ae g μ hμ a hm
    _ = ∫ z in chartTarget a, (2 : ℝ) ^ n * Q z ∂lebesgueC n :=
      setIntegral_congr_fun (isOpen_extChartAt_target (I := ComplexModel n) a).measurableSet hlocal
    _ = (2 : ℝ) ^ n * ∫ z in chartTarget a, Q z ∂lebesgueC n := integral_const_mul _ _
    _ = _ := congrArg (fun t : ℝ => (2 : ℝ) ^ n * t)
      (setIntegral_eq_integral_of_forall_compl_eq_zero hQzero)

end Yau.LeafProofs.L14Aux

namespace Yau.LeafProofs.L14Aux

open BundleDbar Filter

def scalarTopTest {n r : ℕ} (α : Fin r) (c : ℂ) (ψ : ComplexVector n → ℝ) (z : ComplexVector n) :
    ComplexVector r := (c * (ψ z : ℂ)) • stdVec α

theorem scalarTopTest_properties {n r : ℕ} (α : Fin r) (c : ℂ) (ψ : ComplexVector n → ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ) :
    ContDiff ℝ ∞ (scalarTopTest α c ψ) ∧ HasCompactSupport (scalarTopTest α c ψ) ∧
      tsupport (scalarTopTest α c ψ) ⊆ tsupport ψ := by
  let f : ℝ → ComplexVector r := fun t => (c * (t : ℂ)) • stdVec α
  have hf0 : f 0 = 0 := by simp [f]
  have hscalar : ContDiff ℝ ∞ (fun z => c * (ψ z : ℂ)) :=
    contDiff_const.mul (Complex.ofRealCLM.contDiff.comp hψ)
  have hd : ContDiff ℝ ∞ (f ∘ ψ) := hscalar.smul contDiff_const
  change ContDiff ℝ ∞ (f ∘ ψ) ∧ HasCompactSupport (f ∘ ψ) ∧ tsupport (f ∘ ψ) ⊆ tsupport ψ
  exact ⟨hd, hc.comp_left hf0, tsupport_comp_subset hf0 ψ⟩

variable {n r : ℕ} {M : ComplexManifold n}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

def weightedTopDualCoefficient (h : Metric E) (φ : M.Carrier → ℝ) (u : NQForm E 0)
    (a : M.Carrier) (z : ComplexVector n) (α : Fin r) : ℂ :=
  (∑ β, BundleDbar.metricMatrix (r := r) E h a z α β *
    coefficients (r := r) E u a z Fin.elim0 β) * (Real.exp (-φ (chartInv a z)) : ℂ)

theorem weightedTopDualCoefficient_locallyIntegrableOn
    (h : Metric E) (hh : BundleDbar.SmoothMetric (r := r) E h)
    (φ : M.Carrier → ℝ) (hφ : SmoothFn φ) (u : NQForm E 0) (hu : LocallyL2 (r := r) E u)
    (a : M.Carrier) (α : Fin r) :
    LocallyIntegrableOn (fun z => weightedTopDualCoefficient (r := r) E h φ u a z α)
      (localDomain (r := r) E a) (lebesgueC n) := by
  let O := localDomain (r := r) E a
  have hterm (β : Fin r) : LocallyIntegrableOn (fun z => BundleDbar.metricMatrix (r := r) E h a z α β *
      coefficients (r := r) E u a z Fin.elim0 β) O (lebesgueC n) :=
    (locallyL2_coefficients_locallyIntegrableOn E u hu a Fin.elim0 β).continuousOn_mul
      (hh a α β).continuousOn (localDomain_isOpen E a).isLocallyClosed
  have hsum : LocallyIntegrableOn (fun z => ∑ β, BundleDbar.metricMatrix (r := r) E h a z α β *
      coefficients (r := r) E u a z Fin.elim0 β) O (lebesgueC n) := by
    apply (locallyIntegrableOn_iff (localDomain_isOpen E a).isLocallyClosed).mpr
    intro K hsub hK
    apply integrable_finset_sum
    intro β _
    exact (hterm β).integrableOn_compact_subset hsub hK
  have hρR : ContinuousOn (fun z => Real.exp (-φ (chartInv a z))) O :=
    Real.continuous_exp.comp_continuousOn (((hφ a).continuousOn.neg).mono Set.inter_subset_left)
  have hρ : ContinuousOn (fun z => (Real.exp (-φ (chartInv a z)) : ℂ)) O :=
    Complex.continuous_ofReal.comp_continuousOn hρR
  exact hsum.mul_continuousOn hρ (localDomain_isOpen E a).isLocallyClosed

variable (g : Yau.SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
  (h : Metric E) (hh : BundleDbar.SmoothMetric (r := r) E h) (φ : M.Carrier → ℝ) (hφ : SmoothFn φ)
  (hE : Holomorphic (r := r) E)

include hE

set_option backward.isDefEq.respectTransparency false in
theorem weightedTopInner_scalarTopTest_re
    (a : M.Carrier) (α : Fin r) (c : ℂ) (ψ : ComplexVector n → ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ ⊆ localDomain (r := r) E a) (v : WeightedTopSection E g μ hμ h hh φ hφ) :
    (weightedTopInner E g.form μ h φ (topFormPushforward (r := r) E a (scalarTopTest α c ψ)) v.1).re =
      (2 : ℝ) ^ n * ∫ z, ψ z *
        (star c * weightedTopDualCoefficient (r := r) E h φ v.1 a z α).re ∂lebesgueC n := by
  obtain ⟨hF, hcF, hsF⟩ := scalarTopTest_properties α c ψ hψ hc
  rw [weightedTopInner_topFormPushforward_re E g μ hμ h hh φ hφ hE a (scalarTopTest α c ψ)
    hF hcF (hsF.trans hs) v]
  congr 1
  apply integral_congr_ae
  apply Eventually.of_forall
  intro z
  change (∑ p, ∑ β, star (scalarTopTest α c ψ z p) *
      BundleDbar.metricMatrix (r := r) E h a z p β * coefficients (r := r) E v.1 a z Fin.elim0 β).re *
        Real.exp (-φ (chartInv a z)) =
    ψ z * (star c * weightedTopDualCoefficient (r := r) E h φ v.1 a z α).re
  have hrow (p : Fin r) : star (scalarTopTest α c ψ z p) =
      if p = α then star (c * (ψ z : ℂ)) else 0 := by
    by_cases hp : p = α
    · subst p
      simp [scalarTopTest, stdVec, PiLp.single_apply, Pi.single_apply]
    · simp [scalarTopTest, stdVec, PiLp.single_apply, Pi.single_apply, hp]
  have hsum : (∑ p, ∑ β, star (scalarTopTest α c ψ z p) *
      BundleDbar.metricMatrix (r := r) E h a z p β * coefficients (r := r) E v.1 a z Fin.elim0 β) =
      star (c * (ψ z : ℂ)) * ∑ β, BundleDbar.metricMatrix (r := r) E h a z α β *
        coefficients (r := r) E v.1 a z Fin.elim0 β := by
    calc
      _ = ∑ p, if p = α then ∑ β, star (c * (ψ z : ℂ)) *
          BundleDbar.metricMatrix (r := r) E h a z p β * coefficients (r := r) E v.1 a z Fin.elim0 β else 0 := by
        apply Finset.sum_congr rfl
        intro p _
        by_cases hp : p = α
        · simp only [hrow, hp, ite_true]
        · simp only [hrow, hp, ite_false, zero_mul, Finset.sum_const_zero]
      _ = ∑ β, star (c * (ψ z : ℂ)) * BundleDbar.metricMatrix (r := r) E h a z α β *
          coefficients (r := r) E v.1 a z Fin.elim0 β := by simp
      _ = _ := by simp only [Finset.mul_sum, mul_assoc]
  calc
    _ = (star (c * (ψ z : ℂ)) * ∑ β, BundleDbar.metricMatrix (r := r) E h a z α β *
        coefficients (r := r) E v.1 a z Fin.elim0 β).re * Real.exp (-φ (chartInv a z)) :=
      congrArg (fun t : ℂ => t.re * Real.exp (-φ (chartInv a z))) hsum
    _ = _ := by
      unfold weightedTopDualCoefficient
      simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.star_def, Complex.conj_re, Complex.conj_im]
      ring

end Yau.LeafProofs.L14Aux

namespace Yau.LeafProofs.L14Aux

open BundleDbar Filter

variable {n r : ℕ} {M : ComplexManifold n}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

theorem topForm_ae_zero_of_coefficients_ae_zero (g : HermitianField M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g μ) (u : NQForm E 0)
    (hu : ∀ a α, (fun z => coefficients (r := r) E u a z Fin.elim0 α) =ᵐ[
      (lebesgueC n).restrict (localDomain (r := r) E a)] 0) :
    ∀ᵐ x ∂μ, u x = (0 : NQForm E 0) x := by
  apply ae_of_bundleCharts (r := r) E g μ hμ _
  intro a
  have hall : ∀ᵐ z ∂(lebesgueC n).restrict (localDomain (r := r) E a),
      ∀ α, coefficients (r := r) E u a z Fin.elim0 α = 0 := ae_all_iff.mpr (hu a)
  filter_upwards [hall, ae_restrict_mem (localDomain_isOpen E a).measurableSet] with z hz hzo
  let hx : chartInv a z ∈ bundleChartSource (r := r) E a :=
    ⟨(extChartAt (ComplexModel n) a).map_target hzo.1, hzo.2⟩
  let L := topTensorCoordinatesEquiv (r := r) E a (chartInv a z) hx
  change (u (chartInv a z) : antiComplexSubmodule E (chartInv a z) 0) =
    (0 : antiComplexSubmodule E (chartInv a z) 0)
  apply L.injective
  have hcoord : L (u (chartInv a z)) = coefficients (r := r) E u a z Fin.elim0 :=
    topTensorCoordinatesEquiv_form E u a z hzo
  have hc : coefficients (r := r) E u a z Fin.elim0 = 0 := by
    ext α
    exact hz α
  exact hcoord.trans (hc.trans (map_zero L).symm)

theorem coefficients_ae_zero_of_weightedTopDual_ae_zero
    (h : Metric E) (φ : M.Carrier → ℝ) (u : NQForm E 0) (a : M.Carrier)
    (hu : ∀ α, (fun z => weightedTopDualCoefficient (r := r) E h φ u a z α) =ᵐ[
      (lebesgueC n).restrict (localDomain (r := r) E a)] 0) (α : Fin r) :
    (fun z => coefficients (r := r) E u a z Fin.elim0 α) =ᵐ[
      (lebesgueC n).restrict (localDomain (r := r) E a)] 0 := by
  have hall : ∀ᵐ z ∂(lebesgueC n).restrict (localDomain (r := r) E a),
      ∀ β, weightedTopDualCoefficient (r := r) E h φ u a z β = 0 := ae_all_iff.mpr hu
  filter_upwards [hall, ae_restrict_mem (localDomain_isOpen E a).measurableSet] with z hz hzo
  let H := BundleDbar.metricMatrix (r := r) E h a z
  let U := fun β => coefficients (r := r) E u a z Fin.elim0 β
  have hρ : (Real.exp (-φ (chartInv a z)) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.exp_pos _))
  have hzero : H *ᵥ U = 0 := by
    funext β
    have he := hz β
    change ((∑ γ, H β γ * U γ) * (Real.exp (-φ (chartInv a z)) : ℂ)) = 0 at he
    exact (mul_eq_zero.mp he).resolve_right hρ
  have hH : H.PosDef := metricMatrix_posDef (r := r) E h a z hzo
  have he := congrArg (fun W : Fin r → ℂ => H⁻¹ *ᵥ W) hzero
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (hH.isUnit.map Matrix.detMonoidHom),
    Matrix.one_mulVec, Matrix.mulVec_zero] at he
  exact congrFun he α

end Yau.LeafProofs.L14Aux

namespace Yau.LeafProofs.L14Aux

open BundleDbar Filter

variable {n r : ℕ} {M : ComplexManifold n}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]
variable (g : Yau.SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
  (h : Metric E) (hh : BundleDbar.SmoothMetric (r := r) E h) (φ : M.Carrier → ℝ) (hφ : SmoothFn φ)
  (hE : Holomorphic (r := r) E)

include hE

theorem weightedMaximalDbar_domain_orthogonal_eq_bot :
    (weightedMaximalDbar E g μ hμ h hh φ hφ).domainᗮ = ⊥ := by
  let D := (weightedMaximalDbar E g μ hμ h hh φ hφ).domain
  apply (Submodule.eq_bot_iff _).mpr
  intro v hv
  let V := weightedTopHilbertRepresentative E g μ hμ h hh φ hφ v
  have hVreal : realizeWeightedTopSection E g μ hμ h hh φ hφ V = v :=
    weightedTopHilbertRepresentative_realize E g μ hμ h hh φ hφ v
  have hdual (a : M.Carrier) (α : Fin r) :
      (fun z => weightedTopDualCoefficient (r := r) E h φ V.1 a z α) =ᵐ[
        (lebesgueC n).restrict (localDomain (r := r) E a)] 0 := by
    let O := localDomain (r := r) E a
    let W := fun z => weightedTopDualCoefficient (r := r) E h φ V.1 a z α
    have hW : LocallyIntegrableOn W O (lebesgueC n) :=
      weightedTopDualCoefficient_locallyIntegrableOn E h hh φ hφ V.1 V.2.1 a α
    have htest (c : ℂ) (ψ : ComplexVector n → ℝ) (hψ : ContDiff ℝ ∞ ψ)
        (hc : HasCompactSupport ψ) (hs : tsupport ψ ⊆ O) :
        (∫ z, ψ z * (star c * W z).re ∂lebesgueC n) = 0 := by
      obtain ⟨hF, hcF, hsF⟩ := scalarTopTest_properties α c ψ hψ hc
      let U := weightedTopChartSection E g μ hμ h hh φ hφ hE a (scalarTopTest α c ψ)
        hF hcF (hsF.trans hs)
      have hDom : realizeWeightedTopSection E g μ hμ h hh φ hφ U ∈ D :=
        weightedTopChartSection_mem_domain E g μ hμ h hh φ hφ hE a (scalarTopTest α c ψ)
          hF hcF (hsF.trans hs)
      have hi : inner ℂ (realizeWeightedTopSection E g μ hμ h hh φ hφ U) v = 0 :=
        (D.mem_orthogonal v).mp hv _ hDom
      have hi' : inner ℂ (realizeWeightedTopSection E g μ hμ h hh φ hφ U)
          (realizeWeightedTopSection E g μ hμ h hh φ hφ V) = 0 := by
        rw [hVreal]
        exact hi
      have hphys : weightedTopInner E g.form μ h φ
          (topFormPushforward (r := r) E a (scalarTopTest α c ψ)) V.1 = 0 :=
        (realizeWeightedTopSection_inner E g μ hμ h hh φ hφ U V).symm.trans hi'
      have hformula := weightedTopInner_scalarTopTest_re E g μ hμ h hh φ hφ hE
        a α c ψ hψ hc hs V
      have hprod : (2 : ℝ) ^ n * (∫ z, ψ z * (star c * W z).re ∂lebesgueC n) = 0 :=
        hformula.symm.trans (congrArg Complex.re hphys)
      exact (mul_eq_zero.mp hprod).resolve_left (ne_of_gt (pow_pos (by norm_num : (0 : ℝ) < 2) n))
    have hWR : LocallyIntegrableOn (fun z => (W z).re) O (lebesgueC n) :=
      Complex.reCLM.locallyIntegrableOn_comp hW
    have hWI : LocallyIntegrableOn (fun z => (W z).im) O (lebesgueC n) :=
      Complex.imCLM.locallyIntegrableOn_comp hW
    have hR : ∀ᵐ z ∂lebesgueC n, z ∈ O → (W z).re = 0 :=
      (localDomain_isOpen E a).ae_eq_zero_of_integral_contDiff_smul_eq_zero hWR
        (fun ψ hψ hc hs => by
          simpa only [star_one, one_mul, smul_eq_mul] using htest 1 ψ hψ hc hs)
    have hI : ∀ᵐ z ∂lebesgueC n, z ∈ O → (W z).im = 0 :=
      (localDomain_isOpen E a).ae_eq_zero_of_integral_contDiff_smul_eq_zero hWI
        (fun ψ hψ hc hs => by
          simpa only [Complex.star_def, Complex.conj_I, Complex.mul_re, Complex.neg_re,
            Complex.neg_im, Complex.I_re, Complex.I_im, neg_zero, zero_mul, neg_mul,
            one_mul, zero_sub, neg_neg, smul_eq_mul] using htest Complex.I ψ hψ hc hs)
    apply (ae_restrict_iff' (localDomain_isOpen E a).measurableSet).mpr
    filter_upwards [hR, hI] with z hzR hzI
    intro hzo
    exact Complex.ext (hzR hzo) (hzI hzo)
  have hcoeff (a : M.Carrier) (α : Fin r) :
      (fun z => coefficients (r := r) E V.1 a z Fin.elim0 α) =ᵐ[
        (lebesgueC n).restrict (localDomain (r := r) E a)] 0 :=
    coefficients_ae_zero_of_weightedTopDual_ae_zero E h φ V.1 a (hdual a) α
  have hVae : ∀ᵐ x ∂μ, V.1 x = (0 : NQForm E 0) x :=
    topForm_ae_zero_of_coefficients_ae_zero E g.form μ hμ V.1 hcoeff
  have hn : ‖V‖ = 0 := (weightedTopSection_norm_eq_zero_iff E g μ hμ h hh φ hφ V).mpr hVae
  have hvnorm : ‖v‖ = 0 := by
    rw [← hVreal]
    change ‖(V : UniformSpace.Completion (WeightedTopSection E g μ hμ h hh φ hφ))‖ = 0
    rw [UniformSpace.Completion.norm_coe, hn]
  exact norm_eq_zero.mp hvnorm

theorem weightedMaximalDbar_domain_dense :
    Dense ((weightedMaximalDbar E g μ hμ h hh φ hφ).domain :
      Set (WeightedTopHilbert E g μ hμ h hh φ hφ)) := by
  let D := (weightedMaximalDbar E g μ hμ h hh φ hφ).domain
  have hz : Dᗮ = ⊥ := weightedMaximalDbar_domain_orthogonal_eq_bot E g μ hμ h hh φ hφ hE
  have hclosure : D.topologicalClosure = ⊤ := by
    rw [← D.orthogonal_orthogonal_eq_closure, hz, Submodule.bot_orthogonal_eq_top]
  apply dense_iff_closure_eq.mpr
  change (D.topologicalClosure : Set (WeightedTopHilbert E g μ hμ h hh φ hφ)) = Set.univ
  rw [hclosure]
  rfl

end Yau.LeafProofs.L14Aux

namespace Yau.LeafProofs.L14Aux

open BundleDbar Filter

variable {n r : ℕ} {M : ComplexManifold n}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

theorem oneFormPushforward_smooth (hE : Holomorphic (r := r) E)
    (a : M.Carrier) (F : ComplexVector n → Fin n → ComplexVector r)
    (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    (hs : tsupport F ⊆ localDomain (r := r) E a) :
    SmoothForm (r := r) E (oneFormPushforward (r := r) E a F) := by
  classical
  intro b I α z hz
  let j := I 0
  have hI : I = fun _ => j := funext fun k => congrArg I (Subsingleton.elim k 0)
  rw [hI]
  have hi : ContinuousAt (chartInv b) z := continuousAt_extChartAt_symm'' (I := ComplexModel n) hz.1
  by_cases hya : chartInv b z ∈ bundleChartSource (r := r) E a
  · let T := fun w => chartPt a (chartInv b w)
    have hT := L18Aux.chartTransition_contDiffAt b a hz.1 hya.1
    have hD : ContDiffAt ℂ ∞ (fderiv ℂ T) z := hT.fderiv_right (m := ∞) (by simp)
    have hJ (i : Fin n) : ContDiffAt ℝ ∞
        (fun t => star (fderiv ℂ T t (stdVec j) i)) z := by
      have hv : ContDiffAt ℂ ∞ (fun t => fderiv ℂ T t (stdVec j)) z :=
        hD.clm_apply contDiffAt_const
      exact Complex.conjCLE.contDiff.contDiffAt.comp z
        (((contDiffAt_piLp 2).mp hv i).restrict_scalars ℝ)
    have hV : ContDiffAt ℝ ∞
        (fun t => ∑ i, star (fderiv ℂ T t (stdVec j) i) • F (T t) i) z :=
      ContDiffAt.sum fun i _ => (hJ i).smul
        (((contDiff_pi.mp hF) i).contDiffAt.comp z (hT.restrict_scalars ℝ))
    have hC := (topBundleTransition_contDiffAt E hE a b z hz hya).restrict_scalars ℝ
    have hCR : ContDiffAt ℝ ∞ (fun t => (topBundleTransition (r := r) E a b t).restrictScalars ℝ) z :=
      (ContinuousLinearMap.restrictScalarsL ℂ (ComplexVector r) (ComplexVector r) ℝ ℝ).contDiff.contDiffAt.comp z hC
    have hm := (contDiffAt_piLp 2).mp (hCR.clm_apply hV) α
    have heq : (fun t => coefficients (r := r) E (oneFormPushforward (r := r) E a F) b t (fun _ => j) α) =ᶠ[𝓝 z]
        (fun t => topBundleTransition (r := r) E a b t
          (∑ i, star (fderiv ℂ T t (stdVec j) i) • F (T t) i) α) := by
      filter_upwards [(localDomain_isOpen E b).mem_nhds hz,
        hi.tendsto.eventually ((bundleChartSource_isOpen (r := r) E a).mem_nhds hya)] with t htb hta
      exact congrArg (fun v : ComplexVector r => v α)
        (oneFormPushforward_coefficients_inChart E a b F t htb hta j)
    exact (hm.congr_of_eventuallyEq heq).contDiffWithinAt
  · let u := oneFormPushforward (r := r) E a F
    let K := closure {x | u x ≠ (0 : NQForm E 1) x}
    have hsource : K ⊆ bundleChartSource (r := r) E a := by
      intro x hx
      obtain ⟨w, hw, rfl⟩ := oneFormPushforward_support E a F hc hs hx
      exact ⟨(extChartAt (ComplexModel n) a).map_target (hs hw).1, (hs hw).2⟩
    have hout : chartInv b z ∉ K := fun h => hya (hsource h)
    have hzero : ∀ᶠ y in 𝓝 (chartInv b z), u y = (0 : NQForm E 1) y := by
      filter_upwards [isClosed_closure.compl_mem_nhds hout] with y hy
      by_contra hn
      exact hy (subset_closure hn)
    have heq : (fun t => coefficients (r := r) E u b t (fun _ => j) α) =ᶠ[𝓝 z] (fun _ => 0) := by
      filter_upwards [hi.tendsto.eventually hzero] with t ht
      have hcoeff : coefficients (r := r) E u b t (fun _ => j) α =
          coefficients (r := r) E (0 : NQForm E 1) b t (fun _ => j) α := by
        unfold coefficients
        rw [ht]
      exact hcoeff.trans (coefficients_zero E b t (fun _ => j) α)
    have hm : ContDiffAt ℝ ∞ (fun _ : ComplexVector n => (0 : ℂ)) z := contDiffAt_const
    exact (hm.congr_of_eventuallyEq heq).contDiffWithinAt

theorem oneFormPushforward_weightedL2 (g : Yau.SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (h : Metric E) (hh : BundleDbar.SmoothMetric (r := r) E h)
    (φ : M.Carrier → ℝ) (hφ : SmoothFn φ) (hE : Holomorphic (r := r) E)
    (a : M.Carrier) (F : ComplexVector n → Fin n → ComplexVector r)
    (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    (hs : tsupport F ⊆ localDomain (r := r) E a) :
    WeightedL2 (r := r) E g.form h μ φ (oneFormPushforward (r := r) E a F) := by
  have hK : IsCompact (chartInv a '' tsupport F) := hc.image_of_continuousOn
    ((continuousOn_extChartAt_symm (I := ComplexModel n) a).mono (hs.trans Set.inter_subset_left))
  exact smooth_compact_weightedL2_one E g μ hμ h hh φ hφ _
    (oneFormPushforward_smooth E hE a F hF hc hs)
    (hK.of_isClosed_subset isClosed_closure (oneFormPushforward_support E a F hc hs))

end Yau.LeafProofs.L14Aux

namespace Yau.LeafProofs.L14Aux

open BundleDbar Filter

variable {n r : ℕ} {M : ComplexManifold n}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

theorem topFormPairing_inChart (g : HermitianField M) (h : Metric E)
    (u v : NQForm E 0) (a : M.Carrier) (z : ComplexVector n)
    (hz : z ∈ localDomain (r := r) E a) :
    topFormPairing E g h u v (chartInv a z) =
      ((((hMat g a z).det.re)⁻¹ : ℝ) : ℂ) *
        (∑ α, ∑ β, star (coefficients (r := r) E u a z Fin.elim0 α) *
          BundleDbar.metricMatrix (r := r) E h a z α β *
            coefficients (r := r) E v a z Fin.elim0 β) := by
  let C := ∑ α, ∑ β, star (coefficients (r := r) E u a z Fin.elim0 α) *
    BundleDbar.metricMatrix (r := r) E h a z α β * coefficients (r := r) E v a z Fin.elim0 β
  have hscale : (∑ α, ∑ β, star (coefficients (r := r) E u a z Fin.elim0 α) *
      BundleDbar.metricMatrix (r := r) E h a z α β *
        coefficients (r := r) E (Complex.I • v) a z Fin.elim0 β) = Complex.I * C := by
    simp only [coefficients_smul, C, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro α _
    apply Finset.sum_congr rfl
    intro β _
    ring
  have hR := topFormPairing_re_inChart E g h u v a z hz
  have hI := topFormPairing_re_inChart E g h u (Complex.I • v) a z hz
  rw [topFormPairing_smul_right, hscale, Complex.I_mul_re, Complex.I_mul_re] at hI
  apply Complex.ext
  · simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] using hR
  · simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
    dsimp only [C] at hI
    linarith

theorem integral_of_compact_chart_density
    (g : Yau.SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (a : M.Carrier) (P : M.Carrier → ℂ) (Q : ComplexVector n → ℂ)
    (hP : Integrable P μ)
    (hPzero : ∀ x, x ∉ (extChartAt (ComplexModel n) a).source → P x = 0)
    (hQzero : ∀ z, z ∉ chartTarget a → Q z = 0)
    (hlocal : ∀ z ∈ chartTarget a,
      Real.sqrt (realMetricFn g.form a z).det • P (chartInv a z) = (2 : ℝ) ^ n • Q z) :
    (∫ x, P x ∂μ) = (2 : ℝ) ^ n • ∫ z, Q z ∂lebesgueC n := by
  have hm := hP.aestronglyMeasurable.mono_measure
    (Measure.restrict_le_self (s := (extChartAt (ComplexModel n) a).source))
  calc
    _ = ∫ x in (extChartAt (ComplexModel n) a).source, P x ∂μ :=
      (setIntegral_eq_integral_of_forall_compl_eq_zero hPzero).symm
    _ = ∫ z in chartTarget a, Real.sqrt (realMetricFn g.form a z).det • P (chartInv a z) ∂lebesgueC n :=
      L18Aux.integral_chart_volume_ae g μ hμ a hm
    _ = ∫ z in chartTarget a, (2 : ℝ) ^ n • Q z ∂lebesgueC n :=
      setIntegral_congr_fun (isOpen_extChartAt_target (I := ComplexModel n) a).measurableSet hlocal
    _ = (2 : ℝ) ^ n • ∫ z in chartTarget a, Q z ∂lebesgueC n := integral_smul _ _
    _ = _ := congrArg (fun w : ℂ => (2 : ℝ) ^ n • w)
      (setIntegral_eq_integral_of_forall_compl_eq_zero hQzero)

theorem weightedOnePairing_eq_zero_of_right_zero (g : HermitianField M) (h : Metric E)
    (φ : M.Carrier → ℝ) (u v : NQForm E 1) (x : M.Carrier)
    (hx : v x = (0 : NQForm E 1) x) : weightedOnePairing E g h φ u v x = 0 := by
  have he : oneFormPairing E g h u v x = oneFormPairing E g h u (0 : NQForm E 1) x := by
    unfold oneFormPairing
    rw [hx]
  have hz : oneFormPairing E g h u (0 : NQForm E 1) x = 0 := by
    simpa only [zero_smul, zero_mul] using
      (oneFormPairing_smul_right E g h (0 : ℂ) u (0 : NQForm E 1) x)
  simp only [weightedOnePairing, he, hz, zero_mul]

end Yau.LeafProofs.L14Aux

namespace Yau.LeafProofs.L14Aux

open BundleDbar Filter

theorem wirtBar_star {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (f : X → ℂ) (z v : X) :
    wirtBar (fun y => star (f y)) z v = star (wirt f z v) := by
  unfold wirtBar wirt
  rw [fderiv_star]
  simp [star_mul, star_sub, Complex.star_def]
  ring

theorem tsupport_wirt_subset {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (f : X → ℂ) (v : X) : tsupport (fun z => wirt f z v) ⊆ tsupport f := by
  apply closure_minimal _ (isClosed_tsupport f)
  intro z hz
  by_contra hn
  have hd : fderiv ℝ f z = 0 := fderiv_of_notMem_tsupport (𝕜 := ℝ) hn
  exact hz (by simp only [wirt, hd, ContinuousLinearMap.zero_apply, mul_zero, sub_zero])

theorem contDiff_of_contDiffOn_of_tsupport_subset {n : ℕ}
    {O : Set (ComplexVector n)} (hO : IsOpen O) (f : ComplexVector n → ℂ)
    (hf : ContDiffOn ℝ ∞ f O) (hs : tsupport f ⊆ O) : ContDiff ℝ ∞ f := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z ∈ O
  · exact hf.contDiffAt (hO.mem_nhds hz)
  · have hout : z ∉ tsupport f := fun h => hz (hs h)
    have heq : f =ᶠ[𝓝 z] (fun _ => 0) := by
      filter_upwards [(isClosed_tsupport f).isOpen_compl.mem_nhds hout] with y hy
      exact image_eq_zero_of_notMem_tsupport hy
    exact contDiffAt_const.congr_of_eventuallyEq heq

variable {n r : ℕ} {M : ComplexManifold n}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

def chartOneDual (g : HermitianField M) (h : Metric E) (φ : M.Carrier → ℝ)
    (a : M.Carrier) (F : ComplexVector n → Fin n → ComplexVector r)
    (z : ComplexVector n) (i : Fin n) (α : Fin r) : ℂ :=
  (Real.exp (-φ (chartInv a z)) : ℂ) * ∑ j, (hMat g a z)⁻¹ i j *
    ∑ β, BundleDbar.metricMatrix (r := r) E h a z α β * F z j β

theorem tsupport_chartOneDual_subset (g : HermitianField M) (h : Metric E)
    (φ : M.Carrier → ℝ) (a : M.Carrier) (F : ComplexVector n → Fin n → ComplexVector r)
    (i : Fin n) (α : Fin r) :
    tsupport (fun z => chartOneDual (r := r) E g h φ a F z i α) ⊆ tsupport F := by
  apply closure_minimal _ (isClosed_tsupport F)
  intro z hz
  by_contra hn
  have hF : F z = 0 := image_eq_zero_of_notMem_tsupport hn
  exact hz (by simp only [chartOneDual, hF, Pi.zero_apply, PiLp.zero_apply,
    mul_zero, Finset.sum_const_zero])

theorem chartOneDual_contDiff (g : Yau.SmoothMetric M) (h : Metric E)
    (hh : BundleDbar.SmoothMetric (r := r) E h) (φ : M.Carrier → ℝ) (hφ : SmoothFn φ)
    (a : M.Carrier) (F : ComplexVector n → Fin n → ComplexVector r)
    (hF : ContDiff ℝ ∞ F) (hs : tsupport F ⊆ localDomain (r := r) E a)
    (i : Fin n) (α : Fin r) :
    ContDiff ℝ ∞ (fun z => chartOneDual (r := r) E g.form h φ a F z i α) := by
  apply contDiff_of_contDiffOn_of_tsupport_subset (localDomain_isOpen E a) _ _
    ((tsupport_chartOneDual_subset E g.form h φ a F i α).trans hs)
  have hρ : ContDiffOn ℝ ∞ (fun z => (Real.exp (-φ (chartInv a z)) : ℂ))
      (localDomain (r := r) E a) :=
    (((hφ a).neg.exp).continuousLinearMap_comp Complex.ofRealCLM).mono Set.inter_subset_left
  apply hρ.mul
  apply ContDiffOn.sum
  intro j _
  apply ((L18Aux.hMat_inverse_contDiffOn g a i j).mono Set.inter_subset_left).mul
  apply ContDiffOn.sum
  intro β _
  exact (hh a α β).mul (((contDiff_piLp 2).mp ((contDiff_pi.mp hF) j) β).contDiffOn)

def chartDbarAdjoint (g : HermitianField M) (h : Metric E) (φ : M.Carrier → ℝ)
    (a : M.Carrier) (F : ComplexVector n → Fin n → ComplexVector r)
    (z : ComplexVector n) : ComplexVector r :=
  WithLp.toLp 2 (fun α => -(Real.exp (φ (chartInv a z)) : ℂ) *
    ∑ β, (BundleDbar.metricMatrix (r := r) E h a z)⁻¹ α β *
      ∑ i, wirt (fun y => chartOneDual (r := r) E g h φ a F y i β) z (stdVec i))

theorem tsupport_chartDbarAdjoint_subset (g : HermitianField M) (h : Metric E)
    (φ : M.Carrier → ℝ) (a : M.Carrier) (F : ComplexVector n → Fin n → ComplexVector r) :
    tsupport (chartDbarAdjoint (r := r) E g h φ a F) ⊆ tsupport F := by
  apply closure_minimal _ (isClosed_tsupport F)
  intro z hz
  by_contra hn
  apply hz
  ext α
  change -(Real.exp (φ (chartInv a z)) : ℂ) * ∑ β, _ = 0
  have hd (β : Fin r) (i : Fin n) :
      wirt (fun y => chartOneDual (r := r) E g h φ a F y i β) z (stdVec i) = 0 := by
    have hz' : z ∉ tsupport (fun y =>
        wirt (fun w => chartOneDual (r := r) E g h φ a F w i β) y (stdVec i)) := by
      intro hw
      exact hn (tsupport_chartOneDual_subset E g h φ a F i β
        (tsupport_wirt_subset _ (stdVec i) hw))
    exact image_eq_zero_of_notMem_tsupport
      (f := fun y => wirt (fun w => chartOneDual (r := r) E g h φ a F w i β) y (stdVec i)) hz'
  simp only [hd, Finset.sum_const_zero, mul_zero]

theorem chartDbarAdjoint_contDiff (g : Yau.SmoothMetric M) (h : Metric E)
    (hh : BundleDbar.SmoothMetric (r := r) E h) (φ : M.Carrier → ℝ) (hφ : SmoothFn φ)
    (a : M.Carrier) (F : ComplexVector n → Fin n → ComplexVector r)
    (hF : ContDiff ℝ ∞ F) (hs : tsupport F ⊆ localDomain (r := r) E a) :
    ContDiff ℝ ∞ (chartDbarAdjoint (r := r) E g.form h φ a F) := by
  apply (contDiff_piLp 2).mpr
  intro α
  apply contDiff_of_contDiffOn_of_tsupport_subset (localDomain_isOpen E a) _ _
    ((tsupport_comp_subset (g := fun v : ComplexVector r => v α) (by rfl) _).trans
      ((tsupport_chartDbarAdjoint_subset E g.form h φ a F).trans hs))
  have hρ : ContDiffOn ℝ ∞ (fun z => (Real.exp (φ (chartInv a z)) : ℂ))
      (localDomain (r := r) E a) :=
    (((hφ a).exp).continuousLinearMap_comp Complex.ofRealCLM).mono Set.inter_subset_left
  have hdet : ∀ z ∈ localDomain (r := r) E a,
      (BundleDbar.metricMatrix (r := r) E h a z).det ≠ 0 := fun z hz =>
    ((metricMatrix_posDef E h a z hz).isUnit.map Matrix.detMonoidHom).ne_zero
  apply hρ.neg.mul
  apply ContDiffOn.sum
  intro β _
  apply (L18Aux.contDiffOn_matrix_inv (hh a) hdet α β).mul
  apply ContDiffOn.sum
  intro i _
  exact wirt_contDiffOn (localDomain_isOpen E a) _
    (chartOneDual_contDiff E g h hh φ hφ a F hF hs i β).contDiffOn (stdVec i)

end Yau.LeafProofs.L14Aux

namespace Yau.LeafProofs.L14Aux

open BundleDbar Filter

variable {n r : ℕ} {M : ComplexManifold n}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

theorem chartDbarAdjoint_dual (g : HermitianField M) (h : Metric E) (φ : M.Carrier → ℝ)
    (a : M.Carrier) (F : ComplexVector n → Fin n → ComplexVector r)
    (z : ComplexVector n) (hz : z ∈ localDomain (r := r) E a) (α : Fin r) :
    (∑ β, BundleDbar.metricMatrix (r := r) E h a z α β *
      chartDbarAdjoint (r := r) E g h φ a F z β) * (Real.exp (-φ (chartInv a z)) : ℂ) =
        -∑ i, wirt (fun y => chartOneDual (r := r) E g h φ a F y i α) z (stdVec i) := by
  let H := BundleDbar.metricMatrix (r := r) E h a z
  let L := fun β => ∑ i, wirt (fun y => chartOneDual (r := r) E g h φ a F y i β) z (stdVec i)
  let c : ℂ := Real.exp (φ (chartInv a z))
  have hc : (fun β => chartDbarAdjoint (r := r) E g h φ a F z β) = -c • (H⁻¹ *ᵥ L) := rfl
  have he := congrArg (fun V : Fin r → ℂ => (H *ᵥ V) α) hc
  rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv H ((metricMatrix_posDef E h a z hz).isUnit.map Matrix.detMonoidHom),
    Matrix.one_mulVec] at he
  change (H *ᵥ (fun β => chartDbarAdjoint (r := r) E g h φ a F z β)) α *
    (Real.exp (-φ (chartInv a z)) : ℂ) = -L α
  rw [he]
  change (-c * L α) * (Real.exp (-φ (chartInv a z)) : ℂ) = -L α
  have hρ : c * (Real.exp (-φ (chartInv a z)) : ℂ) = 1 := by
    dsimp only [c]
    rw [← Complex.ofReal_mul, ← Real.exp_add, add_neg_cancel, Real.exp_zero, Complex.ofReal_one]
  calc
    _ = -(c * (Real.exp (-φ (chartInv a z)) : ℂ)) * L α := by ring
    _ = _ := by rw [hρ]; ring

theorem locallyL2_conjugate_test_integrable {q : ℕ}
    (u : NQForm E q) (hu : LocallyL2 (r := r) E u)
    (a : M.Carrier) (I : Fin q → Fin n) (α : Fin r)
    (ψ : ComplexVector n → ℂ) (hψ : Continuous ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ ⊆ localDomain (r := r) E a) :
    Integrable (fun z => star (coefficients (r := r) E u a z I α) * ψ z) (lebesgueC n) := by
  have hp : IntegrableOn (fun z => star (coefficients (r := r) E u a z I α) * ψ z)
      (tsupport ψ) (lebesgueC n) :=
    test_mul_integrable_of_memLp ((lebesgueC n).restrict (tsupport ψ)) _ ψ
      (locallyL2_coefficients_memLp E u hu a I α (tsupport ψ) hc hs).star
      (compact_test_memLp ψ hψ hc (tsupport ψ))
  exact (integrableOn_iff_integrable_of_support_subset
    ((Function.support_mul_subset_right _ _).trans (subset_tsupport ψ))).mp hp

end Yau.LeafProofs.L14Aux

namespace Yau.LeafProofs.L14Aux

open BundleDbar Filter

variable {n r : ℕ} {M : ComplexManifold n}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]
variable (g : Yau.SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
  (h : Metric E) (hh : BundleDbar.SmoothMetric (r := r) E h) (φ : M.Carrier → ℝ) (hφ : SmoothFn φ)
  (hE : Holomorphic (r := r) E)

include hE

set_option backward.isDefEq.respectTransparency false in
theorem weightedTopInner_topFormPushforward_right
    (a : M.Carrier) (F : ComplexVector n → ComplexVector r)
    (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    (hs : tsupport F ⊆ localDomain (r := r) E a)
    (u : WeightedTopSection E g μ hμ h hh φ hφ) :
    weightedTopInner E g.form μ h φ u.1 (topFormPushforward (r := r) E a F) =
      (2 : ℝ) ^ n • ∫ z,
        (∑ α, ∑ β, star (coefficients (r := r) E u.1 a z Fin.elim0 α) *
          BundleDbar.metricMatrix (r := r) E h a z α β * F z β) *
            (Real.exp (-φ (chartInv a z)) : ℂ) ∂lebesgueC n := by
  classical
  let v := topFormPushforward (r := r) E a F
  let P := weightedTopPairing E g.form h φ u.1 v
  let Q := fun z => (∑ α, ∑ β, star (coefficients (r := r) E u.1 a z Fin.elim0 α) *
    BundleDbar.metricMatrix (r := r) E h a z α β * F z β) * (Real.exp (-φ (chartInv a z)) : ℂ)
  have hv := topFormPushforward_weightedL2 E g μ hμ h hh φ hφ hE a F hF hc hs
  have hP : Integrable P μ := weightedTopPairing_integrable E g μ hμ h hh φ hφ u.1 v u.2 hv
  have hPzero (x : M.Carrier) (hx : x ∉ bundleChartSource (r := r) E a) : P x = 0 := by
    have hvx : v x = (0 : NQForm E 0) x := by
      change (if hy : x ∈ bundleChartSource (r := r) E a then
        (topTensorCoordinatesEquiv (r := r) E a x hy).symm (F (chartPt a x))
        else (0 : antiComplexSubmodule E x 0)) = (0 : antiComplexSubmodule E x 0)
      exact dif_neg hx
    have he := weightedTopPairing_eq_zero_of_left_zero E g.form h φ v u.1 x hvx
    have he' := congrArg star he
    have ht : (Real.exp (-φ x) : ℂ) * topFormPairing E g.form h u.1 v x = 0 := by
      simpa only [weightedTopPairing, star_mul, topFormPairing_conj_symm,
        Complex.star_def, Complex.conj_ofReal, map_zero] using he'
    change topFormPairing E g.form h u.1 v x * (Real.exp (-φ x) : ℂ) = 0
    exact (mul_comm _ _).trans ht
  have hFzero (z : ComplexVector n) (hz : z ∉ localDomain (r := r) E a) : F z = 0 := by
    by_contra hn
    exact hz (hs (subset_tsupport F hn))
  apply integral_of_compact_chart_density g μ hμ a P Q hP
    (fun x hx => hPzero x (fun hy => hx hy.1))
    (fun z hz => by dsimp [Q]; rw [hFzero z (fun h => hz h.1)]; simp)
  intro z hz
  by_cases hzo : z ∈ localDomain (r := r) E a
  · change Real.sqrt (realMetricFn g.form a z).det •
      (topFormPairing E g.form h u.1 v (chartInv a z) * (Real.exp (-φ (chartInv a z)) : ℂ)) = _
    rw [topFormPairing_inChart E g.form h u.1 v a z hzo,
      topFormPushforward_coefficients E a F z hzo, realMetricFn_sqrt_det g.form a z hz]
    dsimp only [Q]
    simp only [Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_inv]
    have hd : ((hMat g.form a z).det.re : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (ne_of_gt (L18Aux.hMat_det_re_pos g.form a hz))
    field_simp [hd]
    <;> ring
  · rw [show P (chartInv a z) = 0 from hPzero _ (fun hy => hzo ⟨hz, hy.2⟩)]
    dsimp only [Q]
    rw [hFzero z hzo]
    simp

set_option backward.isDefEq.respectTransparency false in
theorem weightedOneInner_oneFormPushforward_right
    (a : M.Carrier) (F : ComplexVector n → Fin n → ComplexVector r)
    (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    (hs : tsupport F ⊆ localDomain (r := r) E a)
    (u : WeightedOneSection E g μ hμ h hh φ hφ) :
    weightedOneInner E g.form μ h φ u.1 (oneFormPushforward (r := r) E a F) =
      (2 : ℝ) ^ n • ∫ z,
        ∑ i, ∑ α, star (coefficients (r := r) E u.1 a z (fun _ => i) α) *
          chartOneDual (r := r) E g.form h φ a F z i α ∂lebesgueC n := by
  classical
  let v := oneFormPushforward (r := r) E a F
  let P := weightedOnePairing E g.form h φ u.1 v
  let Q := fun z => ∑ i, ∑ α, star (coefficients (r := r) E u.1 a z (fun _ => i) α) *
    chartOneDual (r := r) E g.form h φ a F z i α
  have hv := oneFormPushforward_weightedL2 E g μ hμ h hh φ hφ hE a F hF hc hs
  have hP : Integrable P μ := weightedOnePairing_integrable E g μ hμ h hh φ hφ u.1 v u.2 hv
  have hPzero (x : M.Carrier) (hx : x ∉ bundleChartSource (r := r) E a) : P x = 0 := by
    apply weightedOnePairing_eq_zero_of_right_zero E g.form h φ u.1 v x
    change (if hy : x ∈ bundleChartSource (r := r) E a then
      oneTensorFromCoefficients (r := r) E a x hy (F (chartPt a x)) else 0) = 0
    exact dif_neg hx
  have hFzero (z : ComplexVector n) (hz : z ∉ localDomain (r := r) E a) : F z = 0 := by
    by_contra hn
    exact hz (hs (subset_tsupport F hn))
  have hQzero (z : ComplexVector n) (hz : z ∉ localDomain (r := r) E a) : Q z = 0 := by
    dsimp only [Q, chartOneDual]
    rw [hFzero z hz]
    simp
  apply integral_of_compact_chart_density g μ hμ a P Q hP
    (fun x hx => hPzero x (fun hy => hx hy.1)) (fun z hz => hQzero z (fun h => hz h.1))
  intro z hz
  by_cases hzo : z ∈ localDomain (r := r) E a
  · change Real.sqrt (realMetricFn g.form a z).det •
      (oneFormPairing E g.form h u.1 v (chartInv a z) * (Real.exp (-φ (chartInv a z)) : ℂ)) = _
    rw [oneFormPairing_inChart E g.form h u.1 v a z hzo, realMetricFn_sqrt_det g.form a z hz]
    have hcf (i : Fin n) (α : Fin r) :
        coefficients (r := r) E v a z (fun _ => i) α = F z i α :=
      oneFormPushforward_coefficients E a F z hzo i α
    simp only [hcf]
    dsimp only [Q, chartOneDual]
    simp only [Complex.real_smul, Complex.ofReal_mul]
    have hd : ((hMat g.form a z).det.re : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (ne_of_gt (L18Aux.hMat_det_re_pos g.form a hz))
    simp only [div_eq_mul_inv, Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)]
    apply Finset.sum_congr rfl
    intro α _
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro β _
    field_simp [hd]
    <;> ring
  · rw [hPzero _ (fun hy => hzo ⟨hz, hy.2⟩), hQzero z hzo]
    simp

end Yau.LeafProofs.L14Aux

namespace Yau.LeafProofs.L14Aux

open BundleDbar Filter

variable {n r : ℕ} {M : ComplexManifold n}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]
variable (g : Yau.SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
  (h : Metric E) (hh : BundleDbar.SmoothMetric (r := r) E h) (φ : M.Carrier → ℝ) (hφ : SmoothFn φ)
  (hE : Holomorphic (r := r) E)

include hE

set_option backward.isDefEq.respectTransparency false in
theorem weakDbar_chart_adjoint_pairing
    (a : M.Carrier) (F : ComplexVector n → Fin n → ComplexVector r)
    (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    (hs : tsupport F ⊆ localDomain (r := r) E a)
    (u : WeightedTopSection E g μ hμ h hh φ hφ)
    (f : WeightedOneSection E g μ hμ h hh φ hφ)
    (hw : WeakDbar (r := r) E u.1 f.1) :
    weightedOneInner E g.form μ h φ f.1 (oneFormPushforward (r := r) E a F) =
      weightedTopInner E g.form μ h φ u.1
        (topFormPushforward (r := r) E a (chartDbarAdjoint (r := r) E g.form h φ a F)) := by
  classical
  let B := chartOneDual (r := r) E g.form h φ a F
  let δ := chartDbarAdjoint (r := r) E g.form h φ a F
  have hB (i : Fin n) (α : Fin r) : ContDiff ℝ ∞ (fun z => B z i α) :=
    chartOneDual_contDiff E g h hh φ hφ a F hF hs i α
  have hsB (i : Fin n) (α : Fin r) : tsupport (fun z => B z i α) ⊆ localDomain (r := r) E a :=
    (tsupport_chartOneDual_subset E g.form h φ a F i α).trans hs
  have hcB (i : Fin n) (α : Fin r) : HasCompactSupport (fun z => B z i α) :=
    hc.of_isClosed_subset (isClosed_tsupport _) (tsupport_chartOneDual_subset E g.form h φ a F i α)
  have hδ : ContDiff ℝ ∞ δ := chartDbarAdjoint_contDiff E g h hh φ hφ a F hF hs
  have hsδ : tsupport δ ⊆ localDomain (r := r) E a :=
    (tsupport_chartDbarAdjoint_subset E g.form h φ a F).trans hs
  have hcδ : HasCompactSupport δ := hc.of_isClosed_subset (isClosed_tsupport _)
    (tsupport_chartDbarAdjoint_subset E g.form h φ a F)
  have hWB (i : Fin n) (α : Fin r) : ContDiff ℝ ∞
      (fun z => wirt (fun y => B y i α) z (stdVec i)) := by
    simpa only [contDiffOn_univ] using
      wirt_contDiffOn isOpen_univ _ (hB i α).contDiffOn (stdVec i)
  have hsWB (i : Fin n) (α : Fin r) :
      tsupport (fun z => wirt (fun y => B y i α) z (stdVec i)) ⊆ localDomain (r := r) E a :=
    (tsupport_wirt_subset _ (stdVec i)).trans (hsB i α)
  have hcWB (i : Fin n) (α : Fin r) :
      HasCompactSupport (fun z => wirt (fun y => B y i α) z (stdVec i)) :=
    (hcB i α).of_isClosed_subset (isClosed_tsupport _) (tsupport_wirt_subset _ (stdVec i))
  have hL (i : Fin n) (α : Fin r) : Integrable
      (fun z => star (coefficients (r := r) E f.1 a z (fun _ => i) α) * B z i α) (lebesgueC n) :=
    locallyL2_conjugate_test_integrable E f.1 f.2.1 a (fun _ => i) α _
      (hB i α).continuous (hcB i α) (hsB i α)
  have hR (i : Fin n) (α : Fin r) : Integrable
      (fun z => star (coefficients (r := r) E u.1 a z Fin.elim0 α) *
        wirt (fun y => B y i α) z (stdVec i)) (lebesgueC n) :=
    locallyL2_conjugate_test_integrable E u.1 u.2.1 a Fin.elim0 α _
      (hWB i α).continuous (hcWB i α) (hsWB i α)
  have hweak (i : Fin n) (α : Fin r) :
      (∫ z, star (coefficients (r := r) E f.1 a z (fun _ => i) α) * B z i α ∂lebesgueC n) =
        -(∫ z, star (coefficients (r := r) E u.1 a z Fin.elim0 α) *
          wirt (fun y => B y i α) z (stdVec i) ∂lebesgueC n) := by
    let ψ := fun z => star (B z i α)
    have hψ : ContDiff ℝ ∞ ψ := Complex.conjCLE.contDiff.comp (hB i α)
    have hsψ : tsupport ψ ⊆ tsupport (fun z => B z i α) :=
      tsupport_comp_subset (g := fun c : ℂ => star c) (by exact star_zero _) _
    have ht := (weakDbar_zero_iff_component_tests E u.1 f.1).mp hw |>.2.2
      a i α ψ hψ ((hcB i α).of_isClosed_subset (isClosed_tsupport _) hsψ) (hsψ.trans (hsB i α))
    calc
      _ = star (∫ z, coefficients (r := r) E f.1 a z (fun _ => i) α * ψ z ∂lebesgueC n) := by
        calc
          _ = ∫ z, star (coefficients (r := r) E f.1 a z (fun _ => i) α * ψ z) ∂lebesgueC n :=
            integral_congr_ae (Eventually.of_forall fun z => by
              simp only [ψ, star_mul, star_star, mul_comm])
          _ = _ := integral_conj (f := fun z => coefficients (r := r) E f.1 a z (fun _ => i) α * ψ z)
      _ = star (-(∫ z, coefficients (r := r) E u.1 a z Fin.elim0 α *
          wirtBar ψ z (stdVec i) ∂lebesgueC n)) := congrArg star ht
      _ = _ := by
        have he : star (∫ z, coefficients (r := r) E u.1 a z Fin.elim0 α *
            wirtBar ψ z (stdVec i) ∂lebesgueC n) =
            ∫ z, star (coefficients (r := r) E u.1 a z Fin.elim0 α) *
              wirt (fun y => B y i α) z (stdVec i) ∂lebesgueC n := by
          calc
            _ = ∫ z, star (coefficients (r := r) E u.1 a z Fin.elim0 α *
                wirtBar ψ z (stdVec i)) ∂lebesgueC n :=
              (integral_conj (f := fun z => coefficients (r := r) E u.1 a z Fin.elim0 α *
                wirtBar ψ z (stdVec i))).symm
            _ = _ := integral_congr_ae (Eventually.of_forall fun z => by
              simp only [ψ, star_mul, wirtBar_star, star_star, mul_comm])
        simpa only [star_neg] using congrArg Neg.neg he
  have hdual (z : ComplexVector n) (α : Fin r) :
      (∑ β, BundleDbar.metricMatrix (r := r) E h a z α β * δ z β) *
        (Real.exp (-φ (chartInv a z)) : ℂ) =
          -∑ i, wirt (fun y => B y i α) z (stdVec i) := by
    by_cases hz : z ∈ localDomain (r := r) E a
    · exact chartDbarAdjoint_dual E g.form h φ a F z hz α
    · have hzδ : δ z = 0 := image_eq_zero_of_notMem_tsupport (fun h => hz (hsδ h))
      have hzWB (i : Fin n) : wirt (fun y => B y i α) z (stdVec i) = 0 := by
        have hz' : z ∉ tsupport (fun y => wirt (fun w => B w i α) y (stdVec i)) :=
          fun h => hz (hsWB i α h)
        exact image_eq_zero_of_notMem_tsupport
          (f := fun y => wirt (fun w => B w i α) y (stdVec i)) hz'
      simp only [hzδ, PiLp.zero_apply, hzWB, mul_zero, zero_mul, Finset.sum_const_zero, neg_zero]
  have hpoint (z : ComplexVector n) :
      (∑ α, ∑ β, star (coefficients (r := r) E u.1 a z Fin.elim0 α) *
        BundleDbar.metricMatrix (r := r) E h a z α β * δ z β) *
          (Real.exp (-φ (chartInv a z)) : ℂ) =
      -(∑ i, ∑ α, star (coefficients (r := r) E u.1 a z Fin.elim0 α) *
        wirt (fun y => B y i α) z (stdVec i)) := by
    calc
      _ = ∑ α, star (coefficients (r := r) E u.1 a z Fin.elim0 α) *
          ((∑ β, BundleDbar.metricMatrix (r := r) E h a z α β * δ z β) *
            (Real.exp (-φ (chartInv a z)) : ℂ)) := by
        simp_rw [Finset.sum_mul, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro α _
        apply Finset.sum_congr rfl
        intro β _
        ring
      _ = _ := by
        simp_rw [hdual, mul_neg, Finset.mul_sum, Finset.sum_neg_distrib]
        rw [Finset.sum_comm]
  have hsum (P : Fin n → Fin r → ComplexVector n → ℂ)
      (hP : ∀ i α, Integrable (P i α) (lebesgueC n)) :
      (∫ z, ∑ i, ∑ α, P i α z ∂lebesgueC n) = ∑ i, ∑ α, ∫ z, P i α z ∂lebesgueC n := by
    rw [integral_finset_sum _ (fun i _ => integrable_finset_sum _ (fun α _ => hP i α))]
    apply Finset.sum_congr rfl
    intro i _
    exact integral_finset_sum _ (fun α _ => hP i α)
  rw [weightedOneInner_oneFormPushforward_right E g μ hμ h hh φ hφ hE a F hF hc hs f,
    weightedTopInner_topFormPushforward_right E g μ hμ h hh φ hφ hE a δ hδ hcδ hsδ u]
  congr 1
  calc
    _ = ∑ i, ∑ α, ∫ z, star (coefficients (r := r) E f.1 a z (fun _ => i) α) * B z i α ∂lebesgueC n :=
      hsum _ hL
    _ = -(∑ i, ∑ α, ∫ z, star (coefficients (r := r) E u.1 a z Fin.elim0 α) *
        wirt (fun y => B y i α) z (stdVec i) ∂lebesgueC n) := by
      simp_rw [hweak, Finset.sum_neg_distrib]
    _ = -(∫ z, ∑ i, ∑ α, star (coefficients (r := r) E u.1 a z Fin.elim0 α) *
        wirt (fun y => B y i α) z (stdVec i) ∂lebesgueC n) := congrArg Neg.neg (hsum _ hR).symm
    _ = _ := by
      rw [← integral_neg]
      exact integral_congr_ae (Eventually.of_forall fun z => (hpoint z).symm)

end Yau.LeafProofs.L14Aux

namespace Yau.LeafProofs.L14Aux

open BundleDbar Filter

variable {n r : ℕ} {M : ComplexManifold n}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]
variable (g : Yau.SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
  (h : Metric E) (hh : BundleDbar.SmoothMetric (r := r) E h) (φ : M.Carrier → ℝ) (hφ : SmoothFn φ)
  (hE : Holomorphic (r := r) E)

include hμ hh hφ hE

def weightedOneChartSection (a : M.Carrier) (F : ComplexVector n → Fin n → ComplexVector r)
    (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    (hs : tsupport F ⊆ localDomain (r := r) E a) : WeightedOneSection E g μ hμ h hh φ hφ :=
  ⟨oneFormPushforward (r := r) E a F,
    oneFormPushforward_weightedL2 E g μ hμ h hh φ hφ hE a F hF hc hs⟩

def weightedDbarAdjointChartSection (a : M.Carrier) (F : ComplexVector n → Fin n → ComplexVector r)
    (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    (hs : tsupport F ⊆ localDomain (r := r) E a) : WeightedTopSection E g μ hμ h hh φ hφ :=
  weightedTopChartSection E g μ hμ h hh φ hφ hE a (chartDbarAdjoint (r := r) E g.form h φ a F)
    (chartDbarAdjoint_contDiff E g h hh φ hφ a F hF hs)
    (hc.of_isClosed_subset (isClosed_tsupport _) (tsupport_chartDbarAdjoint_subset E g.form h φ a F))
    ((tsupport_chartDbarAdjoint_subset E g.form h φ a F).trans hs)

set_option backward.isDefEq.respectTransparency false in
theorem weightedMaximalDbar_adjoint_chart
    (a : M.Carrier) (F : ComplexVector n → Fin n → ComplexVector r)
    (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    (hs : tsupport F ⊆ localDomain (r := r) E a) :
    (realizeWeightedOneSection E g μ hμ h hh φ hφ
        (weightedOneChartSection E g μ hμ h hh φ hφ hE a F hF hc hs),
      realizeWeightedTopSection E g μ hμ h hh φ hφ
        (weightedDbarAdjointChartSection E g μ hμ h hh φ hφ hE a F hF hc hs)) ∈
      (weightedMaximalDbar E g μ hμ h hh φ hφ).adjoint.graph := by
  let T := weightedMaximalDbar E g μ hμ h hh φ hφ
  let V := weightedOneChartSection E g μ hμ h hh φ hφ hE a F hF hc hs
  let S := weightedDbarAdjointChartSection E g μ hμ h hh φ hφ hE a F hF hc hs
  let v := realizeWeightedOneSection E g μ hμ h hh φ hφ V
  let s := realizeWeightedTopSection E g μ hμ h hh φ hφ S
  change (v, s) ∈ T.adjoint.graph
  have hpair (x : T.domain) : inner ℂ s (x : WeightedTopHilbert E g μ hμ h hh φ hφ) =
      inner ℂ v (T x) := by
    let U := weightedTopHilbertRepresentative E g μ hμ h hh φ hφ x
    let D := weightedOneHilbertRepresentative E g μ hμ h hh φ hφ (T x)
    have hG : ((x : WeightedTopHilbert E g μ hμ h hh φ hφ), T x) ∈
        weightedMaximalDbarHilbertGraph E g μ hμ h hh φ hφ := by
      rw [← weightedMaximalDbar_graph]
      exact T.mem_graph x
    have hw : WeakDbar (r := r) E U.1 D.1 :=
      (weightedMaximalDbarHilbertGraph_iff_representative E g μ hμ h hh φ hφ _ _).mp hG
    have hp := weakDbar_chart_adjoint_pairing E g μ hμ h hh φ hφ hE a F hF hc hs U D hw
    have hleft := realizeWeightedOneSection_inner E g μ hμ h hh φ hφ D V
    have hright := realizeWeightedTopSection_inner E g μ hμ h hh φ hφ U S
    rw [weightedOneHilbertRepresentative_realize] at hleft
    rw [weightedTopHilbertRepresentative_realize] at hright
    have hi : inner ℂ (T x) v = inner ℂ (x : WeightedTopHilbert E g μ hμ h hh φ hφ) s :=
      hleft.trans (hp.trans hright.symm)
    calc
      _ = star (inner ℂ (x : WeightedTopHilbert E g μ hμ h hh φ hφ) s) := (inner_conj_symm _ _).symm
      _ = star (inner ℂ (T x) v) := congrArg star hi.symm
      _ = _ := inner_conj_symm _ _
  have hv : v ∈ T.adjoint.domain :=
    LinearPMap.mem_adjoint_domain_of_exists v ⟨s, hpair⟩
  have hout : T.adjoint ⟨v, hv⟩ = s :=
    LinearPMap.adjoint_apply_eq (weightedMaximalDbar_domain_dense E g μ hμ h hh φ hφ hE) _ hpair
  exact T.adjoint.mem_graph_iff.mpr ⟨⟨v, hv⟩, rfl, hout⟩

end Yau.LeafProofs.L14Aux

namespace Yau.LeafProofs.L14Aux

open BundleDbar Filter

theorem wirtBar_real_components {n : ℕ} (f : ComplexVector n → ℂ)
    (z : ComplexVector n) (hf : DifferentiableAt ℝ f z) (i : Fin n) :
    (wirtBar f z (stdVec i)).re = (1 / 2 : ℝ) *
      (rDeriv (fun y => (f y).re) z (i, 0) - rDeriv (fun y => (f y).im) z (i, 1)) ∧
    (wirtBar f z (stdVec i)).im = (1 / 2 : ℝ) *
      (rDeriv (fun y => (f y).im) z (i, 0) + rDeriv (fun y => (f y).re) z (i, 1)) := by
  have hR : fderiv ℝ (fun y => (f y).re) z = Complex.reCLM.comp (fderiv ℝ f z) :=
    (Complex.reCLM.hasFDerivAt.comp z hf.hasFDerivAt).fderiv
  have hI : fderiv ℝ (fun y => (f y).im) z = Complex.imCLM.comp (fderiv ℝ f z) :=
    (Complex.imCLM.hasFDerivAt.comp z hf.hasFDerivAt).fderiv
  constructor <;>
    simp [wirtBar, rDeriv, hR, hI, realVec, stdVec, Complex.mul_re, Complex.mul_im] <;> ring

theorem kahler_hMat_wirtBar_symm {n : ℕ} {M : ComplexManifold n}
    (g : Yau.SmoothMetric M) (a : M.Carrier) (z : ComplexVector n)
    (hz : z ∈ chartTarget a) (i j k : Fin n) :
    wirtBar (fun y => hMat g.form a y j k) z (stdVec i) =
      wirtBar (fun y => hMat g.form a y i k) z (stdVec j) := by
  let G := hMat g.form a
  let R := fun p q d => rDeriv (fun y => (G y p q).re) z d
  let I := fun p q d => rDeriv (fun y => (G y p q).im) z d
  have hDiff (p q : Fin n) : DifferentiableAt ℝ (fun y => G y p q) z :=
    ((L18Aux.hMat_contDiffOn g a p q).contDiffAt
      ((isOpen_extChartAt_target (I := ComplexModel n) a).mem_nhds hz)).differentiableAt (by simp)
  have hRDiff (p q : Fin n) : DifferentiableAt ℝ (fun y => (G y p q).re) z :=
    Complex.reCLM.differentiableAt.comp z (hDiff p q)
  have hIDiff (p q : Fin n) : DifferentiableAt ℝ (fun y => (G y p q).im) z :=
    Complex.imCLM.differentiableAt.comp z (hDiff p q)
  have hRe (p q : Fin n) : (fun y => (G y p q).re) = fun y => (G y q p).re := by
    funext y
    have he := congrArg Complex.re ((L18Aux.hMat_isHermitian g.form a y).apply p q)
    simpa only [Complex.star_def, Complex.conj_re] using he.symm
  have hIm (p q : Fin n) : (fun y => (G y p q).im) = fun y => -(G y q p).im := by
    funext y
    have he := congrArg Complex.im ((L18Aux.hMat_isHermitian g.form a y).apply p q)
    simpa only [Complex.star_def, Complex.conj_im] using he.symm
  have hRsym (p q : Fin n) (d : RIdx n) : R p q d = R q p d :=
    congrArg (fun f : ComplexVector n → ℝ => rDeriv f z d) (hRe p q)
  have hNeg (f : ComplexVector n → ℝ) (d : RIdx n) :
      rDeriv (fun y => -f y) z d = -rDeriv f z d := by
    unfold rDeriv
    rw [fderiv_fun_neg]
    rfl
  have hIskew (p q : Fin n) (d : RIdx n) : I p q d = -I q p d := by
    change rDeriv (fun y => (G y p q).im) z d = -rDeriv (fun y => (G y q p).im) z d
    rw [hIm p q, hNeg]
  have hScaleR (p q : Fin n) (c : ℝ) (d : RIdx n) :
      rDeriv (fun y => c * (hMat g.form a y p q).re) z d = c * R p q d :=
    L18Aux.rDeriv_const_mul (hRDiff p q) c d
  have hScaleI (p q : Fin n) (c : ℝ) (d : RIdx n) :
      rDeriv (fun y => c * (hMat g.form a y p q).im) z d = c * I p q d :=
    L18Aux.rDeriv_const_mul (hIDiff p q) c d
  have C1 := L18Aux.kahlerClosed_in_chart g g.kahler_equations a hz (i, 0) (j, 0) (k, 1)
  have C2 := L18Aux.kahlerClosed_in_chart g g.kahler_equations a hz (i, 1) (j, 1) (k, 1)
  have C3 := L18Aux.kahlerClosed_in_chart g g.kahler_equations a hz (i, 0) (j, 0) (k, 0)
  have C4 := L18Aux.kahlerClosed_in_chart g g.kahler_equations a hz (i, 1) (j, 1) (k, 0)
  norm_num only [L18Aux.kahlerFormFn_entries, Prod.fst, Prod.snd, Fin.reduceEq,
    ite_true, ite_false, mul_neg] at C1 C2 C3 C4
  simp only [hNeg, hScaleR, hScaleI] at C1 C2 C3 C4
  have hfirst := wirtBar_real_components (fun y => G y j k) z (hDiff j k) i
  have hsecond := wirtBar_real_components (fun y => G y i k) z (hDiff i k) j
  apply Complex.ext
  · rw [hfirst.1, hsecond.1]
    change (1 / 2 : ℝ) * (R j k (i, 0) - I j k (i, 1)) =
      (1 / 2 : ℝ) * (R i k (j, 0) - I i k (j, 1))
    nlinarith [hRsym k i (j, 0), hIskew k i (j, 1)]
  · rw [hfirst.2, hsecond.2]
    change (1 / 2 : ℝ) * (I j k (i, 0) + R j k (i, 1)) =
      (1 / 2 : ℝ) * (I i k (j, 0) + R i k (j, 1))
    nlinarith [hIskew k i (j, 0), hRsym k i (j, 1)]

end Yau.LeafProofs.L14Aux

namespace Yau.LeafProofs.L14Aux

open BundleDbar Filter

variable {n r : ℕ} {M : ComplexManifold n}

def chartOneRaise (g : HermitianField M) (a : M.Carrier)
    (F : ComplexVector n → Fin n → ComplexVector r) (z : ComplexVector n) (i : Fin n) : ComplexVector r :=
  WithLp.toLp 2 (fun α => ∑ j, (hMat g a z)⁻¹ i j * F z j α)

theorem chartOneRaise_lower (g : HermitianField M) (a : M.Carrier)
    (F : ComplexVector n → Fin n → ComplexVector r) (z : ComplexVector n)
    (hz : z ∈ chartTarget a) (j : Fin n) (α : Fin r) :
    (∑ i, hMat g a z j i * chartOneRaise g a F z i α) = F z j α := by
  change (hMat g a z *ᵥ ((hMat g a z)⁻¹ *ᵥ (fun i => F z i α))) j = F z j α
  rw [Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv _ ((hMat_posDef g a z hz).isUnit.map Matrix.detMonoidHom), Matrix.one_mulVec]

theorem chartOneRaise_contDiffOn (g : Yau.SmoothMetric M) (a : M.Carrier)
    (F : ComplexVector n → Fin n → ComplexVector r) (hF : ContDiff ℝ ∞ F)
    (i : Fin n) (α : Fin r) :
    ContDiffOn ℝ ∞ (fun z => chartOneRaise g.form a F z i α) (chartTarget a) := by
  change ContDiffOn ℝ ∞ (fun z => ∑ j, (hMat g.form a z)⁻¹ i j * F z j α) (chartTarget a)
  apply ContDiffOn.sum
  intro j _
  exact (L18Aux.hMat_inverse_contDiffOn g a i j).mul
    (((contDiff_piLp 2).mp ((contDiff_pi.mp hF) j) α).contDiffOn)

theorem dbarCoefficients_chartOneRaise (g : Yau.SmoothMetric M) (a : M.Carrier)
    (F : ComplexVector n → Fin n → ComplexVector r) (hF : ContDiff ℝ ∞ F)
    (z : ComplexVector n) (hz : z ∈ chartTarget a) (i j : Fin n) (α : Fin r) :
    wirtBar (fun y => F y j α) z (stdVec i) - wirtBar (fun y => F y i α) z (stdVec j) =
      ∑ b, (hMat g.form a z j b *
        wirtBar (fun y => chartOneRaise g.form a F y b α) z (stdVec i) -
          hMat g.form a z i b * wirtBar (fun y => chartOneRaise g.form a F y b α) z (stdVec j)) := by
  have hG (p q : Fin n) : DifferentiableAt ℝ (fun y => hMat g.form a y p q) z :=
    ((L18Aux.hMat_contDiffOn g a p q).contDiffAt
      ((isOpen_extChartAt_target (I := ComplexModel n) a).mem_nhds hz)).differentiableAt (by simp)
  have hW (b : Fin n) : DifferentiableAt ℝ (fun y => chartOneRaise g.form a F y b α) z :=
    ((chartOneRaise_contDiffOn g a F hF b α).contDiffAt
      ((isOpen_extChartAt_target (I := ComplexModel n) a).mem_nhds hz)).differentiableAt (by simp)
  have hEq (k : Fin n) : (fun y => F y k α) =ᶠ[𝓝 z]
      (fun y => ∑ b, hMat g.form a y k b * chartOneRaise g.form a F y b α) := by
    filter_upwards [(isOpen_extChartAt_target (I := ComplexModel n) a).mem_nhds hz] with y hy
    exact (chartOneRaise_lower g.form a F y hy k α).symm
  have hDer (k : Fin n) (v : ComplexVector n) :
      wirtBar (fun y => F y k α) z v =
        ∑ b, (wirtBar (fun y => hMat g.form a y k b) z v * chartOneRaise g.form a F z b α +
          hMat g.form a z k b * wirtBar (fun y => chartOneRaise g.form a F y b α) z v) := by
    calc
      _ = wirtBar (fun y => ∑ b, hMat g.form a y k b * chartOneRaise g.form a F y b α) z v := by
        unfold wirtBar
        rw [(hEq k).fderiv_eq]
      _ = ∑ b, wirtBar (fun y => hMat g.form a y k b * chartOneRaise g.form a F y b α) z v :=
        wirtBar_sum_fun Finset.univ _ z v (fun b _ => (hG k b).mul (hW b))
      _ = _ := Finset.sum_congr rfl (fun b _ =>
        wirtBar_mul_rule _ _ z v (hG k b) (hW b))
  rw [hDer j (stdVec i), hDer i (stdVec j), ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro b _
  rw [kahler_hMat_wirtBar_symm g a z hz i j b]
  ring

end Yau.LeafProofs.L14Aux

namespace Yau.LeafProofs.L14Aux

open BundleDbar Filter

theorem wirt_mul_rule {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (f g : X → ℂ) (z v : X) (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) :
    wirt (fun x => f x * g x) z v = wirt f z v * g z + f z * wirt g z v := by
  unfold wirt
  rw [fderiv_fun_mul hf hg]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

theorem wirt_sum_fun {X ι : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (s : Finset ι) (f : ι → X → ℂ) (z v : X)
    (hf : ∀ i ∈ s, DifferentiableAt ℝ (f i) z) :
    wirt (fun x => ∑ i ∈ s, f i x) z v = ∑ i ∈ s, wirt (f i) z v := by
  unfold wirt
  rw [fderiv_fun_sum hf]
  simp only [sum_apply, mul_sub, Finset.mul_sum, Finset.sum_sub_distrib, mul_assoc]

theorem wirt_star {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (f : X → ℂ) (z v : X) : wirt (fun y => star (f y)) z v = star (wirtBar f z v) := by
  unfold wirt wirtBar
  rw [fderiv_star]
  simp [star_mul, star_add]
  ring

variable {n r : ℕ}

def localChernD (H : ComplexVector n → Matrix (Fin r) (Fin r) ℂ)
    (u : ComplexVector n → Fin r → ℂ) (i : Fin n) (z : ComplexVector n) : Fin r → ℂ :=
  (fun α => wirt (fun y => u y α) z (stdVec i)) + chernConnectionMatrix H z i *ᵥ u z

theorem chernConnection_lower (H : ComplexVector n → Matrix (Fin r) (Fin r) ℂ)
    (z : ComplexVector n) (hH : IsUnit (H z).det) (i : Fin n) :
    H z * chernConnectionMatrix H z i =
      Matrix.of (fun α β => wirt (fun y => H y α β) z (stdVec i)) := by
  unfold chernConnectionMatrix
  rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hH, Matrix.one_mul]

theorem localChernD_lower (H : ComplexVector n → Matrix (Fin r) (Fin r) ℂ)
    (u : ComplexVector n → Fin r → ℂ) (z : ComplexVector n) (hH : IsUnit (H z).det) (i : Fin n) :
    H z *ᵥ localChernD H u i z =
      H z *ᵥ (fun α => wirt (fun y => u y α) z (stdVec i)) +
        Matrix.of (fun α β => wirt (fun y => H y α β) z (stdVec i)) *ᵥ u z := by
  rw [localChernD, Matrix.mulVec_add, Matrix.mulVec_mulVec, chernConnection_lower H z hH i]

set_option backward.isDefEq.respectTransparency false in
theorem chern_pairing_wirt (H : ComplexVector n → Matrix (Fin r) (Fin r) ℂ)
    (u v : ComplexVector n → Fin r → ℂ) (z : ComplexVector n) (i : Fin n)
    (hH : ∀ α β, DifferentiableAt ℝ (fun y => H y α β) z)
    (hu : ∀ α, DifferentiableAt ℝ (fun y => u y α) z)
    (hv : ∀ α, DifferentiableAt ℝ (fun y => v y α) z) (hdet : IsUnit (H z).det) :
    wirt (fun y => star (u y) ⬝ᵥ H y *ᵥ v y) z (stdVec i) =
      star (fun α => wirtBar (fun y => u y α) z (stdVec i)) ⬝ᵥ H z *ᵥ v z +
        star (u z) ⬝ᵥ H z *ᵥ localChernD H v i z := by
  have hsu (α : Fin r) : DifferentiableAt ℝ (fun y => star (u y α)) z :=
    Complex.conjCLE.differentiableAt.comp z (hu α)
  have ht (α β : Fin r) : DifferentiableAt ℝ
      (fun y => star (u y α) * H y α β * v y β) z := ((hsu α).mul (hH α β)).mul (hv β)
  have hpair : (fun y => star (u y) ⬝ᵥ H y *ᵥ v y) =
      (fun y => ∑ α, ∑ β, star (u y α) * H y α β * v y β) := by
    funext y
    simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro α _
    apply Finset.sum_congr rfl
    intro β _
    ring
  rw [hpair]
  rw [wirt_sum_fun Finset.univ _ z (stdVec i)
    (fun α _ => DifferentiableAt.fun_sum (fun β _ => ht α β))]
  have hinner (α : Fin r) :
      wirt (fun y => ∑ β, star (u y α) * H y α β * v y β) z (stdVec i) =
        ∑ β, wirt (fun y => star (u y α) * H y α β * v y β) z (stdVec i) :=
    wirt_sum_fun Finset.univ _ z (stdVec i) (fun β _ => ht α β)
  simp_rw [hinner]
  have hterm (α β : Fin r) :
      wirt (fun y => star (u y α) * H y α β * v y β) z (stdVec i) =
        star (wirtBar (fun y => u y α) z (stdVec i)) * H z α β * v z β +
        star (u z α) * wirt (fun y => H y α β) z (stdVec i) * v z β +
        star (u z α) * H z α β * wirt (fun y => v y β) z (stdVec i) := by
    rw [wirt_mul_rule (fun y => star (u y α) * H y α β) (fun y => v y β)
        z (stdVec i) ((hsu α).mul (hH α β)) (hv β),
      wirt_mul_rule (fun y => star (u y α)) (fun y => H y α β)
        z (stdVec i) (hsu α) (hH α β), wirt_star]
    ring
  simp_rw [hterm]
  rw [localChernD_lower H v z hdet i, dotProduct_add]
  simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, Pi.star_apply,
    Finset.mul_sum, Finset.sum_add_distrib]
  ring

end Yau.LeafProofs.L14Aux

namespace Yau.LeafProofs.L14Aux

open BundleDbar Filter

set_option backward.isDefEq.respectTransparency false in
theorem chern_pairing_wirtBar {n r : ℕ}
    (H : ComplexVector n → Matrix (Fin r) (Fin r) ℂ)
    (u v : ComplexVector n → Fin r → ℂ) (z : ComplexVector n) (i : Fin n)
    (hH : ∀ α β, DifferentiableAt ℝ (fun y => H y α β) z)
    (hu : ∀ α, DifferentiableAt ℝ (fun y => u y α) z)
    (hv : ∀ α, DifferentiableAt ℝ (fun y => v y α) z) (hdet : IsUnit (H z).det)
    (hHermitian : ∀ᶠ y in 𝓝 z, (H y).IsHermitian) :
    wirtBar (fun y => star (u y) ⬝ᵥ H y *ᵥ v y) z (stdVec i) =
      star (localChernD H u i z) ⬝ᵥ H z *ᵥ v z +
        star (u z) ⬝ᵥ H z *ᵥ (fun α => wirtBar (fun y => v y α) z (stdVec i)) := by
  have hHz : (H z).IsHermitian := hHermitian.self_of_nhds
  have hEq : (fun y => star (star (v y) ⬝ᵥ H y *ᵥ u y)) =ᶠ[𝓝 z]
      (fun y => star (u y) ⬝ᵥ H y *ᵥ v y) :=
    hHermitian.mono (fun y hy => hy.star_dotProduct_mulVec_comm (v y) (u y))
  have hBarEq : wirtBar (fun y => star (star (v y) ⬝ᵥ H y *ᵥ u y)) z (stdVec i) =
      wirtBar (fun y => star (u y) ⬝ᵥ H y *ᵥ v y) z (stdVec i) := by
    unfold wirtBar
    rw [hEq.fderiv_eq]
  have hstar (f : ComplexVector n → ℂ) :
      wirtBar (fun y => star (f y)) z (stdVec i) = star (wirt f z (stdVec i)) := by
    have he := congrArg star (wirt_star (fun y => star (f y)) z (stdVec i))
    simpa only [star_star] using he.symm
  calc
    _ = wirtBar (fun y => star (star (v y) ⬝ᵥ H y *ᵥ u y)) z (stdVec i) := hBarEq.symm
    _ = star (wirt (fun y => star (v y) ⬝ᵥ H y *ᵥ u y) z (stdVec i)) := hstar _
    _ = star (star (fun α => wirtBar (fun y => v y α) z (stdVec i)) ⬝ᵥ H z *ᵥ u z +
        star (v z) ⬝ᵥ H z *ᵥ localChernD H u i z) :=
      congrArg star (chern_pairing_wirt H v u z i hH hv hu hdet)
    _ = _ := by
      rw [star_add, hHz.star_dotProduct_mulVec_comm, hHz.star_dotProduct_mulVec_comm]
      ring

end Yau.LeafProofs.L14Aux

namespace Yau.LeafProofs.L14Aux

open BundleDbar Filter

theorem fderiv_wirt {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    {f : X → ℂ} {z : X} (hf : DifferentiableAt ℝ (fderiv ℝ f) z) (v w : X) :
    fderiv ℝ (fun y => wirt f y v) z w = (1 / 2 : ℂ) *
      (fderiv ℝ (fderiv ℝ f) z w v - Complex.I * fderiv ℝ (fderiv ℝ f) z w (Complex.I • v)) := by
  have hv := hf.clm_apply (differentiableAt_const v)
  have hIv := hf.clm_apply (differentiableAt_const (Complex.I • v))
  simp only [wirt]
  rw [fderiv_const_mul (hv.fun_sub (hIv.const_mul Complex.I)),
    fderiv_fun_sub hv (hIv.const_mul Complex.I), fderiv_const_mul hIv,
    fderiv_clm_apply hf (differentiableAt_const v),
    fderiv_clm_apply hf (differentiableAt_const (Complex.I • v))]
  simp

theorem wirtBar_wirt_eq_secondFDeriv {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    {f : X → ℂ} {z : X} (hf : DifferentiableAt ℝ (fderiv ℝ f) z) (v w : X) :
    wirtBar (fun y => wirt f y v) z w = (1 / 4 : ℂ) *
      (fderiv ℝ (fderiv ℝ f) z w v +
        fderiv ℝ (fderiv ℝ f) z (Complex.I • w) (Complex.I • v) -
        Complex.I * fderiv ℝ (fderiv ℝ f) z w (Complex.I • v) +
        Complex.I * fderiv ℝ (fderiv ℝ f) z (Complex.I • w) v) := by
  rw [wirtBar, fderiv_wirt hf, fderiv_wirt hf]
  linear_combination -(1 / 4 : ℂ) *
    fderiv ℝ (fderiv ℝ f) z (Complex.I • w) (Complex.I • v) * Complex.I_sq

theorem wirt_wirtBar_comm {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (f : X → ℂ) (z : X) (hf : ContDiffAt ℝ 2 f z) (v w : X) :
    wirt (fun y => wirtBar f y v) z w = wirtBar (fun y => wirt f y w) z v := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) z :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hs := hf.isSymmSndFDerivAt (by norm_num)
  rw [L18Aux.wirt_wirtBar_eq_secondFDeriv hd, wirtBar_wirt_eq_secondFDeriv hd,
    hs v w, hs (Complex.I • v) (Complex.I • w), hs v (Complex.I • w), hs (Complex.I • v) w]
  ring

theorem wirtBar_add_rule {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (f g : X → ℂ) (z v : X) (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) :
    wirtBar (fun y => f y + g y) z v = wirtBar f z v + wirtBar g z v := by
  unfold wirtBar
  rw [fderiv_fun_add hf hg]
  simp only [ContinuousLinearMap.add_apply]
  ring

set_option backward.isDefEq.respectTransparency false in
theorem chern_commutator {n r : ℕ} {O : Set (ComplexVector n)} (hO : IsOpen O)
    (H : ComplexVector n → Matrix (Fin r) (Fin r) ℂ)
    (u : ComplexVector n → Fin r → ℂ)
    (hH : ∀ α β, ContDiffOn ℝ ∞ (fun y => H y α β) O)
    (hu : ∀ α, ContDiffOn ℝ ∞ (fun y => u y α) O)
    (hdet : ∀ y ∈ O, (H y).det ≠ 0)
    (z : ComplexVector n) (hz : z ∈ O) (i j : Fin n) (α : Fin r) :
    localChernD H (fun y β => wirtBar (fun t => u t β) y (stdVec j)) i z α -
      wirtBar (fun y => localChernD H u i y α) z (stdVec j) =
        ((H z)⁻¹ *ᵥ (curvatureMatrix H z i j *ᵥ u z)) α := by
  let Γ := chernConnectionMatrix H
  have hU (β : Fin r) : DifferentiableAt ℝ (fun y => u y β) z :=
    ((hu β).contDiffAt (hO.mem_nhds hz)).differentiableAt (by simp)
  have hG (β : Fin r) : DifferentiableAt ℝ (fun y => Γ y i α β) z :=
    ((chernConnectionMatrix_contDiffOn hO H hH hdet i α β).contDiffAt
      (hO.mem_nhds hz)).differentiableAt (by simp)
  have hW : DifferentiableAt ℝ (fun y => wirt (fun t => u t α) y (stdVec i)) z :=
    ((wirt_contDiffOn hO _ (hu α) (stdVec i)).contDiffAt
      (hO.mem_nhds hz)).differentiableAt (by simp)
  have hProd (β : Fin r) : DifferentiableAt ℝ (fun y => Γ y i α β * u y β) z :=
    (hG β).mul (hU β)
  have hbarProd (β : Fin r) :
      wirtBar (fun y => Γ y i α β * u y β) z (stdVec j) =
        wirtBar (fun y => Γ y i α β) z (stdVec j) * u z β +
          Γ z i α β * wirtBar (fun y => u y β) z (stdVec j) :=
    wirtBar_mul_rule (fun y => Γ y i α β) (fun y => u y β) z (stdVec j) (hG β) (hU β)
  have hbarD : wirtBar (fun y => localChernD H u i y α) z (stdVec j) =
      wirtBar (fun y => wirt (fun t => u t α) y (stdVec i)) z (stdVec j) +
        ∑ β, (wirtBar (fun y => Γ y i α β) z (stdVec j) * u z β +
          Γ z i α β * wirtBar (fun y => u y β) z (stdVec j)) := by
    change wirtBar (fun y => wirt (fun t => u t α) y (stdVec i) +
      ∑ β, Γ y i α β * u y β) z (stdVec j) = _
    rw [wirtBar_add_rule _ _ z (stdVec j) hW (DifferentiableAt.fun_sum (fun β _ => hProd β)),
      wirtBar_sum_fun Finset.univ _ z (stdVec j) (fun β _ => hProd β)]
    simp only [hbarProd]
  have hcurv : (H z)⁻¹ * curvatureMatrix H z i j =
      -(Matrix.of fun γ β => wirtBar (fun y => Γ y i γ β) z (stdVec j)) := by
    unfold curvatureMatrix
    rw [Matrix.mul_neg, ← Matrix.mul_assoc,
      Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (hdet z hz)), Matrix.one_mul]
  rw [Matrix.mulVec_mulVec, hcurv, Matrix.neg_mulVec]
  change wirt (fun y => wirtBar (fun t => u t α) y (stdVec j)) z (stdVec i) +
    (∑ β, Γ z i α β * wirtBar (fun y => u y β) z (stdVec j)) -
      wirtBar (fun y => localChernD H u i y α) z (stdVec j) =
        -(∑ β, wirtBar (fun y => Γ y i α β) z (stdVec j) * u z β)
  rw [hbarD, wirt_wirtBar_comm (fun y => u y α) z
    (((hu α).contDiffAt (hO.mem_nhds hz)).of_le (by norm_num)) (stdVec j) (stdVec i)]
  simp only [Finset.sum_add_distrib]
  ring

end Yau.LeafProofs.L14Aux

namespace Yau.LeafProofs.L14Aux

open BundleDbar Filter

theorem localChernD_contDiffOn {n r : ℕ} {O : Set (ComplexVector n)} (hO : IsOpen O)
    (H : ComplexVector n → Matrix (Fin r) (Fin r) ℂ) (u : ComplexVector n → Fin r → ℂ)
    (hH : ∀ α β, ContDiffOn ℝ ∞ (fun y => H y α β) O)
    (hu : ∀ α, ContDiffOn ℝ ∞ (fun y => u y α) O)
    (hdet : ∀ y ∈ O, (H y).det ≠ 0) (i : Fin n) (α : Fin r) :
    ContDiffOn ℝ ∞ (fun y => localChernD H u i y α) O := by
  change ContDiffOn ℝ ∞ (fun y => wirt (fun t => u t α) y (stdVec i) +
    ∑ β, chernConnectionMatrix H y i α β * u y β) O
  apply (wirt_contDiffOn hO _ (hu α) (stdVec i)).add
  exact ContDiffOn.sum (fun β _ => (chernConnectionMatrix_contDiffOn hO H hH hdet i α β).mul (hu β))

set_option backward.isDefEq.respectTransparency false in
theorem chern_pairing_second_order_divergence {n r : ℕ} {O : Set (ComplexVector n)} (hO : IsOpen O)
    (H : ComplexVector n → Matrix (Fin r) (Fin r) ℂ)
    (u v : ComplexVector n → Fin r → ℂ)
    (hH : ∀ α β, ContDiffOn ℝ ∞ (fun y => H y α β) O)
    (hu : ∀ α, ContDiffOn ℝ ∞ (fun y => u y α) O)
    (hv : ∀ α, ContDiffOn ℝ ∞ (fun y => v y α) O)
    (hdet : ∀ y ∈ O, (H y).det ≠ 0) (hHermitian : ∀ y ∈ O, (H y).IsHermitian)
    (z : ComplexVector n) (hz : z ∈ O) (i j : Fin n) :
    star (localChernD H u i z) ⬝ᵥ H z *ᵥ localChernD H v j z -
      star (fun α => wirtBar (fun y => u y α) z (stdVec j)) ⬝ᵥ H z *ᵥ
        (fun α => wirtBar (fun y => v y α) z (stdVec i)) =
      star (u z) ⬝ᵥ curvatureMatrix H z j i *ᵥ v z +
        wirtBar (fun y => star (u y) ⬝ᵥ H y *ᵥ localChernD H v j y) z (stdVec i) -
        wirt (fun y => star (u y) ⬝ᵥ H y *ᵥ
          (fun α => wirtBar (fun t => v t α) y (stdVec i))) z (stdVec j) := by
  have hHd (α β : Fin r) : DifferentiableAt ℝ (fun y => H y α β) z :=
    ((hH α β).contDiffAt (hO.mem_nhds hz)).differentiableAt (by simp)
  have hUd (α : Fin r) : DifferentiableAt ℝ (fun y => u y α) z :=
    ((hu α).contDiffAt (hO.mem_nhds hz)).differentiableAt (by simp)
  have hDd (α : Fin r) : DifferentiableAt ℝ (fun y => localChernD H v j y α) z :=
    ((localChernD_contDiffOn hO H v hH hv hdet j α).contDiffAt
      (hO.mem_nhds hz)).differentiableAt (by simp)
  have hBd (α : Fin r) : DifferentiableAt ℝ
      (fun y => wirtBar (fun t => v t α) y (stdVec i)) z :=
    ((wirtBar_contDiffOn hO _ (hv α) (stdVec i)).contDiffAt
      (hO.mem_nhds hz)).differentiableAt (by simp)
  have hunit : IsUnit (H z).det := isUnit_iff_ne_zero.mpr (hdet z hz)
  have hHerm : ∀ᶠ y in 𝓝 z, (H y).IsHermitian := by
    filter_upwards [hO.mem_nhds hz] with y hy
    exact hHermitian y hy
  have hbar := chern_pairing_wirtBar H u (fun y => localChernD H v j y)
    z i hHd hUd hDd hunit hHerm
  have hplain := chern_pairing_wirt H u
    (fun y α => wirtBar (fun t => v t α) y (stdVec i)) z j hHd hUd hBd hunit
  have hc : localChernD H (fun y α => wirtBar (fun t => v t α) y (stdVec i)) j z -
      (fun α => wirtBar (fun y => localChernD H v j y α) z (stdVec i)) =
        (H z)⁻¹ *ᵥ (curvatureMatrix H z j i *ᵥ v z) := by
    funext α
    exact chern_commutator hO H v hH hv hdet z hz j i α
  have hlower := congrArg (fun W : Fin r → ℂ => H z *ᵥ W) hc
  rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv _ hunit, Matrix.one_mulVec] at hlower
  have hdot := congrArg (fun W : Fin r → ℂ => star (u z) ⬝ᵥ W) hlower
  rw [dotProduct_sub] at hdot
  linear_combination -hbar + hplain + hdot

end Yau.LeafProofs.L14Aux

namespace Yau.LeafProofs.L14Aux

open BundleDbar Filter

theorem integral_wirt_wirtBar_compact {n : ℕ} (ψ : ComplexVector n → ℂ)
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ) (v : ComplexVector n) :
    (∫ z, wirt ψ z v ∂lebesgueC n) = 0 ∧ (∫ z, wirtBar ψ z v ∂lebesgueC n) = 0 := by
  have hbar (f : ComplexVector n → ℂ) (hf : ContDiff ℝ ∞ f) (hcf : HasCompactSupport f) :
      (∫ z, wirtBar f z v ∂lebesgueC n) = 0 := by
    have h1 (z : ComplexVector n) : wirtBar (fun _ : ComplexVector n => (1 : ℂ)) z v = 0 := by
      simp [wirtBar]
    have he : (0 : ℂ) = -(∫ z, wirtBar f z v ∂lebesgueC n) := by
      simpa only [h1, zero_mul, one_mul, integral_zero] using
        (integral_compactTest_wirtBar_on isOpen_univ hf hcf (Set.subset_univ _)
          (contDiffOn_const (c := (1 : ℂ))) v)
    exact neg_eq_zero.mp he.symm
  have hsc : HasCompactSupport (fun z => star (ψ z)) :=
    hc.of_isClosed_subset (isClosed_tsupport _) (tsupport_comp_subset (g := fun c : ℂ => star c) (by simp) ψ)
  have hsz := hbar (fun z => star (ψ z)) (Complex.conjCLE.contDiff.comp hψ) hsc
  constructor
  · calc
      _ = ∫ z, star (wirtBar (fun y => star (ψ y)) z v) ∂lebesgueC n :=
        integral_congr_ae (Eventually.of_forall fun z => by
          simpa only [star_star] using wirt_star (fun y => star (ψ y)) z v)
      _ = star (∫ z, wirtBar (fun y => star (ψ y)) z v ∂lebesgueC n) :=
        integral_conj (f := fun z => wirtBar (fun y => star (ψ y)) z v)
      _ = 0 := by rw [hsz, star_zero]
  · exact hbar ψ hψ hc

theorem tsupport_localChernD_subset {n r : ℕ}
    (H : ComplexVector n → Matrix (Fin r) (Fin r) ℂ) (v : ComplexVector n → Fin r → ℂ)
    (i : Fin n) (α : Fin r) : tsupport (fun z => localChernD H v i z α) ⊆ tsupport v := by
  apply closure_minimal _ (isClosed_tsupport v)
  intro z hz
  by_contra hn
  have hvz : v z = 0 := image_eq_zero_of_notMem_tsupport hn
  have hα : z ∉ tsupport (fun y => v y α) := fun h =>
    hn (tsupport_comp_subset (g := fun w : Fin r → ℂ => w α) (by rfl) v h)
  have hd : fderiv ℝ (fun y => v y α) z = 0 := fderiv_of_notMem_tsupport (𝕜 := ℝ) hα
  apply hz
  change wirt (fun y => v y α) z (stdVec i) +
    ∑ β, chernConnectionMatrix H z i α β * v z β = 0
  simp only [wirt, hd, ContinuousLinearMap.zero_apply, mul_zero, sub_zero, hvz,
    Pi.zero_apply, Finset.sum_const_zero, add_zero]

set_option backward.isDefEq.respectTransparency false in
theorem chern_pairing_second_order_integral {n r : ℕ} {O : Set (ComplexVector n)} (hO : IsOpen O)
    (H : ComplexVector n → Matrix (Fin r) (Fin r) ℂ)
    (u v : ComplexVector n → Fin r → ℂ)
    (hH : ∀ α β, ContDiffOn ℝ ∞ (fun y => H y α β) O)
    (hu : ∀ α, ContDiffOn ℝ ∞ (fun y => u y α) O)
    (hv : ContDiff ℝ ∞ v) (hc : HasCompactSupport v) (hs : tsupport v ⊆ O)
    (hdet : ∀ y ∈ O, (H y).det ≠ 0) (hHermitian : ∀ y ∈ O, (H y).IsHermitian)
    (i j : Fin n) :
    (∫ z in O, star (localChernD H u i z) ⬝ᵥ H z *ᵥ localChernD H v j z -
      star (fun α => wirtBar (fun y => u y α) z (stdVec j)) ⬝ᵥ H z *ᵥ
        (fun α => wirtBar (fun y => v y α) z (stdVec i)) -
          star (u z) ⬝ᵥ curvatureMatrix H z j i *ᵥ v z ∂lebesgueC n) = 0 := by
  let P := fun z => star (u z) ⬝ᵥ H z *ᵥ localChernD H v j z
  let Q := fun z => star (u z) ⬝ᵥ H z *ᵥ
    (fun α => wirtBar (fun y => v y α) z (stdVec i))
  have hvO (α : Fin r) : ContDiffOn ℝ ∞ (fun y => v y α) O := (contDiff_pi.mp hv α).contDiffOn
  have hB (α : Fin r) : ContDiffOn ℝ ∞
      (fun y => wirtBar (fun t => v t α) y (stdVec i)) O :=
    wirtBar_contDiffOn hO _ (hvO α) (stdVec i)
  have hPairSupport (w : ComplexVector n → Fin r → ℂ)
      (hws : ∀ α, tsupport (fun z => w z α) ⊆ tsupport v) :
      tsupport (fun z => star (u z) ⬝ᵥ H z *ᵥ w z) ⊆ tsupport v := by
    apply closure_minimal _ (isClosed_tsupport v)
    intro z hz
    by_contra hn
    have hwz : w z = 0 := funext (fun α =>
      image_eq_zero_of_notMem_tsupport (f := fun y => w y α) (fun h => hn (hws α h)))
    apply hz
    change star (u z) ⬝ᵥ H z *ᵥ w z = 0
    rw [hwz, Matrix.mulVec_zero, dotProduct_zero]
  have hPs : tsupport P ⊆ tsupport v := hPairSupport _ (fun α => tsupport_localChernD_subset H v j α)
  have hQs : tsupport Q ⊆ tsupport v := hPairSupport _ (fun α =>
    (closure_minimal (support_wirtBar_subset (fun y => v y α) (stdVec i)) (isClosed_tsupport _)).trans
      (tsupport_comp_subset (g := fun w : Fin r → ℂ => w α) (by rfl) v))
  have hPOn : ContDiffOn ℝ ∞ P O := by
    simp only [P, dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum]
    apply ContDiffOn.sum
    intro α _
    apply ContDiffOn.sum
    intro β _
    exact ((hu α).continuousLinearMap_comp (Complex.conjCLE : ℂ →L[ℝ] ℂ)).mul
      ((hH α β).mul (localChernD_contDiffOn hO H v hH hvO hdet j β))
  have hQOn : ContDiffOn ℝ ∞ Q O := by
    simp only [Q, dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum]
    apply ContDiffOn.sum
    intro α _
    apply ContDiffOn.sum
    intro β _
    exact ((hu α).continuousLinearMap_comp (Complex.conjCLE : ℂ →L[ℝ] ℂ)).mul ((hH α β).mul (hB β))
  have hP : ContDiff ℝ ∞ P := contDiff_of_contDiffOn_of_tsupport_subset hO P hPOn (hPs.trans hs)
  have hQ : ContDiff ℝ ∞ Q := contDiff_of_contDiffOn_of_tsupport_subset hO Q hQOn (hQs.trans hs)
  have hcP : HasCompactSupport P := hc.of_isClosed_subset (isClosed_tsupport _) hPs
  have hcQ : HasCompactSupport Q := hc.of_isClosed_subset (isClosed_tsupport _) hQs
  letI : IsLocallyFiniteMeasure (lebesgueC n) := by rw [lebesgueC_eq_volume]; infer_instance
  have hPb : Integrable (fun z => wirtBar P z (stdVec i)) (lebesgueC n) :=
    (wirtBar_contDiff P hP (stdVec i)).continuous.integrable_of_hasCompactSupport
      (wirtBar_hasCompactSupport P hcP (stdVec i))
  have hQwSmooth : ContDiff ℝ ∞ (fun z => wirt Q z (stdVec j)) := by
    simpa only [contDiffOn_univ] using wirt_contDiffOn isOpen_univ Q hQ.contDiffOn (stdVec j)
  have hQw : Integrable (fun z => wirt Q z (stdVec j)) (lebesgueC n) :=
    hQwSmooth.continuous.integrable_of_hasCompactSupport
      (hcQ.of_isClosed_subset (isClosed_tsupport _) (tsupport_wirt_subset Q (stdVec j)))
  have hlocal (z : ComplexVector n) (hz : z ∈ O) :
      star (localChernD H u i z) ⬝ᵥ H z *ᵥ localChernD H v j z -
        star (fun α => wirtBar (fun y => u y α) z (stdVec j)) ⬝ᵥ H z *ᵥ
          (fun α => wirtBar (fun y => v y α) z (stdVec i)) -
            star (u z) ⬝ᵥ curvatureMatrix H z j i *ᵥ v z =
        wirtBar P z (stdVec i) - wirt Q z (stdVec j) := by
    have he := chern_pairing_second_order_divergence hO H u v hH hu hvO hdet hHermitian z hz i j
    change _ = _ + wirtBar P z (stdVec i) - wirt Q z (stdVec j) at he
    linear_combination he
  have hout (z : ComplexVector n) (hz : z ∉ O) : wirtBar P z (stdVec i) - wirt Q z (stdVec j) = 0 := by
    have hPd : fderiv ℝ P z = 0 := fderiv_of_notMem_tsupport (𝕜 := ℝ) (fun h => hz (hs (hPs h)))
    have hQd : fderiv ℝ Q z = 0 := fderiv_of_notMem_tsupport (𝕜 := ℝ) (fun h => hz (hs (hQs h)))
    simp only [wirtBar, wirt, hPd, hQd, ContinuousLinearMap.zero_apply, mul_zero, add_zero, sub_zero]
  calc
    _ = ∫ z in O, wirtBar P z (stdVec i) - wirt Q z (stdVec j) ∂lebesgueC n :=
      setIntegral_congr_fun hO.measurableSet hlocal
    _ = ∫ z, wirtBar P z (stdVec i) - wirt Q z (stdVec j) ∂lebesgueC n :=
      setIntegral_eq_integral_of_forall_compl_eq_zero hout
    _ = (∫ z, wirtBar P z (stdVec i) ∂lebesgueC n) - ∫ z, wirt Q z (stdVec j) ∂lebesgueC n :=
      integral_sub hPb hQw
    _ = 0 := by
      rw [(integral_wirt_wirtBar_compact P hP hcP (stdVec i)).2,
        (integral_wirt_wirtBar_compact Q hQ hcQ (stdVec j)).1]
      ring

end Yau.LeafProofs.L14Aux

namespace Yau.LeafProofs.L14Aux

open BundleDbar

def loweredCurlMatrix {n : ℕ} (G D : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  D * Gᵀ - G * Dᵀ

theorem loweredCurl_trace_identity {n : ℕ} (G U V : Matrix (Fin n) (Fin n) ℂ)
    (hG : G.IsHermitian) (hunit : IsUnit G.det) :
    (1 / 2 : ℂ) *
      ((G⁻¹)ᵀ * (loweredCurlMatrix G U)ᴴ * G⁻¹ * loweredCurlMatrix G V).trace =
      (Uᴴ * G⁻¹ * V * Gᵀ).trace - (Uᵀᴴ * V).trace := by
  have hATG : (G⁻¹)ᵀ * Gᵀ = 1 := by
    rw [← Matrix.transpose_mul, Matrix.mul_nonsing_inv _ hunit, Matrix.transpose_one]
  have hGTA : Gᵀ * (G⁻¹)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, Matrix.nonsing_inv_mul _ hunit, Matrix.transpose_one]
  have hcancelAT (B : Matrix (Fin n) (Fin n) ℂ) : (G⁻¹)ᵀ * (Gᵀ * B) = B := by
    rw [← Matrix.mul_assoc, hATG, Matrix.one_mul]
  have hcancelGA (B : Matrix (Fin n) (Fin n) ℂ) : G * (G⁻¹ * B) = B :=
    Matrix.mul_nonsing_inv_cancel_left _ B hunit
  have hcancelAG (B : Matrix (Fin n) (Fin n) ℂ) : G⁻¹ * (G * B) = B :=
    Matrix.nonsing_inv_mul_cancel_left _ B hunit
  have hbar : (Uᵀᴴ)ᵀ = Uᴴ := by
    rw [Matrix.conjTranspose_transpose_eq_transpose_conjTranspose, Matrix.transpose_transpose]
  have hT2 : (Uᴴ * Vᵀ).trace = (Uᵀᴴ * V).trace := by
    simpa only [hbar] using Matrix.trace_transpose_mul (Uᵀᴴ) V
  have hT3 : ((G⁻¹)ᵀ * Uᵀᴴ * V * Gᵀ).trace = (Uᵀᴴ * V).trace := by
    calc
      _ = (Gᵀ * (G⁻¹)ᵀ * Uᵀᴴ * V).trace := by
        simpa only [Matrix.mul_assoc] using
          Matrix.trace_mul_cycle ((G⁻¹)ᵀ * Uᵀᴴ) V Gᵀ
      _ = _ := by rw [hGTA, Matrix.one_mul]
  have hT4 : ((G⁻¹)ᵀ * Uᵀᴴ * G * Vᵀ).trace = (Uᴴ * G⁻¹ * V * Gᵀ).trace := by
    calc
      _ = (((G⁻¹)ᵀ * Uᵀᴴ * G * Vᵀ)ᵀ).trace := (Matrix.trace_transpose _).symm
      _ = (V * Gᵀ * Uᴴ * G⁻¹).trace := by
        simp only [Matrix.transpose_mul, Matrix.transpose_transpose, hbar, Matrix.mul_assoc]
      _ = _ := by
        simpa only [Matrix.mul_assoc] using Matrix.trace_mul_comm (V * Gᵀ) (Uᴴ * G⁻¹)
  have he : ((G⁻¹)ᵀ * (loweredCurlMatrix G U)ᴴ * G⁻¹ * loweredCurlMatrix G V).trace =
      (Uᴴ * G⁻¹ * V * Gᵀ).trace - (Uᵀᴴ * V).trace -
        ((Uᵀᴴ * V).trace - (Uᴴ * G⁻¹ * V * Gᵀ).trace) := by
    simp only [loweredCurlMatrix, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul,
      hG.eq, hG.transpose.eq, Matrix.mul_sub, Matrix.sub_mul, Matrix.trace_sub]
    simp only [Matrix.mul_assoc, hcancelAT, hcancelGA, hcancelAG]
    simp only [← Matrix.mul_assoc]
    rw [hT2, hT3, hT4]
  rw [he]
  ring

end Yau.LeafProofs.L14Aux

namespace Yau.LeafProofs.L14Aux

theorem loweredCurlMatrix_apply {n : ℕ} (G D : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    loweredCurlMatrix G D i j = ∑ a, (G j a * D i a - G i a * D j a) := by
  simp only [loweredCurlMatrix, Matrix.sub_apply, Matrix.mul_apply, Matrix.transpose_apply]
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun a _ => by ring)

theorem loweredCurl_weighted_trace_identity {n r : ℕ}
    (G : Matrix (Fin n) (Fin n) ℂ) (H : Matrix (Fin r) (Fin r) ℂ)
    (D : Fin r → Matrix (Fin n) (Fin n) ℂ)
    (hG : G.IsHermitian) (hunit : IsUnit G.det) :
    (1 / 2 : ℂ) * ∑ α, ∑ β, H α β *
      ((G⁻¹)ᵀ * (loweredCurlMatrix G (D α))ᴴ * G⁻¹ * loweredCurlMatrix G (D β)).trace =
      (∑ α, ∑ β, H α β * ((D α)ᴴ * G⁻¹ * D β * Gᵀ).trace) -
        ∑ α, ∑ β, H α β * ((D α)ᵀᴴ * D β).trace := by
  simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro α _
  apply Finset.sum_congr rfl
  intro β _
  calc
    _ = H α β * ((1 / 2 : ℂ) *
        ((G⁻¹)ᵀ * (loweredCurlMatrix G (D α))ᴴ * G⁻¹ * loweredCurlMatrix G (D β)).trace) := by ring
    _ = _ := by rw [loweredCurl_trace_identity G (D α) (D β) hG hunit]; ring

end Yau.LeafProofs.L14Aux

namespace Yau.LeafProofs.L14Aux

open scoped Kronecker

theorem weighted_trace_remainder_eq_kronecker {n r : ℕ}
    (G : Matrix (Fin n) (Fin n) ℂ) (H : Matrix (Fin r) (Fin r) ℂ)
    (D : Fin r → Matrix (Fin n) (Fin n) ℂ) :
    (∑ α, ∑ β, H α β * ((D α)ᴴ * G⁻¹ * D β * Gᵀ).trace) =
      star (fun p : (Fin r × Fin n) × Fin n => D p.1.1 p.1.2 p.2) ⬝ᵥ
        ((H ⊗ₖ G⁻¹) ⊗ₖ G) *ᵥ (fun p : (Fin r × Fin n) × Fin n => D p.1.1 p.1.2 p.2) := by
  classical
  let e : (Fin r × Fin r × Fin n × Fin n × Fin n × Fin n) ≃
      (Fin r × Fin n × Fin n × Fin r × Fin n × Fin n) :=
    { toFun := fun ⟨α, β, a, b, k, i⟩ => (α, i, a, β, k, b)
      invFun := fun ⟨α, i, a, β, k, b⟩ => (α, β, a, b, k, i)
      left_inv := by rintro ⟨α, β, a, b, k, i⟩; rfl
      right_inv := by rintro ⟨α, i, a, β, k, b⟩; rfl }
  have hperm (f : Fin r → Fin r → Fin n → Fin n → Fin n → Fin n → ℂ) :
      (∑ α, ∑ β, ∑ a, ∑ b, ∑ k, ∑ i, f α β a b k i) =
        ∑ α, ∑ i, ∑ a, ∑ β, ∑ k, ∑ b, f α β a b k i := by
    simpa only [Fintype.sum_prod_type] using Fintype.sum_equiv e
      (fun p => f p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2)
      (fun p => f p.1 p.2.2.2.1 p.2.2.1 p.2.2.2.2.2 p.2.2.2.2.1 p.2.1)
      (by rintro ⟨α, β, a, b, k, i⟩; rfl)
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.transpose_apply, dotProduct, Matrix.mulVec, Matrix.kronecker_apply,
    Fintype.sum_prod_type, Pi.star_apply, Finset.mul_sum, Finset.sum_mul]
  rw [hperm]
  apply Finset.sum_congr rfl
  intro α _
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro β _
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem weighted_trace_remainder_nonneg {n r : ℕ}
    (G : Matrix (Fin n) (Fin n) ℂ) (H : Matrix (Fin r) (Fin r) ℂ)
    (hG : G.PosDef) (hH : H.PosDef) (D : Fin r → Matrix (Fin n) (Fin n) ℂ) :
    0 ≤ (∑ α, ∑ β, H α β * ((D α)ᴴ * G⁻¹ * D β * Gᵀ).trace).re := by
  rw [weighted_trace_remainder_eq_kronecker]
  exact (Complex.nonneg_iff.mp
    (((hH.kronecker hG.inv).kronecker hG).posSemidef.dotProduct_mulVec_nonneg _)).1

end Yau.LeafProofs.L14Aux

namespace Yau.LeafProofs.L14Aux

theorem trace_tensor_contraction {n : ℕ} (A U V : Matrix (Fin n) (Fin n) ℂ) :
    (Aᵀ * Uᴴ * A * V).trace =
      ∑ i, ∑ j, ∑ k, ∑ l, A i k * A j l * star (U i j) * V k l := by
  classical
  let e : (Fin n × Fin n × Fin n × Fin n) ≃ (Fin n × Fin n × Fin n × Fin n) :=
    { toFun := fun ⟨p, l, k, j⟩ => (k, j, l, p)
      invFun := fun ⟨i, j, k, l⟩ => (l, k, i, j)
      left_inv := by rintro ⟨p, l, k, j⟩; rfl
      right_inv := by rintro ⟨i, j, k, l⟩; rfl }
  have hperm (f : Fin n → Fin n → Fin n → Fin n → ℂ) :
      (∑ p, ∑ l, ∑ k, ∑ j, f p l k j) = ∑ i, ∑ j, ∑ k, ∑ l, f l k i j := by
    simpa only [Fintype.sum_prod_type] using Fintype.sum_equiv e
      (fun p => f p.1 p.2.1 p.2.2.1 p.2.2.2)
      (fun p => f p.2.2.2 p.2.2.1 p.1 p.2.1)
      (by rintro ⟨p, l, k, j⟩; rfl)
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.conjTranspose_apply, Finset.mul_sum, Finset.sum_mul]
  rw [hperm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  ring

theorem trace_cross_contraction {n : ℕ} (U V : Matrix (Fin n) (Fin n) ℂ) :
    (Uᵀᴴ * V).trace = ∑ i, ∑ j, star (U i j) * V j i := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.transpose_apply]

theorem loweredCurl_energy_identity {n r : ℕ}
    (G : Matrix (Fin n) (Fin n) ℂ) (H : Matrix (Fin r) (Fin r) ℂ)
    (D : Fin r → Matrix (Fin n) (Fin n) ℂ) (hG : G.IsHermitian) (hunit : IsUnit G.det) :
    (1 / 2 : ℂ) * (∑ α, ∑ β, ∑ i, ∑ j, ∑ k, ∑ l,
      H α β * G⁻¹ i k * G⁻¹ j l * star (loweredCurlMatrix G (D α) i j) *
        loweredCurlMatrix G (D β) k l) =
      (∑ α, ∑ β, H α β * ((D α)ᴴ * G⁻¹ * D β * Gᵀ).trace) -
        ∑ α, ∑ β, ∑ i, ∑ j, H α β * star (D α i j) * D β j i := by
  have he := loweredCurl_weighted_trace_identity G H D hG hunit
  have hB (α β : Fin r) := trace_tensor_contraction G⁻¹
    (loweredCurlMatrix G (D α)) (loweredCurlMatrix G (D β))
  have hC (α β : Fin r) := trace_cross_contraction (D α) (D β)
  simp only [hB, hC, Finset.mul_sum] at he
  simpa only [Finset.mul_sum, mul_assoc] using he

theorem loweredCurl_energy_decomposition {n r : ℕ}
    (G : Matrix (Fin n) (Fin n) ℂ) (H : Matrix (Fin r) (Fin r) ℂ)
    (D : Fin r → Matrix (Fin n) (Fin n) ℂ) (hG : G.PosDef) (hH : H.PosDef) :
    (((1 / 2 : ℂ) * (∑ α, ∑ β, ∑ i, ∑ j, ∑ k, ∑ l,
        H α β * G⁻¹ i k * G⁻¹ j l * star (loweredCurlMatrix G (D α) i j) *
          loweredCurlMatrix G (D β) k l)).re =
      (∑ α, ∑ β, H α β * ((D α)ᴴ * G⁻¹ * D β * Gᵀ).trace).re -
        (∑ α, ∑ β, ∑ i, ∑ j, H α β * star (D α i j) * D β j i).re) ∧
      0 ≤ (∑ α, ∑ β, H α β * ((D α)ᴴ * G⁻¹ * D β * Gᵀ).trace).re := by
  refine ⟨?_, weighted_trace_remainder_nonneg G H hG hH D⟩
  simpa only [Complex.sub_re] using congrArg Complex.re
    (loweredCurl_energy_identity G H D hG.isHermitian (hG.isUnit.map Matrix.detMonoidHom))

end Yau.LeafProofs.L14Aux

namespace Yau.LeafProofs.L14Aux

open BundleDbar

set_option backward.isDefEq.respectTransparency false in
theorem chartDbarMatrix_eq_loweredCurl {n r : ℕ} {M : ComplexManifold n}
    (g : Yau.SmoothMetric M) (a : M.Carrier)
    (F : ComplexVector n → Fin n → ComplexVector r) (hF : ContDiff ℝ ∞ F)
    (z : ComplexVector n) (hz : z ∈ chartTarget a) (α : Fin r) :
    (fun i j => wirtBar (fun y => F y j α) z (stdVec i) -
      wirtBar (fun y => F y i α) z (stdVec j)) =
      loweredCurlMatrix (hMat g.form a z)
        (fun i b => wirtBar (fun y => chartOneRaise g.form a F y b α) z (stdVec i)) := by
  ext i j
  have hCurl := loweredCurlMatrix_apply (hMat g.form a z)
    (Matrix.of fun i b => wirtBar (fun y => chartOneRaise g.form a F y b α) z (stdVec i)) i j
  exact (dbarCoefficients_chartOneRaise g a F hF z hz i j α).trans hCurl.symm

set_option backward.isDefEq.respectTransparency false in
theorem chartDbar_energy_decomposition {n r : ℕ} {M : ComplexManifold n}
    (g : Yau.SmoothMetric M) (a : M.Carrier)
    (F : ComplexVector n → Fin n → ComplexVector r) (hF : ContDiff ℝ ∞ F)
    (z : ComplexVector n) (hz : z ∈ chartTarget a)
    (H : Matrix (Fin r) (Fin r) ℂ) (hH : H.PosDef) :
    let G := hMat g.form a z
    let D : Fin r → Matrix (Fin n) (Fin n) ℂ := fun α i b =>
      wirtBar (fun y => chartOneRaise g.form a F y b α) z (stdVec i)
    let T : Fin r → Matrix (Fin n) (Fin n) ℂ := fun α i j =>
      wirtBar (fun y => F y j α) z (stdVec i) - wirtBar (fun y => F y i α) z (stdVec j)
    (((1 / 2 : ℂ) * (∑ α, ∑ β, ∑ i, ∑ j, ∑ k, ∑ l,
      H α β * G⁻¹ i k * G⁻¹ j l * star (T α i j) * T β k l)).re =
      (∑ α, ∑ β, H α β * ((D α)ᴴ * G⁻¹ * D β * Gᵀ).trace).re -
        (∑ α, ∑ β, ∑ i, ∑ j, H α β * star (D α i j) * D β j i).re) ∧
      0 ≤ (∑ α, ∑ β, H α β * ((D α)ᴴ * G⁻¹ * D β * Gᵀ).trace).re := by
  let G := hMat g.form a z
  let D : Fin r → Matrix (Fin n) (Fin n) ℂ := fun α i b =>
    wirtBar (fun y => chartOneRaise g.form a F y b α) z (stdVec i)
  let T : Fin r → Matrix (Fin n) (Fin n) ℂ := fun α i j =>
    wirtBar (fun y => F y j α) z (stdVec i) - wirtBar (fun y => F y i α) z (stdVec j)
  have hEq (α : Fin r) : loweredCurlMatrix G (D α) = T α :=
    (chartDbarMatrix_eq_loweredCurl g a F hF z hz α).symm
  have he := loweredCurl_energy_decomposition G H D (hMat_posDef g.form a z hz) hH
  simpa only [hEq] using he

end Yau.LeafProofs.L14Aux

namespace Yau.LeafProofs.L14Aux

open BundleDbar Filter

def weightedMetricMatrix {n r : ℕ} (H : ComplexVector n → Matrix (Fin r) (Fin r) ℂ)
    (f : ComplexVector n → ℝ) (z : ComplexVector n) : Matrix (Fin r) (Fin r) ℂ :=
  (Real.exp (-f z) : ℂ) • H z

theorem weightedMetricMatrix_det_isUnit {n r : ℕ}
    (H : ComplexVector n → Matrix (Fin r) (Fin r) ℂ) (f : ComplexVector n → ℝ)
    (z : ComplexVector n) (hH : IsUnit (H z).det) : IsUnit (weightedMetricMatrix H f z).det := by
  apply isUnit_iff_ne_zero.mpr
  rw [weightedMetricMatrix, Matrix.det_smul]
  exact mul_ne_zero (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _))) hH.ne_zero

set_option backward.isDefEq.respectTransparency false in
theorem wirt_real_exp_neg {n : ℕ} (f : ComplexVector n → ℝ)
    (z : ComplexVector n) (hf : DifferentiableAt ℝ f z) (v : ComplexVector n) :
    wirt (fun y => (Real.exp (-f y) : ℂ)) z v =
      -(Real.exp (-f z) : ℂ) * wirt (fun y => (f y : ℂ)) z v := by
  let F := fun y => (f y : ℂ)
  have hF : DifferentiableAt ℝ F z := Complex.ofRealCLM.differentiableAt.comp z hf
  have hExp := hF.hasFDerivAt.neg.cexp
  have hvalue (y : ComplexVector n) : Complex.exp (-F y) = (Real.exp (-f y) : ℂ) := by
    simpa only [F, Complex.ofReal_neg] using (Complex.ofReal_exp (-f y)).symm
  have hfun : (fun y => (Real.exp (-f y) : ℂ)) = (fun y => Complex.exp (-F y)) :=
    funext (fun y => (hvalue y).symm)
  rw [hfun]
  unfold wirt
  have hd : fderiv ℝ (fun y => Complex.exp (-F y)) z = Complex.exp (-F z) • -fderiv ℝ F z :=
    hExp.fderiv
  rw [hd]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.neg_apply, smul_eq_mul, hvalue]
  ring

set_option backward.isDefEq.respectTransparency false in
theorem chernConnection_weighted {n r : ℕ}
    (H : ComplexVector n → Matrix (Fin r) (Fin r) ℂ) (f : ComplexVector n → ℝ)
    (z : ComplexVector n) (hH : ∀ α β, DifferentiableAt ℝ (fun y => H y α β) z)
    (hf : DifferentiableAt ℝ f z) (hunit : IsUnit (H z).det) (i : Fin n) :
    chernConnectionMatrix (weightedMetricMatrix H f) z i =
      chernConnectionMatrix H z i - wirt (fun y => (f y : ℂ)) z (stdVec i) • 1 := by
  let K := weightedMetricMatrix H f
  let ρ : ℂ := Real.exp (-f z)
  let p := wirt (fun y => (f y : ℂ)) z (stdVec i)
  have hρ : DifferentiableAt ℝ (fun y => (Real.exp (-f y) : ℂ)) z :=
    Complex.ofRealCLM.differentiableAt.comp z hf.neg.exp
  have hunitK : IsUnit (K z).det := weightedMetricMatrix_det_isUnit H f z hunit
  have hDK : Matrix.of (fun α β => wirt (fun y => K y α β) z (stdVec i)) =
      ρ • (Matrix.of (fun α β => wirt (fun y => H y α β) z (stdVec i)) - p • H z) := by
    ext α β
    change wirt (fun y => (Real.exp (-f y) : ℂ) * H y α β) z (stdVec i) =
      ρ * (wirt (fun y => H y α β) z (stdVec i) - p * H z α β)
    rw [wirt_mul_rule (fun y => (Real.exp (-f y) : ℂ)) (fun y => H y α β)
      z (stdVec i) hρ (hH α β), wirt_real_exp_neg f z hf (stdVec i)]
    dsimp only [ρ, p]
    ring
  have hright : K z * (chernConnectionMatrix H z i - p • 1) =
      Matrix.of (fun α β => wirt (fun y => K y α β) z (stdVec i)) := by
    change (ρ • H z) * (chernConnectionMatrix H z i - p • 1) = _
    rw [Matrix.smul_mul, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one,
      chernConnection_lower H z hunit i]
    exact hDK.symm
  have he := congrArg (fun B : Matrix (Fin r) (Fin r) ℂ => (K z)⁻¹ * B)
    ((chernConnection_lower K z hunitK i).trans hright.symm)
  have hcancel (B : Matrix (Fin r) (Fin r) ℂ) : (K z)⁻¹ * (K z * B) = B :=
    Matrix.nonsing_inv_mul_cancel_left _ B hunitK
  simpa only [hcancel] using he

theorem wirtBar_sub_rule {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (f g : X → ℂ) (z v : X) (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) :
    wirtBar (fun y => f y - g y) z v = wirtBar f z v - wirtBar g z v := by
  unfold wirtBar
  rw [fderiv_fun_sub hf hg]
  simp only [ContinuousLinearMap.sub_apply]
  ring

set_option backward.isDefEq.respectTransparency false in
theorem curvatureMatrix_weighted {n r : ℕ} {O : Set (ComplexVector n)} (hO : IsOpen O)
    (H : ComplexVector n → Matrix (Fin r) (Fin r) ℂ) (f : ComplexVector n → ℝ)
    (hH : ∀ α β, ContDiffOn ℝ ∞ (fun y => H y α β) O)
    (hf : ContDiffOn ℝ ∞ f O) (hdet : ∀ y ∈ O, (H y).det ≠ 0)
    (z : ComplexVector n) (hz : z ∈ O) (i j : Fin n) :
    curvatureMatrix (weightedMetricMatrix H f) z i j = (Real.exp (-f z) : ℂ) •
      (curvatureMatrix H z i j + leviC f z j i • H z) := by
  let K := weightedMetricMatrix H f
  let F := fun y => (f y : ℂ)
  let p := fun y => wirt F y (stdVec i)
  have hFO : ContDiffOn ℝ ∞ F O := hf.continuousLinearMap_comp Complex.ofRealCLM
  have hp : DifferentiableAt ℝ p z :=
    ((wirt_contDiffOn hO F hFO (stdVec i)).contDiffAt (hO.mem_nhds hz)).differentiableAt (by simp)
  have hΓ (α β : Fin r) : DifferentiableAt ℝ
      (fun y => chernConnectionMatrix H y i α β) z :=
    ((chernConnectionMatrix_contDiffOn hO H hH hdet i α β).contDiffAt
      (hO.mem_nhds hz)).differentiableAt (by simp)
  have hEq (α β : Fin r) : (fun y => chernConnectionMatrix K y i α β) =ᶠ[𝓝 z]
      (fun y => chernConnectionMatrix H y i α β - p y * (1 : Matrix (Fin r) (Fin r) ℂ) α β) := by
    filter_upwards [hO.mem_nhds hz] with y hy
    exact congrArg (fun B : Matrix (Fin r) (Fin r) ℂ => B α β)
      (chernConnection_weighted H f y
        (fun γ δ => ((hH γ δ).contDiffAt (hO.mem_nhds hy)).differentiableAt (by simp))
        ((hf.contDiffAt (hO.mem_nhds hy)).differentiableAt (by simp))
        (isUnit_iff_ne_zero.mpr (hdet y hy)) i)
  have hbarp : wirtBar p z (stdVec j) = leviC f z j i := by
    change wirtBar (fun y => wirt F y (stdVec i)) z (stdVec j) =
      wirt (fun y => wirtBar F y (stdVec j)) z (stdVec i)
    exact (wirt_wirtBar_comm F z ((hFO.contDiffAt (hO.mem_nhds hz)).of_le (by norm_num))
      (stdVec j) (stdVec i)).symm
  have hbarΓ (α β : Fin r) : wirtBar (fun y => chernConnectionMatrix K y i α β) z (stdVec j) =
      wirtBar (fun y => chernConnectionMatrix H y i α β) z (stdVec j) -
        leviC f z j i * (1 : Matrix (Fin r) (Fin r) ℂ) α β := by
    calc
      _ = wirtBar (fun y => chernConnectionMatrix H y i α β -
          p y * (1 : Matrix (Fin r) (Fin r) ℂ) α β) z (stdVec j) := by
        unfold wirtBar
        rw [(hEq α β).fderiv_eq]
      _ = _ := by
        rw [wirtBar_sub_rule (fun y => chernConnectionMatrix H y i α β)
            (fun y => p y * (1 : Matrix (Fin r) (Fin r) ℂ) α β)
            z (stdVec j) (hΓ α β)
              (hp.mul (differentiableAt_const ((1 : Matrix (Fin r) (Fin r) ℂ) α β))),
          wirtBar_mul_rule p (fun _ => (1 : Matrix (Fin r) (Fin r) ℂ) α β)
            z (stdVec j) hp (differentiableAt_const ((1 : Matrix (Fin r) (Fin r) ℂ) α β)), hbarp]
        simp [wirtBar]
  have hbarMatrix : Matrix.of (fun α β => wirtBar
      (fun y => chernConnectionMatrix K y i α β) z (stdVec j)) =
      Matrix.of (fun α β => wirtBar (fun y => chernConnectionMatrix H y i α β) z (stdVec j)) -
        leviC f z j i • (1 : Matrix (Fin r) (Fin r) ℂ) := by
    ext α β
    exact hbarΓ α β
  unfold curvatureMatrix
  rw [hbarMatrix]
  change -(((Real.exp (-f z) : ℂ) • H z) *
    (Matrix.of (fun α β => wirtBar (fun y => chernConnectionMatrix H y i α β) z (stdVec j)) -
      leviC f z j i • 1)) = (Real.exp (-f z) : ℂ) •
      (-(H z * Matrix.of (fun α β => wirtBar (fun y => chernConnectionMatrix H y i α β) z (stdVec j))) +
        leviC f z j i • H z)
  rw [Matrix.smul_mul, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one]
  simp only [smul_sub, smul_add, smul_neg]
  abel

variable {n r : ℕ} {M : ComplexManifold n}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

theorem weightedMetricMatrix_curvature_inChart (h : Metric E)
    (hh : BundleDbar.SmoothMetric (r := r) E h) (φ : M.Carrier → ℝ) (hφ : SmoothFn φ)
    (a : M.Carrier) (z : ComplexVector n) (hz : z ∈ localDomain (r := r) E a) (i j : Fin n) :
    curvatureMatrix (weightedMetricMatrix (BundleDbar.metricMatrix (r := r) E h a) (inChart a φ)) z i j =
      (Real.exp (-inChart a φ z) : ℂ) • weightedCurvature (r := r) E h φ a z i j := by
  have hdet : ∀ y ∈ localDomain (r := r) E a,
      (BundleDbar.metricMatrix (r := r) E h a y).det ≠ 0 := fun y hy =>
    ((metricMatrix_posDef E h a y hy).isUnit.map Matrix.detMonoidHom).ne_zero
  exact curvatureMatrix_weighted (localDomain_isOpen E a)
    (BundleDbar.metricMatrix (r := r) E h a) (inChart a φ) (hh a)
    ((hφ a).mono Set.inter_subset_left) hdet z hz i j

end Yau.LeafProofs.L14Aux

namespace Yau.LeafProofs.L14Aux

open BundleDbar Filter

theorem metric_pairing_sum_sum {n r : ℕ} (H : Matrix (Fin r) (Fin r) ℂ)
    (U V : Fin n → Fin r → ℂ) :
    star (∑ i, U i) ⬝ᵥ H *ᵥ (∑ j, V j) =
      ∑ i, ∑ j, star (U i) ⬝ᵥ H *ᵥ V j := by
  rw [star_sum, Matrix.mulVec_sum, sum_dotProduct]
  exact Finset.sum_congr rfl (fun i _ => dotProduct_sum _ _ _)

theorem matrix_cross_pairing_sum {n r : ℕ} (H : Matrix (Fin r) (Fin r) ℂ)
    (D : Fin r → Matrix (Fin n) (Fin n) ℂ) :
    (∑ i, ∑ j, star (fun α => D α j i) ⬝ᵥ H *ᵥ (fun β => D β i j)) =
      ∑ α, ∑ β, H α β * ((D α)ᵀᴴ * D β).trace := by
  classical
  let e : (Fin n × Fin n × Fin r × Fin r) ≃ (Fin r × Fin r × Fin n × Fin n) :=
    { toFun := fun ⟨i, j, α, β⟩ => (α, β, j, i)
      invFun := fun ⟨α, β, p, q⟩ => (q, p, α, β)
      left_inv := by rintro ⟨i, j, α, β⟩; rfl
      right_inv := by rintro ⟨α, β, p, q⟩; rfl }
  have hperm (f : Fin n → Fin n → Fin r → Fin r → ℂ) :
      (∑ i, ∑ j, ∑ α, ∑ β, f i j α β) = ∑ α, ∑ β, ∑ p, ∑ q, f q p α β := by
    simpa only [Fintype.sum_prod_type] using Fintype.sum_equiv e
      (fun p => f p.1 p.2.1 p.2.2.1 p.2.2.2)
      (fun p => f p.2.2.2 p.2.2.1 p.1 p.2.1)
      (by rintro ⟨i, j, α, β⟩; rfl)
  simp only [dotProduct, Matrix.mulVec, Pi.star_apply, trace_cross_contraction, Finset.mul_sum]
  rw [hperm]
  apply Finset.sum_congr rfl
  intro α _
  apply Finset.sum_congr rfl
  intro β _
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  ring

theorem curvature_pairing_sum {n r : ℕ}
    (R : Fin n → Fin n → Matrix (Fin r) (Fin r) ℂ) (W : Fin n → Fin r → ℂ) :
    (∑ i, ∑ j, star (W i) ⬝ᵥ R j i *ᵥ W j) =
      ∑ i, ∑ j, ∑ α, ∑ β, R i j α β * star (W j α) * W i β := by
  rw [Finset.sum_comm]
  simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro α _
  apply Finset.sum_congr rfl
  intro β _
  ring

def localBarMatrix {n r : ℕ} (W : ComplexVector n → Fin n → Fin r → ℂ)
    (z : ComplexVector n) (α : Fin r) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => wirtBar (fun y => W y j α) z (stdVec i)

def localChernDivergence {n r : ℕ} (H : ComplexVector n → Matrix (Fin r) (Fin r) ℂ)
    (W : ComplexVector n → Fin n → Fin r → ℂ) (z : ComplexVector n) : Fin r → ℂ :=
  ∑ i, localChernD H (fun y => W y i) i z

set_option backward.isDefEq.respectTransparency false in
theorem chern_divergence_sum {n r : ℕ} {O : Set (ComplexVector n)} (hO : IsOpen O)
    (H : ComplexVector n → Matrix (Fin r) (Fin r) ℂ)
    (W : ComplexVector n → Fin n → Fin r → ℂ)
    (hH : ∀ α β, ContDiffOn ℝ ∞ (fun y => H y α β) O)
    (hW : ∀ i α, ContDiffOn ℝ ∞ (fun y => W y i α) O)
    (hdet : ∀ y ∈ O, (H y).det ≠ 0) (hHermitian : ∀ y ∈ O, (H y).IsHermitian)
    (z : ComplexVector n) (hz : z ∈ O) :
    star (localChernDivergence H W z) ⬝ᵥ H z *ᵥ localChernDivergence H W z -
      (∑ α, ∑ β, H z α β * ((localBarMatrix W z α)ᵀᴴ * localBarMatrix W z β).trace) -
      (∑ i, ∑ j, ∑ α, ∑ β, curvatureMatrix H z i j α β * star (W z j α) * W z i β) =
      ∑ i, ∑ j,
        (wirtBar (fun y => star (W y i) ⬝ᵥ H y *ᵥ localChernD H (fun t => W t j) j y) z (stdVec i) -
          wirt (fun y => star (W y i) ⬝ᵥ H y *ᵥ
            (fun α => wirtBar (fun t => W t j α) y (stdVec i))) z (stdVec j)) := by
  have hlocal (i j : Fin n) :
      star (localChernD H (fun y => W y i) i z) ⬝ᵥ H z *ᵥ localChernD H (fun y => W y j) j z -
        star (fun α => wirtBar (fun y => W y i α) z (stdVec j)) ⬝ᵥ H z *ᵥ
          (fun α => wirtBar (fun y => W y j α) z (stdVec i)) -
          star (W z i) ⬝ᵥ curvatureMatrix H z j i *ᵥ W z j =
      wirtBar (fun y => star (W y i) ⬝ᵥ H y *ᵥ localChernD H (fun t => W t j) j y) z (stdVec i) -
        wirt (fun y => star (W y i) ⬝ᵥ H y *ᵥ
          (fun α => wirtBar (fun t => W t j α) y (stdVec i))) z (stdVec j) := by
    have he := chern_pairing_second_order_divergence hO H
      (fun y => W y i) (fun y => W y j) hH (hW i) (hW j) hdet hHermitian z hz i j
    linear_combination he
  have hsum := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
    (fun i _ => Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl (fun j _ => hlocal i j))
  simp only [Finset.sum_sub_distrib] at hsum
  have hfirst := metric_pairing_sum_sum (H z)
    (fun i => localChernD H (fun y => W y i) i z) (fun j => localChernD H (fun y => W y j) j z)
  have hcross : (∑ i, ∑ j,
      star (fun α => wirtBar (fun y => W y i α) z (stdVec j)) ⬝ᵥ H z *ᵥ
        (fun α => wirtBar (fun y => W y j α) z (stdVec i))) =
      ∑ α, ∑ β, H z α β * ((localBarMatrix W z α)ᵀᴴ * localBarMatrix W z β).trace :=
    matrix_cross_pairing_sum (H z) (localBarMatrix W z)
  have hcurv := curvature_pairing_sum (curvatureMatrix H z) (W z)
  rw [← hfirst, hcross, hcurv] at hsum
  simpa only [localChernDivergence, Finset.sum_sub_distrib] using hsum

end Yau.LeafProofs.L14Aux

namespace Yau.LeafProofs.L14Aux

open BundleDbar

def localCurlMatrix {n r : ℕ} (F : ComplexVector n → Fin n → ComplexVector r)
    (z : ComplexVector n) (α : Fin r) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => wirtBar (fun y => F y j α) z (stdVec i) - wirtBar (fun y => F y i α) z (stdVec j)

def localCurlEnergy {n r : ℕ} (G : Matrix (Fin n) (Fin n) ℂ) (H : Matrix (Fin r) (Fin r) ℂ)
    (F : ComplexVector n → Fin n → ComplexVector r) (z : ComplexVector n) : ℝ :=
  ((1 / 2 : ℂ) * ∑ α, ∑ β, ∑ i, ∑ j, ∑ k, ∑ l,
    H α β * G⁻¹ i k * G⁻¹ j l * star (localCurlMatrix F z α i j) * localCurlMatrix F z β k l).re

def localPositiveEnergy {n r : ℕ} (G : Matrix (Fin n) (Fin n) ℂ) (H : Matrix (Fin r) (Fin r) ℂ)
    (W : ComplexVector n → Fin n → Fin r → ℂ) (z : ComplexVector n) : ℝ :=
  (∑ α, ∑ β, H α β * ((localBarMatrix W z α)ᴴ * G⁻¹ * localBarMatrix W z β * Gᵀ).trace).re

set_option backward.isDefEq.respectTransparency false in
theorem local_bkn_divergence {n r : ℕ} {M : ComplexManifold n}
    (g : Yau.SmoothMetric M) (a : M.Carrier) {O : Set (ComplexVector n)} (hO : IsOpen O)
    (hsub : O ⊆ chartTarget a) (H : ComplexVector n → Matrix (Fin r) (Fin r) ℂ)
    (F : ComplexVector n → Fin n → ComplexVector r) (hF : ContDiff ℝ ∞ F)
    (hH : ∀ α β, ContDiffOn ℝ ∞ (fun y => H y α β) O)
    (hPos : ∀ y ∈ O, (H y).PosDef) (z : ComplexVector n) (hz : z ∈ O) :
    let W := fun y i α => chartOneRaise g.form a F y i α
    let S := localChernDivergence H W z
    ((star S ⬝ᵥ H z *ᵥ S).re + localCurlEnergy (hMat g.form a z) (H z) F z =
      localPositiveEnergy (hMat g.form a z) (H z) W z +
        nakanoQuadratic (curvatureMatrix H z) (W z) +
        (∑ i, ∑ j,
          (wirtBar (fun y => star (W y i) ⬝ᵥ H y *ᵥ localChernD H (fun t => W t j) j y) z (stdVec i) -
            wirt (fun y => star (W y i) ⬝ᵥ H y *ᵥ
              (fun α => wirtBar (fun t => W t j α) y (stdVec i))) z (stdVec j))).re) ∧
      0 ≤ localPositiveEnergy (hMat g.form a z) (H z) W z := by
  let W := fun y i α => chartOneRaise g.form a F y i α
  have hW (i : Fin n) (α : Fin r) : ContDiffOn ℝ ∞ (fun y => W y i α) O :=
    (chartOneRaise_contDiffOn g a F hF i α).mono hsub
  have hdet : ∀ y ∈ O, (H y).det ≠ 0 := fun y hy =>
    ((hPos y hy).isUnit.map Matrix.detMonoidHom).ne_zero
  have hHerm : ∀ y ∈ O, (H y).IsHermitian := fun y hy => (hPos y hy).isHermitian
  have hsum := chern_divergence_sum hO H W hH hW hdet hHerm z hz
  have hr := congrArg Complex.re hsum
  simp only [Complex.sub_re] at hr
  change (star (localChernDivergence H W z) ⬝ᵥ H z *ᵥ localChernDivergence H W z).re -
      (∑ α, ∑ β, H z α β * ((localBarMatrix W z α)ᵀᴴ * localBarMatrix W z β).trace).re -
        nakanoQuadratic (curvatureMatrix H z) (W z) = _ at hr
  have hGeom := chartDbar_energy_decomposition g a F hF z (hsub hz) (H z) (hPos z hz)
  change (localCurlEnergy (hMat g.form a z) (H z) F z =
    localPositiveEnergy (hMat g.form a z) (H z) W z -
      (∑ α, ∑ β, ∑ i, ∑ j, H z α β * star (localBarMatrix W z α i j) *
        localBarMatrix W z β j i).re) ∧ 0 ≤ localPositiveEnergy (hMat g.form a z) (H z) W z at hGeom
  have hCross : (∑ α, ∑ β, H z α β * ((localBarMatrix W z α)ᵀᴴ * localBarMatrix W z β).trace) =
      ∑ α, ∑ β, ∑ i, ∑ j, H z α β * star (localBarMatrix W z α i j) * localBarMatrix W z β j i := by
    simp only [trace_cross_contraction, Finset.mul_sum, mul_assoc]
  rw [hCross] at hr
  refine ⟨?_, hGeom.2⟩
  linarith [hr, hGeom.1]

end Yau.LeafProofs.L14Aux

namespace Yau.LeafProofs.L14Aux

open BundleDbar

theorem weightedMetricMatrix_posDef {n r : ℕ}
    (H : ComplexVector n → Matrix (Fin r) (Fin r) ℂ) (f : ComplexVector n → ℝ)
    (z : ComplexVector n) (hH : (H z).PosDef) : (weightedMetricMatrix H f z).PosDef := by
  have hc : IsSelfAdjoint (Real.exp (-f z) : ℂ) := by
    change star (Real.exp (-f z) : ℂ) = (Real.exp (-f z) : ℂ)
    simp only [Complex.star_def, Complex.conj_ofReal]
  change ((Real.exp (-f z) : ℂ) • H z).PosDef
  apply Matrix.PosDef.of_dotProduct_mulVec_pos (hH.isHermitian.smul hc)
  intro v hv
  rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
  have hq := Complex.pos_iff.mp (hH.dotProduct_mulVec_pos hv)
  apply Complex.pos_iff.mpr
  constructor
  · simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] using
      mul_pos (Real.exp_pos (-f z)) hq.1
  · simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, ← hq.2, mul_zero]

theorem weightedMetricMatrix_contDiffOn {n r : ℕ} {O : Set (ComplexVector n)}
    (H : ComplexVector n → Matrix (Fin r) (Fin r) ℂ) (f : ComplexVector n → ℝ)
    (hH : ∀ α β, ContDiffOn ℝ ∞ (fun y => H y α β) O) (hf : ContDiffOn ℝ ∞ f O)
    (α β : Fin r) : ContDiffOn ℝ ∞ (fun y => weightedMetricMatrix H f y α β) O := by
  change ContDiffOn ℝ ∞ (fun y => (Real.exp (-f y) : ℂ) * H y α β) O
  exact ((hf.neg.exp).continuousLinearMap_comp Complex.ofRealCLM).mul (hH α β)

variable {n r : ℕ} {M : ComplexManifold n}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

set_option backward.isDefEq.respectTransparency false in
theorem weighted_local_bkn_divergence (g : Yau.SmoothMetric M)
    (h : Metric E) (hh : BundleDbar.SmoothMetric (r := r) E h) (φ : M.Carrier → ℝ) (hφ : SmoothFn φ)
    (a : M.Carrier) (F : ComplexVector n → Fin n → ComplexVector r) (hF : ContDiff ℝ ∞ F)
    (z : ComplexVector n) (hz : z ∈ localDomain (r := r) E a) :
    let K := weightedMetricMatrix (BundleDbar.metricMatrix (r := r) E h a) (inChart a φ)
    let W := fun y i α => chartOneRaise g.form a F y i α
    let S := localChernDivergence K W z
    ((star S ⬝ᵥ K z *ᵥ S).re + localCurlEnergy (hMat g.form a z) (K z) F z =
      localPositiveEnergy (hMat g.form a z) (K z) W z +
        Real.exp (-inChart a φ z) * nakanoQuadratic (weightedCurvature (r := r) E h φ a z) (W z) +
        (∑ i, ∑ j,
          (wirtBar (fun y => star (W y i) ⬝ᵥ K y *ᵥ localChernD K (fun t => W t j) j y) z (stdVec i) -
            wirt (fun y => star (W y i) ⬝ᵥ K y *ᵥ
              (fun α => wirtBar (fun t => W t j α) y (stdVec i))) z (stdVec j))).re) ∧
      0 ≤ localPositiveEnergy (hMat g.form a z) (K z) W z := by
  let K := weightedMetricMatrix (BundleDbar.metricMatrix (r := r) E h a) (inChart a φ)
  let W := fun y i α => chartOneRaise g.form a F y i α
  have hK (α β : Fin r) : ContDiffOn ℝ ∞ (fun y => K y α β) (localDomain (r := r) E a) :=
    weightedMetricMatrix_contDiffOn _ _ (hh a) ((hφ a).mono Set.inter_subset_left) α β
  have hKpos (y : ComplexVector n) (hy : y ∈ localDomain (r := r) E a) : (K y).PosDef :=
    weightedMetricMatrix_posDef _ _ y (metricMatrix_posDef E h a y hy)
  have he := local_bkn_divergence g a (localDomain_isOpen E a) Set.inter_subset_left
    K F hF hK hKpos z hz
  have hsum : (∑ i, ∑ j, ∑ α, ∑ β,
      curvatureMatrix K z i j α β * star (W z j α) * W z i β) =
      (Real.exp (-inChart a φ z) : ℂ) * ∑ i, ∑ j, ∑ α, ∑ β,
        weightedCurvature (r := r) E h φ a z i j α β * star (W z j α) * W z i β := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro α _
    apply Finset.sum_congr rfl
    intro β _
    have hc : curvatureMatrix K z i j α β = (Real.exp (-inChart a φ z) : ℂ) *
        weightedCurvature (r := r) E h φ a z i j α β :=
      congrArg (fun B : Matrix (Fin r) (Fin r) ℂ => B α β)
        (weightedMetricMatrix_curvature_inChart E h hh φ hφ a z hz i j)
    rw [hc]
    ring
  have hN : nakanoQuadratic (curvatureMatrix K z) (W z) =
      Real.exp (-inChart a φ z) * nakanoQuadratic (weightedCurvature (r := r) E h φ a z) (W z) := by
    simpa only [nakanoQuadratic, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      using congrArg Complex.re hsum
  dsimp only at he
  rw [hN] at he
  exact he

end Yau.LeafProofs.L14Aux

namespace Yau.LeafProofs.L14Aux

open BundleDbar

set_option backward.isDefEq.respectTransparency false in
theorem wirt_matrix_mulVec_eq_chern {n r : ℕ}
    (H : ComplexVector n → Matrix (Fin r) (Fin r) ℂ) (u : ComplexVector n → Fin r → ℂ)
    (z : ComplexVector n) (i : Fin n) (α : Fin r)
    (hH : ∀ γ β, DifferentiableAt ℝ (fun y => H y γ β) z)
    (hu : ∀ β, DifferentiableAt ℝ (fun y => u y β) z) (hunit : IsUnit (H z).det) :
    wirt (fun y => (H y *ᵥ u y) α) z (stdVec i) = (H z *ᵥ localChernD H u i z) α := by
  rw [localChernD_lower H u z hunit i]
  change wirt (fun y => ∑ β, H y α β * u y β) z (stdVec i) =
    (∑ β, H z α β * wirt (fun y => u y β) z (stdVec i)) +
      ∑ β, wirt (fun y => H y α β) z (stdVec i) * u z β
  rw [wirt_sum_fun Finset.univ (fun β y => H y α β * u y β) z (stdVec i)
    (fun β _ => (hH α β).mul (hu β))]
  have hterm (β : Fin r) := wirt_mul_rule (fun y => H y α β) (fun y => u y β)
    z (stdVec i) (hH α β) (hu β)
  simp only [hterm, Finset.sum_add_distrib]
  ring

variable {n r : ℕ} {M : ComplexManifold n}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

theorem chartOneDual_eq_weighted_raise (g : HermitianField M) (h : Metric E) (φ : M.Carrier → ℝ)
    (a : M.Carrier) (F : ComplexVector n → Fin n → ComplexVector r)
    (z : ComplexVector n) (i : Fin n) (α : Fin r) :
    chartOneDual (r := r) E g h φ a F z i α =
      (weightedMetricMatrix (BundleDbar.metricMatrix (r := r) E h a) (inChart a φ) z *ᵥ
        (fun β => chartOneRaise g a F z i β)) α := by
  change (Real.exp (-φ (chartInv a z)) : ℂ) * ∑ j, (hMat g a z)⁻¹ i j *
      ∑ β, BundleDbar.metricMatrix (r := r) E h a z α β * F z j β =
    ∑ β, ((Real.exp (-φ (chartInv a z)) : ℂ) * BundleDbar.metricMatrix (r := r) E h a z α β) *
      ∑ j, (hMat g a z)⁻¹ i j * F z j β
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro β _
  apply Finset.sum_congr rfl
  intro j _
  ring

set_option backward.isDefEq.respectTransparency false in
theorem chartDbarAdjoint_eq_neg_localChernDivergence (g : Yau.SmoothMetric M)
    (h : Metric E) (hh : BundleDbar.SmoothMetric (r := r) E h) (φ : M.Carrier → ℝ) (hφ : SmoothFn φ)
    (a : M.Carrier) (F : ComplexVector n → Fin n → ComplexVector r) (hF : ContDiff ℝ ∞ F)
    (z : ComplexVector n) (hz : z ∈ localDomain (r := r) E a) :
    (fun α => chartDbarAdjoint (r := r) E g.form h φ a F z α) =
      -localChernDivergence (weightedMetricMatrix (BundleDbar.metricMatrix (r := r) E h a) (inChart a φ))
        (fun y i α => chartOneRaise g.form a F y i α) z := by
  let K := weightedMetricMatrix (BundleDbar.metricMatrix (r := r) E h a) (inChart a φ)
  let W := fun y i α => chartOneRaise g.form a F y i α
  let S := localChernDivergence K W z
  have hunit : IsUnit (K z).det := weightedMetricMatrix_det_isUnit _ _ z
    ((metricMatrix_posDef E h a z hz).isUnit.map Matrix.detMonoidHom)
  have hKd (γ β : Fin r) : DifferentiableAt ℝ (fun y => K y γ β) z :=
    ((weightedMetricMatrix_contDiffOn _ _ (hh a) ((hφ a).mono Set.inter_subset_left) γ β).contDiffAt
      ((localDomain_isOpen E a).mem_nhds hz)).differentiableAt (by simp)
  have hWd (i : Fin n) (β : Fin r) : DifferentiableAt ℝ (fun y => W y i β) z :=
    ((chartOneRaise_contDiffOn g a F hF i β).contDiffAt
      ((isOpen_extChartAt_target (I := ComplexModel n) a).mem_nhds hz.1)).differentiableAt (by simp)
  have hDB (i : Fin n) (α : Fin r) :
      wirt (fun y => chartOneDual (r := r) E g.form h φ a F y i α) z (stdVec i) =
        (K z *ᵥ localChernD K (fun y => W y i) i z) α := by
    have hEq : (fun y => chartOneDual (r := r) E g.form h φ a F y i α) =
        (fun y => (K y *ᵥ W y i) α) :=
      funext (fun y => chartOneDual_eq_weighted_raise E g.form h φ a F y i α)
    exact (congrArg (fun f : ComplexVector n → ℂ => wirt f z (stdVec i)) hEq).trans
      (wirt_matrix_mulVec_eq_chern K (fun y => W y i) z i α hKd (hWd i) hunit)
  have hsum (α : Fin r) :
      (∑ i, wirt (fun y => chartOneDual (r := r) E g.form h φ a F y i α) z (stdVec i)) =
        (K z *ᵥ S) α := by
    simp only [S, localChernDivergence, Matrix.mulVec_sum, Finset.sum_apply]
    exact Finset.sum_congr rfl (fun i _ => hDB i α)
  have hvec : K z *ᵥ (fun α => chartDbarAdjoint (r := r) E g.form h φ a F z α) = K z *ᵥ -S := by
    funext α
    have hd := chartDbarAdjoint_dual E g.form h φ a F z hz α
    rw [hsum α] at hd
    have hlower : (K z *ᵥ (fun β => chartDbarAdjoint (r := r) E g.form h φ a F z β)) α =
        (∑ β, BundleDbar.metricMatrix (r := r) E h a z α β * chartDbarAdjoint (r := r) E g.form h φ a F z β) *
          (Real.exp (-φ (chartInv a z)) : ℂ) := by
      change (∑ β, ((Real.exp (-φ (chartInv a z)) : ℂ) * BundleDbar.metricMatrix (r := r) E h a z α β) *
        chartDbarAdjoint (r := r) E g.form h φ a F z β) = _
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl (fun β _ => by ring)
    rw [hlower, Matrix.mulVec_neg]
    exact hd
  have he := congrArg (fun U : Fin r → ℂ => (K z)⁻¹ *ᵥ U) hvec
  have hcancel (U : Fin r → ℂ) : (K z)⁻¹ *ᵥ (K z *ᵥ U) = U := by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hunit, Matrix.one_mulVec]
  simpa only [hcancel] using he

end Yau.LeafProofs.L14Aux

namespace Yau.LeafProofs.L14Aux

open BundleDbar

variable {n r : ℕ} {M : ComplexManifold n}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

set_option backward.isDefEq.respectTransparency false in
theorem weighted_local_bkn_adjoint_divergence (g : Yau.SmoothMetric M)
    (h : Metric E) (hh : BundleDbar.SmoothMetric (r := r) E h) (φ : M.Carrier → ℝ) (hφ : SmoothFn φ)
    (a : M.Carrier) (F : ComplexVector n → Fin n → ComplexVector r) (hF : ContDiff ℝ ∞ F)
    (z : ComplexVector n) (hz : z ∈ localDomain (r := r) E a) :
    let K := weightedMetricMatrix (BundleDbar.metricMatrix (r := r) E h a) (inChart a φ)
    let W := fun y i α => chartOneRaise g.form a F y i α
    let A := fun α => chartDbarAdjoint (r := r) E g.form h φ a F z α
    ((star A ⬝ᵥ K z *ᵥ A).re + localCurlEnergy (hMat g.form a z) (K z) F z =
      localPositiveEnergy (hMat g.form a z) (K z) W z +
        Real.exp (-inChart a φ z) * nakanoQuadratic (weightedCurvature (r := r) E h φ a z) (W z) +
        (∑ i, ∑ j,
          (wirtBar (fun y => star (W y i) ⬝ᵥ K y *ᵥ localChernD K (fun t => W t j) j y) z (stdVec i) -
            wirt (fun y => star (W y i) ⬝ᵥ K y *ᵥ
              (fun α => wirtBar (fun t => W t j α) y (stdVec i))) z (stdVec j))).re) ∧
      0 ≤ localPositiveEnergy (hMat g.form a z) (K z) W z := by
  let K := weightedMetricMatrix (BundleDbar.metricMatrix (r := r) E h a) (inChart a φ)
  let W := fun y i α => chartOneRaise g.form a F y i α
  let S := localChernDivergence K W z
  let A := fun α => chartDbarAdjoint (r := r) E g.form h φ a F z α
  have hδ : A = -S := chartDbarAdjoint_eq_neg_localChernDivergence E g h hh φ hφ a F hF z hz
  have hnorm : star A ⬝ᵥ K z *ᵥ A = star S ⬝ᵥ K z *ᵥ S := by
    rw [hδ]
    simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Pi.neg_apply, star_neg, mul_neg,
      Finset.sum_neg_distrib, neg_mul, neg_neg]
  have hb := weighted_local_bkn_divergence E g h hh φ hφ a F hF z hz
  dsimp only at hb
  rw [← congrArg Complex.re hnorm] at hb
  exact hb

end Yau.LeafProofs.L14Aux

namespace Yau.LeafProofs.L14Aux

open BundleDbar

theorem tsupport_matrix_pairing_right {n r : ℕ}
    (H : ComplexVector n → Matrix (Fin r) (Fin r) ℂ)
    (u v : ComplexVector n → Fin r → ℂ) :
    tsupport (fun z => star (u z) ⬝ᵥ H z *ᵥ v z) ⊆ tsupport v := by
  apply closure_minimal _ (isClosed_tsupport v)
  intro z hz
  by_contra hn
  have hv : v z = 0 := image_eq_zero_of_notMem_tsupport hn
  apply hz
  change star (u z) ⬝ᵥ H z *ᵥ v z = 0
  rw [hv, Matrix.mulVec_zero, dotProduct_zero]

theorem integrable_matrix_pairing_compact_right {n r : ℕ} {O : Set (ComplexVector n)} (hO : IsOpen O)
    (H : ComplexVector n → Matrix (Fin r) (Fin r) ℂ)
    (u v : ComplexVector n → Fin r → ℂ)
    (hH : ∀ α β, ContDiffOn ℝ ∞ (fun y => H y α β) O)
    (hu : ∀ α, ContDiffOn ℝ ∞ (fun y => u y α) O)
    (hv : ∀ α, ContDiffOn ℝ ∞ (fun y => v y α) O)
    (hc : HasCompactSupport v) (hs : tsupport v ⊆ O) :
    Integrable (fun z => star (u z) ⬝ᵥ H z *ᵥ v z) (lebesgueC n) := by
  let P := fun z => star (u z) ⬝ᵥ H z *ᵥ v z
  have hPOn : ContDiffOn ℝ ∞ P O := by
    simp only [P, dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum]
    apply ContDiffOn.sum
    intro α _
    apply ContDiffOn.sum
    intro β _
    exact ((hu α).continuousLinearMap_comp (Complex.conjCLE : ℂ →L[ℝ] ℂ)).mul ((hH α β).mul (hv β))
  have hPs : tsupport P ⊆ tsupport v := tsupport_matrix_pairing_right H u v
  have hP : ContDiff ℝ ∞ P := contDiff_of_contDiffOn_of_tsupport_subset hO P hPOn (hPs.trans hs)
  have hcP : HasCompactSupport P := hc.of_isClosed_subset (isClosed_tsupport _) hPs
  letI : IsLocallyFiniteMeasure (lebesgueC n) := by rw [lebesgueC_eq_volume]; infer_instance
  exact hP.continuous.integrable_of_hasCompactSupport hcP

theorem tsupport_localChernD_vector_subset {n r : ℕ}
    (H : ComplexVector n → Matrix (Fin r) (Fin r) ℂ) (v : ComplexVector n → Fin r → ℂ)
    (i : Fin n) : tsupport (fun z => localChernD H v i z) ⊆ tsupport v := by
  apply closure_minimal _ (isClosed_tsupport v)
  intro z hz
  by_contra hn
  apply hz
  change localChernD H v i z = 0
  funext α
  exact image_eq_zero_of_notMem_tsupport (f := fun y => localChernD H v i y α)
    (fun h => hn (tsupport_localChernD_subset H v i α h))

theorem tsupport_wirtBar_vector_subset {n r : ℕ} (v : ComplexVector n → Fin r → ℂ) (i : Fin n) :
    tsupport (fun z α => wirtBar (fun y => v y α) z (stdVec i)) ⊆ tsupport v := by
  apply closure_minimal _ (isClosed_tsupport v)
  intro z hz
  by_contra hn
  apply hz
  change (fun α => wirtBar (fun y => v y α) z (stdVec i)) = 0
  funext α
  have hα : z ∉ tsupport (fun y => v y α) := fun h =>
    hn (tsupport_comp_subset (g := fun w : Fin r → ℂ => w α) (by rfl) v h)
  have hd : fderiv ℝ (fun y => v y α) z = 0 := fderiv_of_notMem_tsupport (𝕜 := ℝ) hα
  simp only [wirtBar, hd, ContinuousLinearMap.zero_apply, mul_zero, add_zero, Pi.zero_apply]

set_option backward.isDefEq.respectTransparency false in
theorem chern_pairing_second_order_integrable {n r : ℕ} {O : Set (ComplexVector n)} (hO : IsOpen O)
    (H : ComplexVector n → Matrix (Fin r) (Fin r) ℂ)
    (u v : ComplexVector n → Fin r → ℂ)
    (hH : ∀ α β, ContDiffOn ℝ ∞ (fun y => H y α β) O)
    (hu : ∀ α, ContDiffOn ℝ ∞ (fun y => u y α) O)
    (hv : ∀ α, ContDiffOn ℝ ∞ (fun y => v y α) O)
    (hc : HasCompactSupport v) (hs : tsupport v ⊆ O) (hdet : ∀ y ∈ O, (H y).det ≠ 0)
    (i j : Fin n) :
    Integrable (fun z => star (localChernD H u i z) ⬝ᵥ H z *ᵥ localChernD H v j z -
      star (fun α => wirtBar (fun y => u y α) z (stdVec j)) ⬝ᵥ H z *ᵥ
        (fun α => wirtBar (fun y => v y α) z (stdVec i)) -
          star (u z) ⬝ᵥ curvatureMatrix H z j i *ᵥ v z) (lebesgueC n) := by
  have hD := tsupport_localChernD_vector_subset H v j
  have hB := tsupport_wirtBar_vector_subset v i
  have hfirst := integrable_matrix_pairing_compact_right hO H
    (fun y => localChernD H u i y) (fun y => localChernD H v j y) hH
    (fun α => localChernD_contDiffOn hO H u hH hu hdet i α)
    (fun α => localChernD_contDiffOn hO H v hH hv hdet j α)
    (hc.of_isClosed_subset (isClosed_tsupport _) hD) (hD.trans hs)
  have hcross := integrable_matrix_pairing_compact_right hO H
    (fun y α => wirtBar (fun t => u t α) y (stdVec j))
    (fun y α => wirtBar (fun t => v t α) y (stdVec i)) hH
    (fun α => wirtBar_contDiffOn hO _ (hu α) (stdVec j))
    (fun α => wirtBar_contDiffOn hO _ (hv α) (stdVec i))
    (hc.of_isClosed_subset (isClosed_tsupport _) hB) (hB.trans hs)
  have hcurv := integrable_matrix_pairing_compact_right hO (fun y => curvatureMatrix H y j i) u v
    (fun α β => curvatureMatrix_contDiffOn hO H hH hdet j i α β) hu hv hc hs
  exact (hfirst.sub hcross).sub hcurv

end Yau.LeafProofs.L14Aux

namespace Yau.LeafProofs.L14Aux

open BundleDbar

set_option backward.isDefEq.respectTransparency false in
theorem chern_divergence_integral {n r : ℕ} {O : Set (ComplexVector n)} (hO : IsOpen O)
    (H : ComplexVector n → Matrix (Fin r) (Fin r) ℂ)
    (W : ComplexVector n → Fin n → Fin r → ℂ)
    (hH : ∀ α β, ContDiffOn ℝ ∞ (fun y => H y α β) O)
    (hW : ContDiff ℝ ∞ W) (hc : HasCompactSupport W) (hs : tsupport W ⊆ O)
    (hdet : ∀ y ∈ O, (H y).det ≠ 0) (hHermitian : ∀ y ∈ O, (H y).IsHermitian) :
    Integrable (fun z => star (localChernDivergence H W z) ⬝ᵥ H z *ᵥ localChernDivergence H W z -
      (∑ α, ∑ β, H z α β * ((localBarMatrix W z α)ᵀᴴ * localBarMatrix W z β).trace) -
      (∑ i, ∑ j, ∑ α, ∑ β, curvatureMatrix H z i j α β * star (W z j α) * W z i β)) (lebesgueC n) ∧
    (∫ z, star (localChernDivergence H W z) ⬝ᵥ H z *ᵥ localChernDivergence H W z -
      (∑ α, ∑ β, H z α β * ((localBarMatrix W z α)ᵀᴴ * localBarMatrix W z β).trace) -
      (∑ i, ∑ j, ∑ α, ∑ β, curvatureMatrix H z i j α β * star (W z j α) * W z i β) ∂lebesgueC n) = 0 := by
  let N := fun z => star (localChernDivergence H W z) ⬝ᵥ H z *ᵥ localChernDivergence H W z -
    (∑ α, ∑ β, H z α β * ((localBarMatrix W z α)ᵀᴴ * localBarMatrix W z β).trace) -
    (∑ i, ∑ j, ∑ α, ∑ β, curvatureMatrix H z i j α β * star (W z j α) * W z i β)
  let Φ := fun i j z => star (localChernD H (fun y => W y i) i z) ⬝ᵥ H z *ᵥ
      localChernD H (fun y => W y j) j z -
    star (fun α => wirtBar (fun y => W y i α) z (stdVec j)) ⬝ᵥ H z *ᵥ
      (fun α => wirtBar (fun y => W y j α) z (stdVec i)) -
        star (W z i) ⬝ᵥ curvatureMatrix H z j i *ᵥ W z j
  have hWi (i : Fin n) : ContDiff ℝ ∞ (fun y => W y i) := (contDiff_pi.mp hW) i
  have hWiOn (i : Fin n) (α : Fin r) : ContDiffOn ℝ ∞ (fun y => W y i α) O :=
    ((contDiff_pi.mp (hWi i)) α).contDiffOn
  have hsWi (i : Fin n) : tsupport (fun y => W y i) ⊆ tsupport W :=
    tsupport_comp_subset (g := fun V : Fin n → Fin r → ℂ => V i) (by rfl) W
  have hcWi (i : Fin n) : HasCompactSupport (fun y => W y i) :=
    hc.of_isClosed_subset (isClosed_tsupport _) (hsWi i)
  have hΦInt (i j : Fin n) : Integrable (Φ i j) (lebesgueC n) :=
    chern_pairing_second_order_integrable hO H (fun y => W y i) (fun y => W y j)
      hH (hWiOn i) (hWiOn j) (hcWi j) ((hsWi j).trans hs) hdet i j
  have hΦOut (i j : Fin n) (z : ComplexVector n) (hz : z ∉ O) : Φ i j z = 0 := by
    have hzW : z ∉ tsupport (fun y => W y j) := fun h => hz (hs (hsWi j h))
    have hv0 : W z j = 0 := image_eq_zero_of_notMem_tsupport (f := fun y => W y j) hzW
    have hD0 : localChernD H (fun y => W y j) j z = 0 :=
      image_eq_zero_of_notMem_tsupport (f := fun y => localChernD H (fun t => W t j) j y)
        (fun h => hzW (tsupport_localChernD_vector_subset H (fun y => W y j) j h))
    have hB0 : (fun α => wirtBar (fun y => W y j α) z (stdVec i)) = 0 :=
      image_eq_zero_of_notMem_tsupport
        (f := fun y α => wirtBar (fun t => W t j α) y (stdVec i))
        (fun h => hzW (tsupport_wirtBar_vector_subset (fun y => W y j) i h))
    dsimp only [Φ]
    rw [hD0, hB0, hv0, Matrix.mulVec_zero, dotProduct_zero]
    simp only [Matrix.mulVec_zero, dotProduct_zero, sub_zero]
  have hΦZero (i j : Fin n) : (∫ z, Φ i j z ∂lebesgueC n) = 0 := by
    have hlocal : (∫ z in O, Φ i j z ∂lebesgueC n) = 0 :=
      chern_pairing_second_order_integral hO H (fun y => W y i) (fun y => W y j)
        hH (hWiOn i) (hWi j) (hcWi j) ((hsWi j).trans hs) hdet hHermitian i j
    exact (setIntegral_eq_integral_of_forall_compl_eq_zero (hΦOut i j)).symm.trans hlocal
  have hAlgebra (z : ComplexVector n) : N z = ∑ i, ∑ j, Φ i j z := by
    have hfirst := metric_pairing_sum_sum (H z)
      (fun i => localChernD H (fun y => W y i) i z) (fun j => localChernD H (fun y => W y j) j z)
    have hcross : (∑ i, ∑ j,
        star (fun α => wirtBar (fun y => W y i α) z (stdVec j)) ⬝ᵥ H z *ᵥ
          (fun α => wirtBar (fun y => W y j α) z (stdVec i))) =
        ∑ α, ∑ β, H z α β * ((localBarMatrix W z α)ᵀᴴ * localBarMatrix W z β).trace :=
      matrix_cross_pairing_sum (H z) (localBarMatrix W z)
    have hcurv := curvature_pairing_sum (curvatureMatrix H z) (W z)
    simp only [N, Φ, Finset.sum_sub_distrib]
    rw [← hfirst, hcross, hcurv]
    rfl
  have hsumInt : Integrable (fun z => ∑ i, ∑ j, Φ i j z) (lebesgueC n) :=
    integrable_finset_sum _ (fun i _ => integrable_finset_sum _ (fun j _ => hΦInt i j))
  change Integrable N (lebesgueC n) ∧ (∫ z, N z ∂lebesgueC n) = 0
  refine ⟨hsumInt.congr (ae_of_all _ (fun z => (hAlgebra z).symm)), ?_⟩
  calc
    _ = ∫ z, ∑ i, ∑ j, Φ i j z ∂lebesgueC n := integral_congr_ae (ae_of_all _ hAlgebra)
    _ = ∑ i, ∑ j, ∫ z, Φ i j z ∂lebesgueC n := by
      rw [integral_finset_sum _ (fun i _ => integrable_finset_sum _ (fun j _ => hΦInt i j))]
      exact Finset.sum_congr rfl (fun i _ => integral_finset_sum _ (fun j _ => hΦInt i j))
    _ = 0 := by simp only [hΦZero, Finset.sum_const_zero]

end Yau.LeafProofs.L14Aux

namespace Yau.LeafProofs.L14Aux

open BundleDbar

theorem tsupport_chartOneRaise_array_subset {n r : ℕ} {M : ComplexManifold n}
    (g : HermitianField M) (a : M.Carrier) (F : ComplexVector n → Fin n → ComplexVector r) :
    tsupport (fun y i α => chartOneRaise g a F y i α) ⊆ tsupport F := by
  apply closure_minimal _ (isClosed_tsupport F)
  intro z hz
  by_contra hn
  have hF : F z = 0 := image_eq_zero_of_notMem_tsupport hn
  apply hz
  change (fun i α => chartOneRaise g a F z i α) = 0
  funext i α
  change (∑ j, (hMat g a z)⁻¹ i j * F z j α) = 0
  rw [hF]
  simp only [Pi.zero_apply, PiLp.zero_apply, mul_zero, Finset.sum_const_zero]

set_option backward.isDefEq.respectTransparency false in
theorem chartOneRaise_array_contDiff {n r : ℕ} {M : ComplexManifold n}
    (g : Yau.SmoothMetric M) (a : M.Carrier)
    (F : ComplexVector n → Fin n → ComplexVector r) (hF : ContDiff ℝ ∞ F)
    (hs : tsupport F ⊆ chartTarget a) :
    ContDiff ℝ ∞ (fun y i α => chartOneRaise g.form a F y i α) := by
  apply contDiff_pi.mpr
  intro i
  apply contDiff_pi.mpr
  intro α
  apply contDiff_of_contDiffOn_of_tsupport_subset (isOpen_extChartAt_target (I := ComplexModel n) a) _
    (chartOneRaise_contDiffOn g a F hF i α)
  have heval : tsupport (fun y => chartOneRaise g.form a F y i α) ⊆
      tsupport (fun y i α => chartOneRaise g.form a F y i α) :=
    tsupport_comp_subset (g := fun V : Fin n → Fin r → ℂ => V i α) (by rfl)
      (fun y i α => chartOneRaise g.form a F y i α)
  exact (heval.trans (tsupport_chartOneRaise_array_subset g.form a F)).trans hs

end Yau.LeafProofs.L14Aux

namespace Yau.LeafProofs.L14Aux

open BundleDbar

variable {n r : ℕ} {M : ComplexManifold n}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

set_option backward.isDefEq.respectTransparency false in
theorem weighted_local_bkn_integral (g : Yau.SmoothMetric M)
    (h : Metric E) (hh : BundleDbar.SmoothMetric (r := r) E h) (φ : M.Carrier → ℝ) (hφ : SmoothFn φ)
    (a : M.Carrier) (F : ComplexVector n → Fin n → ComplexVector r) (hF : ContDiff ℝ ∞ F)
    (hc : HasCompactSupport F) (hs : tsupport F ⊆ localDomain (r := r) E a) :
    let K := weightedMetricMatrix (BundleDbar.metricMatrix (r := r) E h a) (inChart a φ)
    let W := fun y i α => chartOneRaise g.form a F y i α
    let A := fun y α => chartDbarAdjoint (r := r) E g.form h φ a F y α
    IntegrableOn (fun y => (star (A y) ⬝ᵥ K y *ᵥ A y).re + localCurlEnergy (hMat g.form a y) (K y) F y -
      localPositiveEnergy (hMat g.form a y) (K y) W y -
        Real.exp (-inChart a φ y) * nakanoQuadratic (weightedCurvature (r := r) E h φ a y) (W y))
      (localDomain (r := r) E a) (lebesgueC n) ∧
    (∫ y in localDomain (r := r) E a,
      (star (A y) ⬝ᵥ K y *ᵥ A y).re + localCurlEnergy (hMat g.form a y) (K y) F y -
      localPositiveEnergy (hMat g.form a y) (K y) W y -
        Real.exp (-inChart a φ y) * nakanoQuadratic (weightedCurvature (r := r) E h φ a y) (W y) ∂lebesgueC n) = 0 := by
  let O := localDomain (r := r) E a
  let K := weightedMetricMatrix (BundleDbar.metricMatrix (r := r) E h a) (inChart a φ)
  let W := fun y i α => chartOneRaise g.form a F y i α
  let A := fun y α => chartDbarAdjoint (r := r) E g.form h φ a F y α
  let N := fun y => star (localChernDivergence K W y) ⬝ᵥ K y *ᵥ localChernDivergence K W y -
    (∑ α, ∑ β, K y α β * ((localBarMatrix W y α)ᵀᴴ * localBarMatrix W y β).trace) -
    (∑ i, ∑ j, ∑ α, ∑ β, curvatureMatrix K y i j α β * star (W y j α) * W y i β)
  let J := fun y => (star (A y) ⬝ᵥ K y *ᵥ A y).re + localCurlEnergy (hMat g.form a y) (K y) F y -
    localPositiveEnergy (hMat g.form a y) (K y) W y -
      Real.exp (-inChart a φ y) * nakanoQuadratic (weightedCurvature (r := r) E h φ a y) (W y)
  have hO : IsOpen O := localDomain_isOpen E a
  have hWs : tsupport W ⊆ tsupport F := tsupport_chartOneRaise_array_subset g.form a F
  have hW : ContDiff ℝ ∞ W := chartOneRaise_array_contDiff g a F hF (hs.trans Set.inter_subset_left)
  have hcW : HasCompactSupport W := hc.of_isClosed_subset (isClosed_tsupport _) hWs
  have hsW : tsupport W ⊆ O := hWs.trans hs
  have hWOn (i : Fin n) (α : Fin r) : ContDiffOn ℝ ∞ (fun y => W y i α) O :=
    (contDiff_pi.mp (contDiff_pi.mp hW i) α).contDiffOn
  have hK (α β : Fin r) : ContDiffOn ℝ ∞ (fun y => K y α β) O :=
    weightedMetricMatrix_contDiffOn _ _ (hh a) ((hφ a).mono Set.inter_subset_left) α β
  have hPos (y : ComplexVector n) (hy : y ∈ O) : (K y).PosDef :=
    weightedMetricMatrix_posDef _ _ y (metricMatrix_posDef E h a y hy)
  have hdet : ∀ y ∈ O, (K y).det ≠ 0 := fun y hy =>
    ((hPos y hy).isUnit.map Matrix.detMonoidHom).ne_zero
  have hHerm : ∀ y ∈ O, (K y).IsHermitian := fun y hy => (hPos y hy).isHermitian
  have hBase : Integrable N (lebesgueC n) ∧ (∫ y, N y ∂lebesgueC n) = 0 :=
    chern_divergence_integral hO K W hK hW hcW hsW hdet hHerm
  have hEq (y : ComplexVector n) (hy : y ∈ O) : J y = (N y).re := by
    have ha := (weighted_local_bkn_adjoint_divergence E g h hh φ hφ a F hF y hy).1
    have hCh := congrArg Complex.re (chern_divergence_sum hO K W hK hWOn hdet hHerm y hy)
    change (N y).re = _ at hCh
    dsimp only at ha
    dsimp only [J]
    linarith [ha, hCh]
  have hEqAE : J =ᵐ[(lebesgueC n).restrict O] (fun y => (N y).re) := by
    filter_upwards [ae_restrict_mem hO.measurableSet] with y hy
    exact hEq y hy
  have hJInt : IntegrableOn J O (lebesgueC n) := hBase.1.re.integrableOn.congr hEqAE.symm
  have hNOut (y : ComplexVector n) (hy : y ∉ O) : N y = 0 := by
    have hout : y ∉ tsupport W := fun hw => hy (hsW hw)
    have hW0 : W y = 0 := image_eq_zero_of_notMem_tsupport hout
    have hd (i : Fin n) (α : Fin r) : fderiv ℝ (fun t => W t i α) y = 0 :=
      fderiv_of_notMem_tsupport (𝕜 := ℝ) (fun hw => hout
        (tsupport_comp_subset (g := fun V : Fin n → Fin r → ℂ => V i α) (by rfl) W hw))
    have hS0 : localChernDivergence K W y = 0 := by
      change (∑ i, localChernD K (fun t => W t i) i y) = 0
      apply Finset.sum_eq_zero
      intro i _
      funext α
      change wirt (fun t => W t i α) y (stdVec i) +
        (chernConnectionMatrix K y i *ᵥ W y i) α = 0
      rw [congrFun hW0 i]
      simp only [Pi.zero_apply, Matrix.mulVec_zero, wirt, hd, ContinuousLinearMap.zero_apply,
        mul_zero, sub_zero, add_zero]
    have hD0 (α : Fin r) : localBarMatrix W y α = 0 := by
      ext i j
      change wirtBar (fun t => W t j α) y (stdVec i) = 0
      simp only [wirtBar, hd, ContinuousLinearMap.zero_apply, mul_zero, add_zero]
    simp only [N, hS0, star_zero, Matrix.mulVec_zero, dotProduct_zero, hD0, Matrix.transpose_zero,
      Matrix.conjTranspose_zero, Matrix.zero_mul, Matrix.mul_zero, Matrix.trace_zero, hW0,
      Pi.zero_apply, mul_zero, zero_mul, Finset.sum_const_zero, sub_zero]
  have hFullZero : (∫ y, (N y).re ∂lebesgueC n) = 0 := by
    calc
      _ = (∫ y, N y ∂lebesgueC n).re := by
        simpa only [RCLike.re_eq_complex_re] using integral_re (𝕜 := ℂ) hBase.1
      _ = 0 := by rw [hBase.2, Complex.zero_re]
  have hLocalZero : (∫ y in O, (N y).re ∂lebesgueC n) = 0 :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy => by
      rw [hNOut y hy]
      exact Complex.zero_re)).trans hFullZero
  change IntegrableOn J O (lebesgueC n) ∧ (∫ y in O, J y ∂lebesgueC n) = 0
  exact ⟨hJInt, (integral_congr_ae hEqAE).trans hLocalZero⟩

end Yau.LeafProofs.L14Aux

namespace Yau.LeafProofs.L14Aux

open BundleDbar

theorem localCurlMatrix_contDiff {n r : ℕ} (F : ComplexVector n → Fin n → ComplexVector r)
    (hF : ContDiff ℝ ∞ F) (α : Fin r) (i j : Fin n) :
    ContDiff ℝ ∞ (fun y => localCurlMatrix F y α i j) := by
  exact (wirtBar_contDiff (fun y => F y j α) ((contDiff_piLp 2).mp (contDiff_pi.mp hF j) α) (stdVec i)).sub
    (wirtBar_contDiff (fun y => F y i α) ((contDiff_piLp 2).mp (contDiff_pi.mp hF i) α) (stdVec j))

theorem tsupport_localCurlMatrix_subset {n r : ℕ} (F : ComplexVector n → Fin n → ComplexVector r)
    (α : Fin r) (i j : Fin n) : tsupport (fun y => localCurlMatrix F y α i j) ⊆ tsupport F := by
  apply closure_minimal _ (isClosed_tsupport F)
  intro z hz
  by_contra hn
  have hd (p : Fin n) : fderiv ℝ (fun y => F y p α) z = 0 :=
    fderiv_of_notMem_tsupport (𝕜 := ℝ) (fun h => hn
      (tsupport_comp_subset (g := fun V : Fin n → ComplexVector r => V p α) (by rfl) F h))
  apply hz
  change wirtBar (fun y => F y j α) z (stdVec i) - wirtBar (fun y => F y i α) z (stdVec j) = 0
  simp only [wirtBar, hd, ContinuousLinearMap.zero_apply, mul_zero, add_zero, sub_zero]

set_option backward.isDefEq.respectTransparency false in
theorem localCurlEnergy_integrable {n r : ℕ} {M : ComplexManifold n}
    (g : Yau.SmoothMetric M) (a : M.Carrier) {O : Set (ComplexVector n)} (hO : IsOpen O)
    (hsub : O ⊆ chartTarget a) (H : ComplexVector n → Matrix (Fin r) (Fin r) ℂ)
    (hH : ∀ α β, ContDiffOn ℝ ∞ (fun y => H y α β) O)
    (F : ComplexVector n → Fin n → ComplexVector r) (hF : ContDiff ℝ ∞ F)
    (hc : HasCompactSupport F) (hs : tsupport F ⊆ O) :
    Integrable (fun y => localCurlEnergy (hMat g.form a y) (H y) F y) (lebesgueC n) := by
  let C := fun y => (1 / 2 : ℂ) * ∑ α, ∑ β, ∑ i, ∑ j, ∑ k, ∑ l,
    H y α β * (hMat g.form a y)⁻¹ i k * (hMat g.form a y)⁻¹ j l *
      star (localCurlMatrix F y α i j) * localCurlMatrix F y β k l
  have hCOn : ContDiffOn ℝ ∞ C O := by
    dsimp only [C]
    apply contDiffOn_const.mul
    apply ContDiffOn.sum
    intro α _
    apply ContDiffOn.sum
    intro β _
    apply ContDiffOn.sum
    intro i _
    apply ContDiffOn.sum
    intro j _
    apply ContDiffOn.sum
    intro k _
    apply ContDiffOn.sum
    intro l _
    exact ((((hH α β).mul ((L18Aux.hMat_inverse_contDiffOn g a i k).mono hsub)).mul
      ((L18Aux.hMat_inverse_contDiffOn g a j l).mono hsub)).mul
      ((localCurlMatrix_contDiff F hF α i j).contDiffOn.continuousLinearMap_comp
        (Complex.conjCLE : ℂ →L[ℝ] ℂ))).mul (localCurlMatrix_contDiff F hF β k l).contDiffOn
  have hCs : tsupport C ⊆ tsupport F := by
    apply closure_minimal _ (isClosed_tsupport F)
    intro y hy
    by_contra hn
    have hzero (α : Fin r) (i j : Fin n) : localCurlMatrix F y α i j = 0 :=
      image_eq_zero_of_notMem_tsupport (f := fun z => localCurlMatrix F z α i j)
        (fun h => hn (tsupport_localCurlMatrix_subset F α i j h))
    apply hy
    change (1 / 2 : ℂ) * ∑ α, ∑ β, ∑ i, ∑ j, ∑ k, ∑ l,
      H y α β * (hMat g.form a y)⁻¹ i k * (hMat g.form a y)⁻¹ j l *
        star (localCurlMatrix F y α i j) * localCurlMatrix F y β k l = 0
    simp only [hzero, star_zero, mul_zero, Finset.sum_const_zero]
  have hC : ContDiff ℝ ∞ C := contDiff_of_contDiffOn_of_tsupport_subset hO C hCOn (hCs.trans hs)
  have hcC : HasCompactSupport C := hc.of_isClosed_subset (isClosed_tsupport _) hCs
  letI : IsLocallyFiniteMeasure (lebesgueC n) := by rw [lebesgueC_eq_volume]; infer_instance
  exact (hC.continuous.integrable_of_hasCompactSupport hcC).re

end Yau.LeafProofs.L14Aux

namespace Yau.LeafProofs.L14Aux

open BundleDbar

variable {n r : ℕ} {M : ComplexManifold n}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

set_option backward.isDefEq.respectTransparency false in
theorem weighted_local_adjointEnergy_integrable (g : Yau.SmoothMetric M)
    (h : Metric E) (hh : BundleDbar.SmoothMetric (r := r) E h) (φ : M.Carrier → ℝ) (hφ : SmoothFn φ)
    (a : M.Carrier) (F : ComplexVector n → Fin n → ComplexVector r) (hF : ContDiff ℝ ∞ F)
    (hc : HasCompactSupport F) (hs : tsupport F ⊆ localDomain (r := r) E a) :
    let K := weightedMetricMatrix (BundleDbar.metricMatrix (r := r) E h a) (inChart a φ)
    let A := fun y α => chartDbarAdjoint (r := r) E g.form h φ a F y α
    Integrable (fun y => (star (A y) ⬝ᵥ K y *ᵥ A y).re) (lebesgueC n) := by
  let K := weightedMetricMatrix (BundleDbar.metricMatrix (r := r) E h a) (inChart a φ)
  let A := fun y α => chartDbarAdjoint (r := r) E g.form h φ a F y α
  have hδ := chartDbarAdjoint_contDiff E g h hh φ hφ a F hF hs
  have hAOn (α : Fin r) : ContDiffOn ℝ ∞ (fun y => A y α) (localDomain (r := r) E a) :=
    ((contDiff_piLp 2).mp hδ α).contDiffOn
  have hAs : tsupport A ⊆ tsupport F :=
    (tsupport_comp_subset (g := fun V : ComplexVector r => fun α => V α) (by rfl)
      (chartDbarAdjoint (r := r) E g.form h φ a F)).trans
        (tsupport_chartDbarAdjoint_subset E g.form h φ a F)
  have hK (α β : Fin r) : ContDiffOn ℝ ∞ (fun y => K y α β) (localDomain (r := r) E a) :=
    weightedMetricMatrix_contDiffOn _ _ (hh a) ((hφ a).mono Set.inter_subset_left) α β
  exact (integrable_matrix_pairing_compact_right (localDomain_isOpen E a) K A A hK hAOn hAOn
    (hc.of_isClosed_subset (isClosed_tsupport _) hAs) (hAs.trans hs)).re

set_option backward.isDefEq.respectTransparency false in
theorem weighted_local_curvatureEnergy_integrable (g : Yau.SmoothMetric M)
    (h : Metric E) (hh : BundleDbar.SmoothMetric (r := r) E h) (φ : M.Carrier → ℝ) (hφ : SmoothFn φ)
    (a : M.Carrier) (F : ComplexVector n → Fin n → ComplexVector r) (hF : ContDiff ℝ ∞ F)
    (hc : HasCompactSupport F) (hs : tsupport F ⊆ localDomain (r := r) E a) :
    let W := fun y i α => chartOneRaise g.form a F y i α
    Integrable (fun y => Real.exp (-inChart a φ y) *
      nakanoQuadratic (weightedCurvature (r := r) E h φ a y) (W y)) (lebesgueC n) := by
  let O := localDomain (r := r) E a
  let W := fun y i α => chartOneRaise g.form a F y i α
  let R := weightedCurvature (r := r) E h φ a
  let ρ := fun y => (Real.exp (-inChart a φ y) : ℂ)
  let P := fun y => ∑ i, ∑ j, star (W y j) ⬝ᵥ (ρ y • R y i j) *ᵥ W y i
  have hρ : ContDiffOn ℝ ∞ ρ O :=
    (((hφ a).neg.exp).continuousLinearMap_comp Complex.ofRealCLM).mono Set.inter_subset_left
  have hWOn (i : Fin n) (α : Fin r) : ContDiffOn ℝ ∞ (fun y => W y i α) O :=
    (chartOneRaise_contDiffOn g a F hF i α).mono Set.inter_subset_left
  have hWs (i : Fin n) : tsupport (fun y => W y i) ⊆ tsupport F :=
    (tsupport_comp_subset (g := fun V : Fin n → Fin r → ℂ => V i) (by rfl) W).trans
      (tsupport_chartOneRaise_array_subset g.form a F)
  have hmat (i j : Fin n) (α β : Fin r) : ContDiffOn ℝ ∞ (fun y => (ρ y • R y i j) α β) O :=
    hρ.mul (weightedCurvature_contDiffOn E h hh φ hφ a i j α β)
  have hP (i j : Fin n) : Integrable (fun y => star (W y j) ⬝ᵥ (ρ y • R y i j) *ᵥ W y i) (lebesgueC n) :=
    integrable_matrix_pairing_compact_right (localDomain_isOpen E a) (fun y => ρ y • R y i j)
      (fun y => W y j) (fun y => W y i) (hmat i j) (hWOn j) (hWOn i)
      (hc.of_isClosed_subset (isClosed_tsupport _) (hWs i)) ((hWs i).trans hs)
  have hSumInt : Integrable P (lebesgueC n) :=
    integrable_finset_sum _ (fun i _ => integrable_finset_sum _ (fun j _ => hP i j))
  have hcomplex (y : ComplexVector n) : P y = ρ y * ∑ i, ∑ j, ∑ α, ∑ β,
      R y i j α β * star (W y j α) * W y i β := by
    simp only [P, dotProduct, Matrix.mulVec, Pi.star_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro α _
    apply Finset.sum_congr rfl
    intro β _
    ring
  have hreal (y : ComplexVector n) : (P y).re = Real.exp (-inChart a φ y) * nakanoQuadratic (R y) (W y) := by
    simpa only [ρ, nakanoQuadratic, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      using congrArg Complex.re (hcomplex y)
  exact hSumInt.re.congr (ae_of_all _ hreal)

end Yau.LeafProofs.L14Aux

namespace Yau.LeafProofs.L14Aux

open BundleDbar

variable {n r : ℕ} {M : ComplexManifold n}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

set_option backward.isDefEq.respectTransparency false in
theorem weighted_local_bkn_estimate (g : Yau.SmoothMetric M)
    (h : Metric E) (hh : BundleDbar.SmoothMetric (r := r) E h) (φ : M.Carrier → ℝ) (hφ : SmoothFn φ)
    (a : M.Carrier) (F : ComplexVector n → Fin n → ComplexVector r) (hF : ContDiff ℝ ∞ F)
    (hc : HasCompactSupport F) (hs : tsupport F ⊆ localDomain (r := r) E a) :
    let K := weightedMetricMatrix (BundleDbar.metricMatrix (r := r) E h a) (inChart a φ)
    let W := fun y i α => chartOneRaise g.form a F y i α
    let A := fun y α => chartDbarAdjoint (r := r) E g.form h φ a F y α
    (∫ y in localDomain (r := r) E a, Real.exp (-inChart a φ y) *
      nakanoQuadratic (weightedCurvature (r := r) E h φ a y) (W y) ∂lebesgueC n) ≤
      (∫ y in localDomain (r := r) E a, (star (A y) ⬝ᵥ K y *ᵥ A y).re ∂lebesgueC n) +
        ∫ y in localDomain (r := r) E a, localCurlEnergy (hMat g.form a y) (K y) F y ∂lebesgueC n := by
  let O := localDomain (r := r) E a
  let K := weightedMetricMatrix (BundleDbar.metricMatrix (r := r) E h a) (inChart a φ)
  let W := fun y i α => chartOneRaise g.form a F y i α
  let A := fun y α => chartDbarAdjoint (r := r) E g.form h φ a F y α
  let P := fun y => (star (A y) ⬝ᵥ K y *ᵥ A y).re
  let B := fun y => localCurlEnergy (hMat g.form a y) (K y) F y
  let Q := fun y => localPositiveEnergy (hMat g.form a y) (K y) W y
  let N := fun y => Real.exp (-inChart a φ y) * nakanoQuadratic (weightedCurvature (r := r) E h φ a y) (W y)
  let J := fun y => P y + B y - Q y - N y
  have hO : IsOpen O := localDomain_isOpen E a
  have hK (α β : Fin r) : ContDiffOn ℝ ∞ (fun y => K y α β) O :=
    weightedMetricMatrix_contDiffOn _ _ (hh a) ((hφ a).mono Set.inter_subset_left) α β
  have hP : IntegrableOn P O (lebesgueC n) :=
    (weighted_local_adjointEnergy_integrable E g h hh φ hφ a F hF hc hs).integrableOn
  have hB : IntegrableOn B O (lebesgueC n) :=
    (localCurlEnergy_integrable g a hO Set.inter_subset_left K hK F hF hc hs).integrableOn
  have hN : IntegrableOn N O (lebesgueC n) :=
    (weighted_local_curvatureEnergy_integrable E g h hh φ hφ a F hF hc hs).integrableOn
  have hJ : IntegrableOn J O (lebesgueC n) ∧ (∫ y in O, J y ∂lebesgueC n) = 0 :=
    weighted_local_bkn_integral E g h hh φ hφ a F hF hc hs
  have hQ : IntegrableOn Q O (lebesgueC n) :=
    (((hP.add hB).sub hN).sub hJ.1).congr (ae_of_all _ (fun y => by
      change P y + B y - N y - (P y + B y - Q y - N y) = Q y
      ring))
  have hIntegral : (∫ y in O, J y ∂lebesgueC n) =
      ((∫ y in O, P y ∂lebesgueC n) + ∫ y in O, B y ∂lebesgueC n) -
        (∫ y in O, Q y ∂lebesgueC n) - ∫ y in O, N y ∂lebesgueC n := by
    change (∫ y in O, ((P + B - Q) - N) y ∂lebesgueC n) = _
    calc
      _ = (∫ y in O, (P + B - Q) y ∂lebesgueC n) -
          ∫ y in O, N y ∂lebesgueC n := integral_sub ((hP.add hB).sub hQ) hN
      _ = ((∫ y in O, (P + B) y ∂lebesgueC n) -
          ∫ y in O, Q y ∂lebesgueC n) - ∫ y in O, N y ∂lebesgueC n :=
        congrArg (fun t : ℝ => t - ∫ y in O, N y ∂lebesgueC n)
          (integral_sub (hP.add hB) hQ)
      _ = _ := congrArg (fun t : ℝ => t - (∫ y in O, Q y ∂lebesgueC n) -
          ∫ y in O, N y ∂lebesgueC n) (integral_add hP hB)
  have hQnonneg : 0 ≤ ∫ y in O, Q y ∂lebesgueC n := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem hO.measurableSet] with y hy
    exact (weighted_local_bkn_adjoint_divergence E g h hh φ hφ a F hF y hy).2
  change (∫ y in O, N y ∂lebesgueC n) ≤
    (∫ y in O, P y ∂lebesgueC n) + ∫ y in O, B y ∂lebesgueC n
  linarith [hIntegral, hJ.2, hQnonneg]

end Yau.LeafProofs.L14Aux

namespace Yau.LeafProofs.L14Aux

section AntiTwoContractionAlgebra
variable {V W ι : Type*} [AddCommGroup V] [Module ℂ V] [Module ℝ V]
  [AddCommGroup W] [Module ℂ W] [Module ℝ W] [Fintype ι] [DecidableEq ι]

def antiCoordinateSlice {q : ℕ} (A : V [⋀^Fin q]→ₗ[ℝ] W)
    (v : Fin q → V) (i : Fin q) : V [⋀^Fin 1]→ₗ[ℝ] W :=
  AlternatingMap.ofSubsingleton ℝ V W (0 : Fin 1) (A.toMultilinearMap.toLinearMap v i)

theorem antiCoordinateSlice_apply {q : ℕ} (A : V [⋀^Fin q]→ₗ[ℝ] W)
    (v : Fin q → V) (i : Fin q) (u : Fin 1 → V) :
    antiCoordinateSlice A v i u = A (Function.update v i (u 0)) := rfl

theorem antiCoordinateSlice_anti {q : ℕ} (A : V [⋀^Fin q]→ₗ[ℝ] W)
    (hA : ∀ (v : Fin q → V) (i : Fin q) (c : ℂ),
      A (Function.update v i (c • v i)) = star c • A v)
    (v : Fin q → V) (i : Fin q) (u : Fin 1 → V) (j : Fin 1) (c : ℂ) :
    antiCoordinateSlice A v i (Function.update u j (c • u j)) =
      star c • antiCoordinateSlice A v i u := by
  have hj : j = 0 := Subsingleton.elim _ _
  subst j
  simpa only [antiCoordinateSlice_apply, Function.update_self, Function.update_idem]
    using hA (Function.update v i (u 0)) i c

theorem antiCoordinateSlice_zero_apply (A : V [⋀^Fin 2]→ₗ[ℝ] W) (u v : V) :
    antiCoordinateSlice A ![0, v] 0 (fun _ => u) = A ![u, v] := by
  rw [antiCoordinateSlice_apply]
  congr 1
  ext k
  fin_cases k <;> simp

theorem antiCoordinateSlice_one_apply (A : V [⋀^Fin 2]→ₗ[ℝ] W) (u v : V) :
    antiCoordinateSlice A ![u, 0] 1 (fun _ => v) = A ![u, v] := by
  rw [antiCoordinateSlice_apply]
  congr 1
  ext k
  fin_cases k <;> simp

set_option backward.isDefEq.respectTransparency false in
theorem antiTwoContraction_basis_independent (hV : Yau.HermitianInnerProduct V)
    (hW : Yau.HermitianInnerProduct W) (A B : V [⋀^Fin 2]→ₗ[ℝ] W)
    (hA : ∀ (v : Fin 2 → V) (i : Fin 2) (c : ℂ),
      A (Function.update v i (c • v i)) = star c • A v)
    (hB : ∀ (v : Fin 2 → V) (i : Fin 2) (c : ℂ),
      B (Function.update v i (c • v i)) = star c • B v) (b c : Basis ι ℂ V) :
    (∑ i, ∑ k, ∑ j, ∑ l, (hermitianGram hV c)⁻¹ i k * (hermitianGram hV c)⁻¹ j l *
      hW.toFun (A ![c i, c j]) (B ![c k, c l])) =
    ∑ i, ∑ k, ∑ j, ∑ l, (hermitianGram hV b)⁻¹ i k * (hermitianGram hV b)⁻¹ j l *
      hW.toFun (A ![b i, b j]) (B ![b k, b l]) := by
  have hfirst (u v : V) :
      (∑ i, ∑ k, (hermitianGram hV c)⁻¹ i k * hW.toFun (A ![c i, u]) (B ![c k, v])) =
        ∑ i, ∑ k, (hermitianGram hV b)⁻¹ i k * hW.toFun (A ![b i, u]) (B ![b k, v]) := by
    simpa only [trace_inv_antiOneGram_eq_sum, antiCoordinateSlice_zero_apply] using
      antiOneContraction_basis_independent hV hW (antiCoordinateSlice A ![0,u] 0)
        (antiCoordinateSlice B ![0,v] 0) (antiCoordinateSlice_anti A hA _ _)
          (antiCoordinateSlice_anti B hB _ _) b c
  have hsecond (u v : V) :
      (∑ j, ∑ l, (hermitianGram hV c)⁻¹ j l * hW.toFun (A ![u, c j]) (B ![v, c l])) =
        ∑ j, ∑ l, (hermitianGram hV b)⁻¹ j l * hW.toFun (A ![u, b j]) (B ![v, b l]) := by
    simpa only [trace_inv_antiOneGram_eq_sum, antiCoordinateSlice_one_apply] using
      antiOneContraction_basis_independent hV hW (antiCoordinateSlice A ![u,0] 1)
        (antiCoordinateSlice B ![v,0] 1) (antiCoordinateSlice_anti A hA _ _)
          (antiCoordinateSlice_anti B hB _ _) b c
  have hswap (f : ι → ι → ι → ι → ℂ) :
      (∑ i, ∑ k, ∑ j, ∑ l, f i k j l) = ∑ j, ∑ l, ∑ i, ∑ k, f i k j l := by
    calc
      _ = ∑ p : ι × ι, ∑ q : ι × ι, f p.1 p.2 q.1 q.2 := by
        simp only [Fintype.sum_prod_type]
      _ = ∑ q : ι × ι, ∑ p : ι × ι, f p.1 p.2 q.1 q.2 := Finset.sum_comm
      _ = _ := by simp only [Fintype.sum_prod_type]
  calc
    _ = ∑ j, ∑ l, (hermitianGram hV c)⁻¹ j l *
        ∑ i, ∑ k, (hermitianGram hV c)⁻¹ i k * hW.toFun (A ![c i, c j]) (B ![c k, c l]) := by
      rw [hswap]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro l _
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = ∑ j, ∑ l, (hermitianGram hV c)⁻¹ j l *
        ∑ i, ∑ k, (hermitianGram hV b)⁻¹ i k * hW.toFun (A ![b i, c j]) (B ![b k, c l]) := by
      simp_rw [hfirst]
    _ = ∑ i, ∑ k, (hermitianGram hV b)⁻¹ i k *
        ∑ j, ∑ l, (hermitianGram hV c)⁻¹ j l * hW.toFun (A ![b i, c j]) (B ![b k, c l]) := by
      simp only [Finset.mul_sum]
      rw [hswap]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro l _
      ring
    _ = _ := by simp_rw [hsecond, Finset.mul_sum, mul_assoc]

end AntiTwoContractionAlgebra
end Yau.LeafProofs.L14Aux

namespace Yau.LeafProofs.L14Aux

open BundleDbar

section TwoFrameAlgebra
variable {V W ι κ : Type*} [AddCommGroup V] [Module ℂ V] [Module ℝ V]
  [AddCommGroup W] [Module ℂ W] [Module ℝ W] [IsScalarTower ℝ ℂ W]
  [Fintype ι] [DecidableEq ι]

def twoTensorHolEvaluation (A : V [⋀^Fin 2]→ₗ[ℝ] (V [⋀^ι]→ₗ[ℂ] W))
    (b : Basis ι ℂ V) : V [⋀^Fin 2]→ₗ[ℝ] W :=
  (alternatingEvaluationReal b).compAlternatingMap A

theorem twoTensorHolEvaluation_apply (A : V [⋀^Fin 2]→ₗ[ℝ] (V [⋀^ι]→ₗ[ℂ] W))
    (b : Basis ι ℂ V) (v : Fin 2 → V) : twoTensorHolEvaluation A b v = A v b := rfl

theorem twoTensorHolEvaluation_anti (A : V [⋀^Fin 2]→ₗ[ℝ] (V [⋀^ι]→ₗ[ℂ] W))
    (hA : ∀ (v : Fin 2 → V) (i : Fin 2) (c : ℂ),
      A (Function.update v i (c • v i)) = star c • A v) (b : Basis ι ℂ V)
    (v : Fin 2 → V) (i : Fin 2) (c : ℂ) :
    twoTensorHolEvaluation A b (Function.update v i (c • v i)) =
      star c • twoTensorHolEvaluation A b v :=
  congrArg (fun T : V [⋀^ι]→ₗ[ℂ] W => T b) (hA v i c)

def twoTensorFramePairing (hV : Yau.HermitianInnerProduct V) (hW : Yau.HermitianInnerProduct W)
    (hol anti : Basis ι ℂ V) (A B : V [⋀^Fin 2]→ₗ[ℝ] (V [⋀^ι]→ₗ[ℂ] W)) : ℂ :=
  (1 / 2 : ℂ) * ((hermitianGram hV hol).det.re : ℂ)⁻¹ *
    ∑ i, ∑ k, ∑ j, ∑ l, (hermitianGram hV anti)⁻¹ i k * (hermitianGram hV anti)⁻¹ j l *
      hW.toFun (twoTensorHolEvaluation A hol ![anti i, anti j])
        (twoTensorHolEvaluation B hol ![anti k, anti l])

theorem twoTensorFramePairing_eq_sum (hV : Yau.HermitianInnerProduct V)
    (hW : Yau.HermitianInnerProduct W) (hol anti : Basis ι ℂ V)
    (A B : V [⋀^Fin 2]→ₗ[ℝ] (V [⋀^ι]→ₗ[ℂ] W)) :
    twoTensorFramePairing hV hW hol anti A B = (1 / 2 : ℂ) *
      ∑ i, ∑ k, ∑ j, ∑ l, (hermitianGram hV anti)⁻¹ i k * (hermitianGram hV anti)⁻¹ j l *
        (hW.toFun (A ![anti i, anti j] hol) (B ![anti k, anti l] hol) /
          ((hermitianGram hV hol).det.re : ℂ)) := by
  unfold twoTensorFramePairing
  simp only [twoTensorHolEvaluation_apply]
  rw [mul_assoc]
  congr 1
  simp only [Finset.mul_sum, div_eq_mul_inv]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro l _
  ring

theorem twoTensorFramePairing_anti_basis_independent (hV : Yau.HermitianInnerProduct V)
    (hW : Yau.HermitianInnerProduct W) (hol b c : Basis ι ℂ V)
    (A B : V [⋀^Fin 2]→ₗ[ℝ] (V [⋀^ι]→ₗ[ℂ] W))
    (hA : ∀ (v : Fin 2 → V) (i : Fin 2) (s : ℂ),
      A (Function.update v i (s • v i)) = star s • A v)
    (hB : ∀ (v : Fin 2 → V) (i : Fin 2) (s : ℂ),
      B (Function.update v i (s • v i)) = star s • B v) :
    twoTensorFramePairing hV hW hol c A B = twoTensorFramePairing hV hW hol b A B := by
  unfold twoTensorFramePairing
  rw [antiTwoContraction_basis_independent hV hW _ _
    (twoTensorHolEvaluation_anti A hA hol) (twoTensorHolEvaluation_anti B hB hol) b c]

theorem twoTensorFramePairing_hol_basis_independent (d : Basis κ ℂ W)
    (hV : Yau.HermitianInnerProduct V) (hW : Yau.HermitianInnerProduct W)
    (b c anti : Basis ι ℂ V) (A B : V [⋀^Fin 2]→ₗ[ℝ] (V [⋀^ι]→ₗ[ℂ] W)) :
    twoTensorFramePairing hV hW c anti A B = twoTensorFramePairing hV hW b anti A B := by
  rw [twoTensorFramePairing_eq_sum, twoTensorFramePairing_eq_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro l _
  rw [alternating_hermitian_complex_ratio_basis_independent d hV hW b c]

theorem twoTensorFramePairing_basis_independent (d : Basis κ ℂ W)
    (hV : Yau.HermitianInnerProduct V) (hW : Yau.HermitianInnerProduct W)
    (b c : Basis ι ℂ V) (A B : V [⋀^Fin 2]→ₗ[ℝ] (V [⋀^ι]→ₗ[ℂ] W))
    (hA : ∀ (v : Fin 2 → V) (i : Fin 2) (s : ℂ),
      A (Function.update v i (s • v i)) = star s • A v)
    (hB : ∀ (v : Fin 2 → V) (i : Fin 2) (s : ℂ),
      B (Function.update v i (s • v i)) = star s • B v) :
    twoTensorFramePairing hV hW c c A B = twoTensorFramePairing hV hW b b A B := by
  calc
    _ = twoTensorFramePairing hV hW b c A B :=
      twoTensorFramePairing_hol_basis_independent d hV hW b c c A B
    _ = _ := twoTensorFramePairing_anti_basis_independent hV hW b b c A B hA hB

end TwoFrameAlgebra

variable {n r : ℕ} {M : ComplexManifold n}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

def twoFormPairing (g : HermitianField M) (h : Metric E) (u v : NQForm E 2) (x : M.Carrier) : ℂ :=
  twoTensorFramePairing (g x) (h x) (chartFrameBasis x x (mem_extChartAt_source x))
    (chartFrameBasis x x (mem_extChartAt_source x)) (u x).1 (v x).1

theorem twoFormPairing_in_fixed_chart (g : HermitianField M) (h : Metric E) (u v : NQForm E 2)
    (a x : M.Carrier) (hx : x ∈ (extChartAt (ComplexModel n) a).source) :
    twoFormPairing E g h u v x = twoTensorFramePairing (g x) (h x) (chartFrameBasis a x hx)
      (chartFrameBasis a x hx) (u x).1 (v x).1 :=
  twoTensorFramePairing_basis_independent (Module.Free.chooseBasis ℂ (E x))
    (g x) (h x) (chartFrameBasis a x hx) (chartFrameBasis x x (mem_extChartAt_source x))
    (u x).1 (v x).1 (u x).2 (v x).2

set_option backward.isDefEq.respectTransparency false in
theorem twoFormPairing_inChart (g : HermitianField M) (h : Metric E)
    (u v : NQForm E 2) (a : M.Carrier) (z : ComplexVector n) (hz : z ∈ localDomain (r := r) E a) :
    twoFormPairing E g h u v (chartInv a z) = (1 / 2 : ℂ) *
      ∑ i, ∑ k, ∑ j, ∑ l, (hMat g a z)⁻¹ i k * (hMat g a z)⁻¹ j l *
        ((∑ α, ∑ β, star (coefficients (r := r) E u a z ![i,j] α) *
          BundleDbar.metricMatrix (r := r) E h a z α β * coefficients (r := r) E v a z ![k,l] β) /
            ((hMat g a z).det.re : ℂ)) := by
  let x := chartInv a z
  let hx := (extChartAt (ComplexModel n) a).map_target hz.1
  let b := chartFrameBasis a x hx
  have hgram : hermitianGram (g x) b = hMat g a z := (frameGram_eq_hermitianGram g a x hx).symm
  have heval (s : NQForm E 2) (i j : Fin n) :
      ((s x).1 ![b i, b j]) b = ((s x).1
        (fun t => chartVec a x (stdVec (![i,j] t)))) (fun t => chartVec a x (stdVec t)) := by
    apply congrArg₂ (fun vv hh => ((s x).1 vv) hh)
    · ext t
      fin_cases t
      · exact chartFrameBasis_apply a x hx i
      · exact chartFrameBasis_apply a x hx j
    · exact funext (fun t => chartFrameBasis_apply a x hx t)
  calc
    _ = twoTensorFramePairing (g x) (h x) b b (u x).1 (v x).1 :=
      twoFormPairing_in_fixed_chart E g h u v a x hx
    _ = _ := by
      rw [twoTensorFramePairing_eq_sum, hgram]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro l _
      rw [heval u i j, heval v k l]
      exact congrArg (fun w : ℂ => (hMat g a z)⁻¹ i k * (hMat g a z)⁻¹ j l *
        (w / ((hMat g a z).det.re : ℂ))) (metricMatrix_pairing E h a z hz _ _).symm

end Yau.LeafProofs.L14Aux

namespace Yau.LeafProofs.L14Aux

open BundleDbar

theorem sum_fin_two_function {n : ℕ} {V : Type*} [AddCommMonoid V]
    (f : (Fin 2 → Fin n) → V) : (∑ I, f I) = ∑ i, ∑ j, f ![i,j] := by
  calc
    _ = ∑ p : Fin n × Fin n, f ![p.1,p.2] := by
      apply Fintype.sum_equiv (finTwoArrowEquiv (Fin n)) f (fun p => f ![p.1,p.2])
      intro I
      congr 1
      ext k
      fin_cases k <;> rfl
    _ = _ := Fintype.sum_prod_type _

variable {n r : ℕ} {M : ComplexManifold n}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

set_option backward.isDefEq.respectTransparency false in
theorem twoFormPairing_self_re (g : HermitianField M) (h : Metric E) (u : NQForm E 2)
    (x : M.Carrier) : (twoFormPairing E g h u u x).re = BundleDbar.formNormSq (r := r) E g h u x := by
  have hz : chartPt x x ∈ localDomain (r := r) E x := by
    refine ⟨mem_extChartAt_target x, ?_⟩
    change chartInv x (chartPt x x) ∈ (localTriv (r := r) E x).baseSet
    rw [chartInv_chartPt_of_mem x x (mem_chart_source _ _)]
    exact FiberBundle.mem_baseSet_trivializationAt' x
  let G := gMat g x
  let H := BundleDbar.metricMatrix (r := r) E h x (chartPt x x)
  let F := fun I α => coefficients (r := r) E u x (chartPt x x) I α
  let C : ℂ := ∑ i, ∑ k, ∑ j, ∑ l, G⁻¹ i k * G⁻¹ j l *
    ∑ α, ∑ β, star (F ![i,j] α) * H α β * F ![k,l] β
  have hp := congrArg (fun y => twoFormPairing E g h u u y)
    (chartInv_chartPt_of_mem x x (mem_chart_source _ _))
  have hs : twoFormPairing E g h u u x = (1 / 2 : ℂ) *
      ∑ i, ∑ k, ∑ j, ∑ l, G⁻¹ i k * G⁻¹ j l *
        ((∑ α, ∑ β, star (F ![i,j] α) * H α β * F ![k,l] β) / (G.det.re : ℂ)) :=
    hp.symm.trans (twoFormPairing_inChart E g h u u x (chartPt x x) hz)
  have hfactor : twoFormPairing E g h u u x = ((1 / 2 : ℂ) * (G.det.re : ℂ)⁻¹) * C := by
    rw [hs]
    dsimp only [C]
    simp only [div_eq_mul_inv, Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro l _
    apply Finset.sum_congr rfl
    intro α _
    apply Finset.sum_congr rfl
    intro β _
    ring
  have hC : (∑ I : Fin 2 → Fin n, ∑ J : Fin 2 → Fin n, ∑ α, ∑ β,
      star (F I α) * H α β * F J β * ∏ t, G⁻¹ (I t) (J t)) = C := by
    simp only [sum_fin_two_function, Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    dsimp only [C]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro l _
    apply Finset.sum_congr rfl
    intro α _
    apply Finset.sum_congr rfl
    intro β _
    ring
  rw [hfactor]
  have hReal (Z : ℂ) : (((1 / 2 : ℂ) * (G.det.re : ℂ)⁻¹) * Z).re =
      (1 / 2 : ℝ) * G.det.re⁻¹ * Z.re := by
    rw [← Complex.ofReal_inv]
    norm_num [Complex.mul_re]
  rw [hReal]
  change (1 / 2 : ℝ) * G.det.re⁻¹ * C.re =
    (Nat.factorial 2 : ℝ)⁻¹ * G⁻¹.det.re *
      (∑ I : Fin 2 → Fin n, ∑ J : Fin 2 → Fin n, ∑ α, ∑ β,
        star (F I α) * H α β * F J β * ∏ t, G⁻¹ (I t) (J t)).re
  rw [hC, show G⁻¹.det.re = G.det.re⁻¹ from gMat_inv_det_re g x]
  norm_num

theorem formNormSq_two_inChart (g : HermitianField M) (h : Metric E)
    (u : NQForm E 2) (a : M.Carrier) (z : ComplexVector n) (hz : z ∈ localDomain (r := r) E a) :
    BundleDbar.formNormSq (r := r) E g h u (chartInv a z) = ((1 / 2 : ℂ) *
      ∑ i, ∑ k, ∑ j, ∑ l, (hMat g a z)⁻¹ i k * (hMat g a z)⁻¹ j l *
        ((∑ α, ∑ β, star (coefficients (r := r) E u a z ![i,j] α) *
          BundleDbar.metricMatrix (r := r) E h a z α β * coefficients (r := r) E u a z ![k,l] β) /
            ((hMat g a z).det.re : ℂ))).re :=
  (twoFormPairing_self_re E g h u (chartInv a z)).symm.trans
    (congrArg Complex.re (twoFormPairing_inChart E g h u u a z hz))

end Yau.LeafProofs.L14Aux

namespace Yau.LeafProofs.L14Aux

open BundleDbar Filter

theorem wirtBar_wirtBar_comm {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (f : X → ℂ) (z : X) (hf : ContDiffAt ℝ 2 f z) (v w : X) :
    wirtBar (fun y => wirtBar f y v) z w = wirtBar (fun y => wirtBar f y w) z v := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) z :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hs := hf.isSymmSndFDerivAt (by norm_num)
  change (1 / 2 : ℂ) * (fderiv ℝ (fun y => wirtBar f y v) z w +
      Complex.I * fderiv ℝ (fun y => wirtBar f y v) z (Complex.I • w)) =
    (1 / 2 : ℂ) * (fderiv ℝ (fun y => wirtBar f y w) z v +
      Complex.I * fderiv ℝ (fun y => wirtBar f y w) z (Complex.I • v))
  rw [L18Aux.fderiv_wirtBar hd, L18Aux.fderiv_wirtBar hd,
    L18Aux.fderiv_wirtBar hd, L18Aux.fderiv_wirtBar hd,
    hs w v, hs w (Complex.I • v), hs (Complex.I • w) v, hs (Complex.I • w) (Complex.I • v)]
  ring


end Yau.LeafProofs.L14Aux

namespace Yau.LeafProofs.L14Aux

open BundleDbar Filter

variable {n r : ℕ} {M : ComplexManifold n}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

set_option backward.isDefEq.respectTransparency false in
theorem weakDbar_weaklyClosed_top (u : NQForm E 0) (f : NQForm E 1)
    (hD : WeakDbar (r := r) E u f) : WeaklyClosed (r := r) E f := by
  refine ⟨hD.2.1, ?_⟩
  intro a I α ψ hψ hc hs
  let i := I 0
  let j := I 1
  have htest (p q : Fin n) :
      (∫ z, coefficients (r := r) E f a z (fun _ => p) α * wirtBar ψ z (stdVec q) ∂lebesgueC n) =
        -∫ z, coefficients (r := r) E u a z Fin.elim0 α *
          wirtBar (fun y => wirtBar ψ y (stdVec q)) z (stdVec p) ∂lebesgueC n := by
    have hsupport : tsupport (fun z => wirtBar ψ z (stdVec q)) ⊆ localDomain (r := r) E a :=
      (closure_minimal (support_wirtBar_subset ψ (stdVec q)) isClosed_closure).trans hs
    have hw := hD.2.2 a (fun _ => p) α (fun z => wirtBar ψ z (stdVec q))
      (wirtBar_contDiff ψ hψ (stdVec q)) (wirtBar_hasCompactSupport ψ hc (stdVec q)) hsupport
    change (∫ z, coefficients (r := r) E f a z (fun _ => p) α *
      wirtBar ψ z (stdVec q) ∂lebesgueC n) =
        -∑ t : Fin 1, (-1 : ℂ) ^ t.val * ∫ z,
          coefficients (r := r) E u a z (fun _ : Fin 0 => p) α *
            wirtBar (fun y => wirtBar ψ y (stdVec q)) z (stdVec p) ∂lebesgueC n at hw
    have hEmpty : (fun _ : Fin 0 => p) = (Fin.elim0 : Fin 0 → Fin n) := Subsingleton.elim _ _
    simpa only [Fin.sum_univ_one, Fin.val_zero, pow_zero, one_mul, hEmpty] using hw
  have hdel0 : (fun t : Fin 1 => I ((0 : Fin 2).succAbove t)) = (fun _ => j) := by
    ext t
    have ht : t = 0 := Subsingleton.elim _ _
    subst t
    rfl
  have hdel1 : (fun t : Fin 1 => I ((1 : Fin 2).succAbove t)) = (fun _ => i) := by
    ext t
    have ht : t = 0 := Subsingleton.elim _ _
    subst t
    rfl
  have hcomm : (∫ z, coefficients (r := r) E u a z Fin.elim0 α *
      wirtBar (fun y => wirtBar ψ y (stdVec i)) z (stdVec j) ∂lebesgueC n) =
    ∫ z, coefficients (r := r) E u a z Fin.elim0 α *
      wirtBar (fun y => wirtBar ψ y (stdVec j)) z (stdVec i) ∂lebesgueC n := by
    apply integral_congr_ae
    exact ae_of_all _ (fun z => congrArg (fun c : ℂ => coefficients (r := r) E u a z Fin.elim0 α * c)
      (wirtBar_wirtBar_comm ψ z (hψ.contDiffAt.of_le (by norm_num)) (stdVec i) (stdVec j)))
  change (∑ t : Fin 2, (-1 : ℂ) ^ t.val * ∫ z,
    coefficients (r := r) E f a z (fun l => I (t.succAbove l)) α *
      wirtBar ψ z (stdVec (I t)) ∂lebesgueC n) = 0
  simp only [Fin.sum_univ_two, Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_mul, hdel0, hdel1]
  change (∫ z, coefficients (r := r) E f a z (fun _ => j) α * wirtBar ψ z (stdVec i) ∂lebesgueC n) +
    (-1 : ℂ) * (∫ z, coefficients (r := r) E f a z (fun _ => i) α * wirtBar ψ z (stdVec j) ∂lebesgueC n) = 0
  rw [htest j i, htest i j, hcomm]
  ring

end Yau.LeafProofs.L14Aux

namespace Yau.LeafProofs.L14Aux

open BundleDbar

variable {n r : ℕ} {M : ComplexManifold n}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

set_option backward.isDefEq.respectTransparency false in
theorem weightedMaximalDbar_apply_weaklyClosed
    (g : Yau.SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (h : Metric E) (hh : BundleDbar.SmoothMetric (r := r) E h) (φ : M.Carrier → ℝ) (hφ : SmoothFn φ)
    (u : (weightedMaximalDbar E g μ hμ h hh φ hφ).domain) :
    WeaklyClosed (r := r) E
      (weightedOneHilbertRepresentative E g μ hμ h hh φ hφ
        (weightedMaximalDbar E g μ hμ h hh φ hφ u)).1 := by
  let T := weightedMaximalDbar E g μ hμ h hh φ hφ
  have hG : ((u : WeightedTopHilbert E g μ hμ h hh φ hφ), T u) ∈
      weightedMaximalDbarHilbertGraph E g μ hμ h hh φ hφ := by
    rw [← weightedMaximalDbar_graph]
    exact T.mem_graph u
  have hD := (weightedMaximalDbarHilbertGraph_iff_representative E g μ hμ h hh φ hφ _ _).mp hG
  exact weakDbar_weaklyClosed_top E _ _ hD

end Yau.LeafProofs.L14Aux

namespace Yau.LeafProofs.L14Aux

open BundleDbar

section AntiCoordinateWedge
variable {V ι : Type*} [AddCommGroup V] [Module ℂ V] [Module ℝ V]
  [IsScalarTower ℝ ℂ V] [Fintype ι] [DecidableEq ι]

def antiCoordinateWedge (b : Basis ι ℂ V) (i j : ι) : V [⋀^Fin 2]→ₗ[ℝ] ℂ where
  toFun v := star (b.coord i (v 0)) * star (b.coord j (v 1)) -
    star (b.coord i (v 1)) * star (b.coord j (v 0))
  map_update_add' v k u w := by
    fin_cases k <;> simp [map_add, star_add] <;> ring
  map_update_smul' v k c u := by
    fin_cases k <;> simp [LinearMap.map_smul_of_tower, Complex.real_smul, star_mul] <;> ring
  map_eq_zero_of_eq' v k l h hne := by
    have heq : v 0 = v 1 := by
      fin_cases k <;> fin_cases l
      · exact False.elim (hne rfl)
      · exact h
      · exact h.symm
      · exact False.elim (hne rfl)
    simp only [heq, sub_self]

theorem antiCoordinateWedge_anti (b : Basis ι ℂ V) (i j : ι)
    (v : Fin 2 → V) (k : Fin 2) (c : ℂ) :
    antiCoordinateWedge b i j (Function.update v k (c • v k)) =
      star c * antiCoordinateWedge b i j v := by
  fin_cases k <;> simp [antiCoordinateWedge, map_smul, star_mul] <;> ring

theorem antiCoordinateWedge_basis (b : Basis ι ℂ V) (i j k l : ι) :
    antiCoordinateWedge b i j ![b k,b l] =
      (if i = k then 1 else 0) * (if j = l then 1 else 0) -
        (if i = l then 1 else 0) * (if j = k then 1 else 0) := by
  simp [antiCoordinateWedge, Basis.coord_apply, Finsupp.single_apply, eq_comm]

end AntiCoordinateWedge

variable {n r : ℕ} {M : ComplexManifold n}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

set_option backward.isDefEq.respectTransparency false in
def twoTensorFromCoefficients (a x : M.Carrier)
    (hx : x ∈ bundleChartSource (r := r) E a) (F : Fin n → Fin n → ComplexVector r) :
    antiComplexSubmodule E x 2 := by
  let b := chartFrameBasis a x hx.1
  let P := fun i j => b.det.smulRight ((localTriv (r := r) E a).symmL ℂ x (F i j))
  letI : IsScalarTower ℝ ℂ ((TangentVector M x) [⋀^Fin n]→ₗ[ℂ] E x) := ⟨by
    intro c d A
    ext v
    exact smul_assoc c d (A v)⟩
  let L := fun i j => (((LinearMap.id : ℂ →ₗ[ℂ] ℂ).smulRight (P i j)).restrictScalars ℝ).compAlternatingMap
    (antiCoordinateWedge b i j)
  refine ⟨(1 / 2 : ℂ) • ∑ i, ∑ j, L i j, ?_⟩
  intro v k c
  simp only [AlternatingMap.smul_apply, sum_apply]
  change (1 / 2 : ℂ) • (∑ i, ∑ j, antiCoordinateWedge b i j (Function.update v k (c • v k)) • P i j) =
    star c • ((1 / 2 : ℂ) • (∑ i, ∑ j, antiCoordinateWedge b i j v • P i j))
  simp_rw [antiCoordinateWedge_anti, mul_smul]
  calc
    _ = (1 / 2 : ℂ) • (star c • ∑ i, ∑ j, antiCoordinateWedge b i j v • P i j) := by
      simp only [Finset.smul_sum]
    _ = _ := smul_comm _ _ _

set_option backward.isDefEq.respectTransparency false in
theorem twoTensorFromCoefficients_basis (a x : M.Carrier)
    (hx : x ∈ bundleChartSource (r := r) E a) (F : Fin n → Fin n → ComplexVector r)
    (i j : Fin n) :
    ((twoTensorFromCoefficients (r := r) E a x hx F).1
      ![chartFrameBasis a x hx.1 i, chartFrameBasis a x hx.1 j]) (chartFrameBasis a x hx.1) =
      (1 / 2 : ℂ) • ((localTriv (r := r) E a).symmL ℂ x (F i j) -
        (localTriv (r := r) E a).symmL ℂ x (F j i)) := by
  simp only [twoTensorFromCoefficients, AlternatingMap.smul_apply, sum_apply,
    LinearMap.compAlternatingMap_apply, LinearMap.restrictScalars_apply, LinearMap.smulRight_apply,
    LinearMap.id_apply, AlternatingMap.smulRight_apply, Basis.det_self, one_smul,
    antiCoordinateWedge_basis, sub_smul, Finset.sum_sub_distrib]
  simp [Basis.det_self]

end Yau.LeafProofs.L14Aux

namespace Yau.LeafProofs.L14Aux

open BundleDbar

variable {n r : ℕ} {M : ComplexManifold n}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

set_option backward.isDefEq.respectTransparency false in
theorem twoTensorFromCoefficients_coordinate (a x : M.Carrier)
    (hx : x ∈ bundleChartSource (r := r) E a) (F : Fin n → Fin n → ComplexVector r)
    (hskew : ∀ i j, F j i = -F i j) (i j : Fin n) (α : Fin r) :
    (localTriv (r := r) E a).continuousLinearMapAt ℂ x
      (((twoTensorFromCoefficients (r := r) E a x hx F).1
        ![chartFrameBasis a x hx.1 i, chartFrameBasis a x hx.1 j]) (chartFrameBasis a x hx.1)) α = F i j α := by
  rw [twoTensorFromCoefficients_basis, hskew i j, map_neg, sub_neg_eq_add,
    ← two_smul ℂ _, smul_smul]
  norm_num only [one_div, inv_mul_cancel₀ (two_ne_zero : (2 : ℂ) ≠ 0), one_smul]
  rw [Trivialization.continuousLinearMapAt_symmL _ hx.2]

/-- A genuine `(n,2)` tensor, using the antisymmetric part of its local coefficient array. -/
def twoFormPushforward (a : M.Carrier)
    (F : ComplexVector n → Fin n → Fin n → ComplexVector r) : NQForm E 2 := by
  classical
  exact (show (∀ x, antiComplexSubmodule E x 2) from fun x =>
    if hx : x ∈ bundleChartSource (r := r) E a then
      twoTensorFromCoefficients (r := r) E a x hx (F (chartPt a x)) else 0)

set_option backward.isDefEq.respectTransparency false in
theorem twoFormPushforward_coefficients (a : M.Carrier)
    (F : ComplexVector n → Fin n → Fin n → ComplexVector r)
    (hskew : ∀ z i j, F z j i = -F z i j) (z : ComplexVector n)
    (hz : z ∈ localDomain (r := r) E a) (i j : Fin n) (α : Fin r) :
    coefficients (r := r) E (twoFormPushforward (r := r) E a F) a z ![i,j] α = F z i j α := by
  classical
  let y := chartInv a z
  have hy : y ∈ bundleChartSource (r := r) E a :=
    ⟨(extChartAt (ComplexModel n) a).map_target hz.1, hz.2⟩
  have hanti : (fun t : Fin 2 => chartVec a y (stdVec (![i,j] t))) =
      ![chartFrameBasis a y hy.1 i, chartFrameBasis a y hy.1 j] := by
    ext t
    fin_cases t
    · exact (chartFrameBasis_apply a y hy.1 i).symm
    · exact (chartFrameBasis_apply a y hy.1 j).symm
  have hhol : (fun t : Fin n => chartVec a y (stdVec t)) = chartFrameBasis a y hy.1 :=
    funext (fun t => (chartFrameBasis_apply a y hy.1 t).symm)
  change (localTriv (r := r) E a).continuousLinearMapAt ℂ y
    (((if hx : y ∈ bundleChartSource (r := r) E a then
        twoTensorFromCoefficients (r := r) E a y hx (F (chartPt a y)) else 0).1
      (fun t => chartVec a y (stdVec (![i,j] t)))) (fun t => chartVec a y (stdVec t))) α = _
  rw [dif_pos hy, hanti, hhol, twoTensorFromCoefficients_coordinate E a y hy _ (hskew _) i j α]
  exact congrArg (fun w => F w i j α) ((extChartAt (ComplexModel n) a).right_inv hz.1)

end Yau.LeafProofs.L14Aux

namespace Yau.LeafProofs.L14Aux

open BundleDbar

section AntiTwoBasisExpansion
variable {V W ι : Type*} [AddCommGroup V] [Module ℂ V] [Module ℝ V]
  [AddCommGroup W] [Module ℂ W] [Module ℝ W] [Fintype ι] [DecidableEq ι]

theorem antiTwo_apply_basis_expansion (b : Basis ι ℂ V)
    (A : V [⋀^Fin 2]→ₗ[ℝ] W)
    (hA : ∀ (v : Fin 2 → V) (i : Fin 2) (c : ℂ),
      A (Function.update v i (c • v i)) = star c • A v) (u v : V) :
    A ![u,v] = ∑ i, ∑ j, (star (b.repr u i) * star (b.repr v j)) • A ![b i,b j] := by
  have hfirst : A ![u,v] = ∑ i, star (b.repr u i) • A ![b i,v] := by
    simpa only [antiCoordinateSlice_zero_apply] using
      antiOne_apply_basis_expansion b (antiCoordinateSlice A ![0,v] 0)
        (antiCoordinateSlice_anti A hA _ _) u
  have hsecond (i : ι) : A ![b i,v] = ∑ j, star (b.repr v j) • A ![b i,b j] := by
    simpa only [antiCoordinateSlice_one_apply] using
      antiOne_apply_basis_expansion b (antiCoordinateSlice A ![b i,0] 1)
        (antiCoordinateSlice_anti A hA _ _) v
  rw [hfirst]
  simp only [hsecond, Finset.smul_sum, smul_smul]

end AntiTwoBasisExpansion

variable {n r : ℕ} {M : ComplexManifold n}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

set_option backward.isDefEq.respectTransparency false in
theorem twoTensorFromCoefficients_basis_skew (a x : M.Carrier)
    (hx : x ∈ bundleChartSource (r := r) E a) (F : Fin n → Fin n → ComplexVector r)
    (hskew : ∀ i j, F j i = -F i j) (i j : Fin n) :
    ((twoTensorFromCoefficients (r := r) E a x hx F).1
      ![chartFrameBasis a x hx.1 i, chartFrameBasis a x hx.1 j]) (chartFrameBasis a x hx.1) =
      (localTriv (r := r) E a).symmL ℂ x (F i j) := by
  rw [twoTensorFromCoefficients_basis, hskew i j, map_neg, sub_neg_eq_add,
    ← two_smul ℂ _, smul_smul]
  norm_num

set_option backward.isDefEq.respectTransparency false in
theorem twoTensorFromCoefficients_apply_basis (a x : M.Carrier)
    (hx : x ∈ bundleChartSource (r := r) E a) (F : Fin n → Fin n → ComplexVector r)
    (hskew : ∀ i j, F j i = -F i j) (u v : TangentVector M x)
    (c : Basis (Fin n) ℂ (TangentVector M x)) :
    ((twoTensorFromCoefficients (r := r) E a x hx F).1 ![u,v]) c =
      ((chartFrameBasis a x hx.1).toMatrix c).det •
        ∑ i, ∑ j, (star ((chartFrameBasis a x hx.1).coord i u) *
          star ((chartFrameBasis a x hx.1).coord j v)) • (localTriv (r := r) E a).symmL ℂ x (F i j) := by
  let A := twoTensorFromCoefficients (r := r) E a x hx F
  let b := chartFrameBasis a x hx.1
  have he := congrArg (fun P : (TangentVector M x) [⋀^Fin n]→ₗ[ℂ] E x => P c)
    (antiTwo_apply_basis_expansion b A.1 A.2 u v)
  simp only [sum_apply, AlternatingMap.smul_apply] at he
  rw [he]
  simp only [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have hvalue : (A.1 ![b i,b j]) c = (b.toMatrix c).det •
      (localTriv (r := r) E a).symmL ℂ x (F i j) :=
    (alternating_apply_basis_change (bundleFrameBasis (r := r) E a x hx.2) b c (A.1 ![b i,b j])).trans
      (congrArg (fun w : E x => (b.toMatrix c).det • w)
        (twoTensorFromCoefficients_basis_skew E a x hx F hskew i j))
  rw [hvalue]
  exact smul_comm _ _ _

set_option backward.isDefEq.respectTransparency false in
theorem twoFormPushforward_coefficients_inChart (a b : M.Carrier)
    (F : ComplexVector n → Fin n → Fin n → ComplexVector r)
    (hskew : ∀ z i j, F z j i = -F z i j) (z : ComplexVector n)
    (hz : z ∈ localDomain (r := r) E b) (hya : chartInv b z ∈ bundleChartSource (r := r) E a)
    (k l : Fin n) :
    coefficients (r := r) E (twoFormPushforward (r := r) E a F) b z ![k,l] =
      topBundleTransition (r := r) E a b z (∑ i, ∑ j,
        (star (fderiv ℂ (fun w => chartPt a (chartInv b w)) z (stdVec k) i) *
          star (fderiv ℂ (fun w => chartPt a (chartInv b w)) z (stdVec l) j)) •
            F (chartPt a (chartInv b z)) i j) := by
  classical
  let y := chartInv b z
  have hyb : y ∈ bundleChartSource (r := r) E b :=
    ⟨(extChartAt (ComplexModel n) b).map_target hz.1, hz.2⟩
  let d := chartFrameBasis b y hyb.1
  have hu : (twoFormPushforward (r := r) E a F y : antiComplexSubmodule E y 2) =
      twoTensorFromCoefficients (r := r) E a y hya (F (chartPt a y)) := by
    change (if hx : y ∈ bundleChartSource (r := r) E a then
      twoTensorFromCoefficients (r := r) E a y hx (F (chartPt a y)) else 0) = _
    exact dif_pos hya
  have hd : (fun t => chartVec b y (stdVec t)) = d :=
    funext (fun t => (chartFrameBasis_apply b y hyb.1 t).symm)
  have hanti : (fun t : Fin 2 => chartVec b y (stdVec (![k,l] t))) = ![d k,d l] := by
    ext t
    fin_cases t
    · exact (chartFrameBasis_apply b y hyb.1 k).symm
    · exact (chartFrameBasis_apply b y hyb.1 l).symm
  change (localTriv (r := r) E b).continuousLinearMapAt ℂ y
    (((twoFormPushforward (r := r) E a F y).1
      (fun t => chartVec b y (stdVec (![k,l] t)))) (fun t => chartVec b y (stdVec t))) = _
  rw [hd, hanti, hu, twoTensorFromCoefficients_apply_basis E a y hya _ (hskew _) _ _ d]
  simp_rw [chartFrameBasis_coord]
  have hj (p i : Fin n) : tangentCoords a y (d p) i =
      fderiv ℂ (fun w => chartPt a (chartInv b w)) z (stdVec p) i := by
    rw [show d p = chartVec b y (stdVec p) from chartFrameBasis_apply b y hyb.1 p]
    exact (congrArg (fun v : ComplexVector n => v i)
      (L18Aux.chartTransition_fderiv b a hz.1 hya.1 (stdVec p))).symm
  simp_rw [hj]
  rw [chartFrameBasis_toMatrix_fderiv a b z hz.1 hya.1, map_smul]
  unfold topBundleTransition
  simp only [ContinuousLinearMap.smul_apply]
  congr 1
  change (localTriv (r := r) E b).continuousLinearMapAt ℂ y
      (∑ i, ∑ j, (star (fderiv ℂ (fun w => chartPt a (chartInv b w)) z (stdVec k) i) *
        star (fderiv ℂ (fun w => chartPt a (chartInv b w)) z (stdVec l) j)) •
          (localTriv (r := r) E a).symmL ℂ y (F (chartPt a y) i j)) =
    (localTriv (r := r) E a).coordChangeL ℂ (localTriv (r := r) E b) y
      (∑ i, ∑ j, (star (fderiv ℂ (fun w => chartPt a (chartInv b w)) z (stdVec k) i) *
        star (fderiv ℂ (fun w => chartPt a (chartInv b w)) z (stdVec l) j)) • F (chartPt a y) i j)
  rw [bundleCoordChange_apply E a b y hya.2 hyb.2]
  congr 1
  simp only [map_sum, map_smul]

end Yau.LeafProofs.L14Aux

namespace Yau.LeafProofs.L14Aux

open BundleDbar Filter

variable {n r : ℕ} {M : ComplexManifold n}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

set_option backward.isDefEq.respectTransparency false in
theorem twoTensorFromCoefficients_zero (a x : M.Carrier)
    (hx : x ∈ bundleChartSource (r := r) E a) :
    twoTensorFromCoefficients (r := r) E a x hx 0 = 0 := by
  apply Subtype.ext
  apply AlternatingMap.ext
  intro v
  apply AlternatingMap.ext
  intro w
  simp [twoTensorFromCoefficients]

theorem twoFormPushforward_support (a : M.Carrier)
    (F : ComplexVector n → Fin n → Fin n → ComplexVector r)
    (hc : HasCompactSupport F) (hs : tsupport F ⊆ localDomain (r := r) E a) :
    closure {x | twoFormPushforward (r := r) E a F x ≠ (0 : NQForm E 2) x} ⊆ chartInv a '' tsupport F := by
  classical
  have hK : IsCompact (chartInv a '' tsupport F) := hc.image_of_continuousOn
    ((continuousOn_extChartAt_symm (I := ComplexModel n) a).mono (hs.trans Set.inter_subset_left))
  apply closure_minimal _ hK.isClosed
  intro x hx
  change twoFormPushforward (r := r) E a F x ≠ (0 : antiComplexSubmodule E x 2) at hx
  by_cases hxa : x ∈ bundleChartSource (r := r) E a
  · have hn : F (chartPt a x) ≠ 0 := by
      intro hf
      exact hx (by
        simp only [twoFormPushforward, dif_pos hxa, hf, twoTensorFromCoefficients_zero]
        rfl)
    exact ⟨chartPt a x, subset_closure hn,
      chartInv_chartPt_of_mem a x (by simpa only [extChartAt_source] using hxa.1)⟩
  · exact False.elim (hx (by
      simp only [twoFormPushforward, dif_neg hxa]
      rfl))

theorem twoFormPushforward_support_in_source (a : M.Carrier)
    (F : ComplexVector n → Fin n → Fin n → ComplexVector r)
    (hc : HasCompactSupport F) (hs : tsupport F ⊆ localDomain (r := r) E a) :
    closure {x | twoFormPushforward (r := r) E a F x ≠ (0 : NQForm E 2) x} ⊆ bundleChartSource (r := r) E a := by
  apply (twoFormPushforward_support E a F hc hs).trans
  rintro x ⟨z, hz, rfl⟩
  exact ⟨(extChartAt (ComplexModel n) a).map_target (hs hz).1, (hs hz).2⟩

set_option backward.isDefEq.respectTransparency false in
theorem twoFormPushforward_smooth (hE : Holomorphic (r := r) E)
    (a : M.Carrier) (F : ComplexVector n → Fin n → Fin n → ComplexVector r)
    (hskew : ∀ z i j, F z j i = -F z i j) (hF : ContDiff ℝ ∞ F)
    (hc : HasCompactSupport F) (hs : tsupport F ⊆ localDomain (r := r) E a) :
    SmoothForm (r := r) E (twoFormPushforward (r := r) E a F) := by
  classical
  letI : NormedAddCommGroup (ComplexVector r) := PiLp.normedAddCommGroup 2 (fun _ : Fin r => ℂ)
  letI : NormedSpace ℂ (ComplexVector r) := PiLp.normedSpace 2 ℂ (fun _ : Fin r => ℂ)
  letI : IsBoundedSMul ℂ (ComplexVector r) := NormedSpace.toIsBoundedSMul
  letI : ContinuousSMul ℂ (ComplexVector r) := IsBoundedSMul.continuousSMul
  intro b I α z hz
  let k := I 0
  let l := I 1
  have hI : I = ![k,l] := by ext t; fin_cases t <;> rfl
  rw [hI]
  have hi : ContinuousAt (chartInv b) z := continuousAt_extChartAt_symm'' (I := ComplexModel n) hz.1
  by_cases hya : chartInv b z ∈ bundleChartSource (r := r) E a
  · let T := fun w => chartPt a (chartInv b w)
    have hT := L18Aux.chartTransition_contDiffAt b a hz.1 hya.1
    have hD : ContDiffAt ℂ ∞ (fderiv ℂ T) z := hT.fderiv_right (m := ∞) (by simp)
    have hJ (p i : Fin n) : ContDiffAt ℝ ∞ (fun w => fderiv ℂ T w (stdVec p) i) z :=
      ((contDiffAt_piLp 2).mp (hD.clm_apply contDiffAt_const) i).restrict_scalars ℝ
    have hFT : ContDiffAt ℝ ∞ (fun w => F (T w)) z := hF.contDiffAt.comp z (hT.restrict_scalars ℝ)
    have hFij (i j : Fin n) : ContDiffAt ℝ ∞ (fun w => F (T w) i j) z :=
      contDiffAt_pi.mp (contDiffAt_pi.mp hFT i) j
    have hsum : ContDiffAt ℝ ∞ (fun w => ∑ i, ∑ j,
        (star (fderiv ℂ T w (stdVec k) i) * star (fderiv ℂ T w (stdVec l) j)) • F (T w) i j) z := by
      apply ContDiffAt.sum
      intro i _
      apply ContDiffAt.sum
      intro j _
      exact ((Complex.conjCLE.contDiff.contDiffAt.comp z (hJ k i)).mul
        (Complex.conjCLE.contDiff.contDiffAt.comp z (hJ l j))).smul (hFij i j)
    have hC := (topBundleTransition_contDiffAt E hE a b z hz hya).restrict_scalars ℝ
    have hCR : ContDiffAt ℝ ∞ (fun w => (topBundleTransition (r := r) E a b w).restrictScalars ℝ) z :=
      (ContinuousLinearMap.restrictScalarsL ℂ (ComplexVector r) (ComplexVector r) ℝ ℝ).contDiff.contDiffAt.comp z hC
    have hm := (contDiffAt_piLp 2).mp (hCR.clm_apply hsum) α
    have heq : (fun w => coefficients (r := r) E (twoFormPushforward (r := r) E a F) b w ![k,l] α) =ᶠ[𝓝 z]
        (fun w => topBundleTransition (r := r) E a b w (∑ i, ∑ j,
          (star (fderiv ℂ T w (stdVec k) i) * star (fderiv ℂ T w (stdVec l) j)) • F (T w) i j) α) := by
      filter_upwards [(localDomain_isOpen E b).mem_nhds hz,
        hi.tendsto.eventually ((bundleChartSource_isOpen (r := r) E a).mem_nhds hya)] with w hwb hwa
      exact congrArg (fun v : ComplexVector r => v α)
        (twoFormPushforward_coefficients_inChart E a b F hskew w hwb hwa k l)
    exact (hm.congr_of_eventuallyEq heq).contDiffWithinAt
  · let u := twoFormPushforward (r := r) E a F
    let K := closure {x | u x ≠ (0 : NQForm E 2) x}
    have hsource : K ⊆ bundleChartSource (r := r) E a := twoFormPushforward_support_in_source E a F hc hs
    have hout : chartInv b z ∉ K := fun h => hya (hsource h)
    have hzero : ∀ᶠ y in 𝓝 (chartInv b z), u y = (0 : NQForm E 2) y := by
      filter_upwards [isClosed_closure.compl_mem_nhds hout] with y hy
      by_contra hn
      exact hy (subset_closure hn)
    have heq : (fun w => coefficients (r := r) E u b w ![k,l] α) =ᶠ[𝓝 z] (fun _ => 0) := by
      filter_upwards [hi.tendsto.eventually hzero] with w hw
      have hcoeff : coefficients (r := r) E u b w ![k,l] α =
          coefficients (r := r) E (0 : NQForm E 2) b w ![k,l] α := by
        unfold coefficients
        rw [hw]
      exact hcoeff.trans (coefficients_zero E b w ![k,l] α)
    have hm : ContDiffAt ℝ ∞ (fun _ : ComplexVector n => (0 : ℂ)) z := contDiffAt_const
    exact (hm.congr_of_eventuallyEq heq).contDiffWithinAt

end Yau.LeafProofs.L14Aux

namespace Yau.LeafProofs.L14Aux

open BundleDbar

def modelOneDbar {n r : ℕ} (F : ComplexVector n → Fin n → ComplexVector r)
    (z : ComplexVector n) (i j : Fin n) : ComplexVector r :=
  WithLp.toLp 2 (fun α => localCurlMatrix F z α i j)

theorem modelOneDbar_skew {n r : ℕ} (F : ComplexVector n → Fin n → ComplexVector r)
    (z : ComplexVector n) (i j : Fin n) : modelOneDbar F z j i = -modelOneDbar F z i j := by
  ext α
  change wirtBar (fun y => F y i α) z (stdVec j) - wirtBar (fun y => F y j α) z (stdVec i) =
    -(wirtBar (fun y => F y j α) z (stdVec i) - wirtBar (fun y => F y i α) z (stdVec j))
  ring

theorem modelOneDbar_contDiff {n r : ℕ} (F : ComplexVector n → Fin n → ComplexVector r)
    (hF : ContDiff ℝ ∞ F) : ContDiff ℝ ∞ (modelOneDbar F) := by
  apply contDiff_pi.mpr
  intro i
  apply contDiff_pi.mpr
  intro j
  apply (contDiff_piLp 2).mpr
  intro α
  exact localCurlMatrix_contDiff F hF α i j

theorem tsupport_modelOneDbar_subset {n r : ℕ} (F : ComplexVector n → Fin n → ComplexVector r) :
    tsupport (modelOneDbar F) ⊆ tsupport F := by
  apply closure_minimal _ (isClosed_tsupport F)
  intro z hz
  by_contra hn
  apply hz
  funext i j
  ext α
  exact image_eq_zero_of_notMem_tsupport (f := fun y => localCurlMatrix F y α i j)
    (fun h => hn (tsupport_localCurlMatrix_subset F α i j h))

variable {n r : ℕ} {M : ComplexManifold n}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

theorem twoFormPushforward_modelOneDbar_smooth (hE : Holomorphic (r := r) E)
    (a : M.Carrier) (F : ComplexVector n → Fin n → ComplexVector r)
    (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    (hs : tsupport F ⊆ localDomain (r := r) E a) :
    SmoothForm (r := r) E (twoFormPushforward (r := r) E a (modelOneDbar F)) :=
  twoFormPushforward_smooth E hE a (modelOneDbar F) (modelOneDbar_skew F)
    (modelOneDbar_contDiff F hF)
    (hc.of_isClosed_subset (isClosed_tsupport _) (tsupport_modelOneDbar_subset F))
    ((tsupport_modelOneDbar_subset F).trans hs)

set_option backward.isDefEq.respectTransparency false in
theorem oneFormPushforward_dbar_coefficients_sameChart (a : M.Carrier)
    (F : ComplexVector n → Fin n → ComplexVector r) (z : ComplexVector n)
    (hz : z ∈ localDomain (r := r) E a) (i j : Fin n) (α : Fin r) :
    coefficients (r := r) E (twoFormPushforward (r := r) E a (modelOneDbar F)) a z ![i,j] α =
      dbarCoefficients (r := r) E (oneFormPushforward (r := r) E a F) a z ![i,j] α := by
  rw [twoFormPushforward_coefficients E a _ (modelOneDbar_skew F) z hz i j α]
  have hEq (k : Fin n) : (fun w => coefficients (r := r) E (oneFormPushforward (r := r) E a F) a w
      (fun _ => k) α) =ᶠ[𝓝 z] (fun w => F w k α) := by
    filter_upwards [(localDomain_isOpen E a).mem_nhds hz] with w hw
    exact oneFormPushforward_coefficients E a F w hw k α
  have hw (k p : Fin n) : wirtBar (fun w => coefficients (r := r) E
      (oneFormPushforward (r := r) E a F) a w (fun _ => k) α) z (stdVec p) =
        wirtBar (fun w => F w k α) z (stdVec p) := by
    unfold wirtBar
    rw [(hEq k).fderiv_eq]
  have hdel0 : (fun t : Fin 1 => (![i,j] : Fin 2 → Fin n) ((0 : Fin 2).succAbove t)) = (fun _ => j) := by
    ext t
    have ht : t = 0 := Subsingleton.elim _ _
    subst t
    rfl
  have hdel1 : (fun t : Fin 1 => (![i,j] : Fin 2 → Fin n) ((1 : Fin 2).succAbove t)) = (fun _ => i) := by
    ext t
    have ht : t = 0 := Subsingleton.elim _ _
    subst t
    rfl
  change wirtBar (fun y => F y j α) z (stdVec i) - wirtBar (fun y => F y i α) z (stdVec j) =
    ∑ t : Fin 2, (-1 : ℂ) ^ t.val * wirtBar (fun w => coefficients (r := r) E
      (oneFormPushforward (r := r) E a F) a w (fun k => (![i,j] : Fin 2 → Fin n) (t.succAbove k)) α)
        z (stdVec ((![i,j] : Fin 2 → Fin n) t))
  simp only [Fin.sum_univ_two, Fin.val_zero, Fin.val_one, pow_zero,
    pow_one, one_mul, hdel0, hdel1, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [hw j i, hw i j]
  ring

end Yau.LeafProofs.L14Aux

namespace Yau.LeafProofs.L14Aux

open BundleDbar

variable {n r : ℕ} {M : ComplexManifold n}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

set_option backward.isDefEq.respectTransparency false in
theorem formNormSq_two_chart_factor (g : HermitianField M) (h : Metric E)
    (u : NQForm E 2) (a : M.Carrier) (z : ComplexVector n)
    (hz : z ∈ localDomain (r := r) E a) :
    BundleDbar.formNormSq (r := r) E g h u (chartInv a z) = ((hMat g a z).det.re)⁻¹ *
      ((1 / 2 : ℂ) * ∑ α, ∑ β, ∑ i, ∑ j, ∑ k, ∑ l,
        BundleDbar.metricMatrix (r := r) E h a z α β * (hMat g a z)⁻¹ i k * (hMat g a z)⁻¹ j l *
          star (coefficients (r := r) E u a z ![i,j] α) * coefficients (r := r) E u a z ![k,l] β).re := by
  let G := hMat g a z
  let H := BundleDbar.metricMatrix (r := r) E h a z
  let T := fun α i j => coefficients (r := r) E u a z ![i,j] α
  rw [formNormSq_two_inChart E g h _ a z hz]
  change ((1 / 2 : ℂ) * ∑ i, ∑ k, ∑ j, ∑ l, G⁻¹ i k * G⁻¹ j l *
    ((∑ α, ∑ β, star (T α i j) * H α β * T β k l) / (G.det.re : ℂ))).re = _
  have hperm (f : Fin n → Fin n → Fin n → Fin n → Fin r → Fin r → ℂ) :
      (∑ i, ∑ k, ∑ j, ∑ l, ∑ α, ∑ β, f i k j l α β) =
        ∑ α, ∑ β, ∑ i, ∑ j, ∑ k, ∑ l, f i k j l α β := by
    let e : (Fin n × Fin n × Fin n × Fin n × Fin r × Fin r) ≃
        (Fin r × Fin r × Fin n × Fin n × Fin n × Fin n) :=
      { toFun := fun ⟨i,k,j,l,α,β⟩ => (α,β,i,j,k,l)
        invFun := fun ⟨α,β,i,j,k,l⟩ => (i,k,j,l,α,β)
        left_inv := by rintro ⟨i,k,j,l,α,β⟩; rfl
        right_inv := by rintro ⟨α,β,i,j,k,l⟩; rfl }
    simpa only [Fintype.sum_prod_type] using Fintype.sum_equiv e
      (fun p => f p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2)
      (fun p => f p.2.2.1 p.2.2.2.2.1 p.2.2.2.1 p.2.2.2.2.2 p.1 p.2.1)
      (by rintro ⟨i,k,j,l,α,β⟩; rfl)
  have he : (1 / 2 : ℂ) * (∑ i, ∑ k, ∑ j, ∑ l, G⁻¹ i k * G⁻¹ j l *
      ((∑ α, ∑ β, star (T α i j) * H α β * T β k l) / (G.det.re : ℂ))) =
      (G.det.re : ℂ)⁻¹ * ((1 / 2 : ℂ) * ∑ α, ∑ β, ∑ i, ∑ j, ∑ k, ∑ l,
        H α β * G⁻¹ i k * G⁻¹ j l * star (T α i j) * T β k l) := by
    simp only [div_eq_mul_inv, Finset.mul_sum, Finset.sum_mul]
    rw [hperm]
    apply Finset.sum_congr rfl
    intro α _
    apply Finset.sum_congr rfl
    intro β _
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    ring
  rw [he, ← Complex.ofReal_inv]
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

set_option backward.isDefEq.respectTransparency false in
theorem formNormSq_modelOneDbar_inChart (g : HermitianField M) (h : Metric E)
    (a : M.Carrier) (F : ComplexVector n → Fin n → ComplexVector r)
    (z : ComplexVector n) (hz : z ∈ localDomain (r := r) E a) :
    BundleDbar.formNormSq (r := r) E g h (twoFormPushforward (r := r) E a (modelOneDbar F)) (chartInv a z) =
      ((hMat g a z).det.re)⁻¹ * localCurlEnergy (hMat g a z)
        (BundleDbar.metricMatrix (r := r) E h a z) F z := by
  rw [formNormSq_two_chart_factor E g h _ a z hz]
  simp_rw [twoFormPushforward_coefficients E a _ (modelOneDbar_skew F) z hz]
  rfl

end Yau.LeafProofs.L14Aux
