import Yau.Geometry.Flat
import Yau.Proofs.C04BoundedGeometryChartsMetric

/-! The half-standard Hermitian field whose underlying real metric is Euclidean. -/
noncomputable section
open scoped Manifold Topology ContDiff Matrix ComplexOrder
open MeasureTheory Filter
namespace Yau.Proofs.C03Aux.FlatComplete
open Yau Yau.Blueprint Yau.LeafProofs
set_option backward.isDefEq.respectTransparency false

/-- The factor one half matches the project's convention `G = 2 Re h`. -/
def euclideanHermitianField (n : ℕ) (hn : 1 ≤ n) :
    HermitianField (ComplexEuclideanManifold n hn) :=
  fun x =>
    { toFun u v := ((1 / 2 : ℝ) : ℂ) * (flatHermitianField hn x).toFun u v
      map_add_left := by intro u v w; rw [(flatHermitianField hn x).map_add_left]; ring
      map_smul_left := by intro a u v; rw [(flatHermitianField hn x).map_smul_left]; ring
      map_add_right := by intro u v w; rw [(flatHermitianField hn x).map_add_right]; ring
      map_smul_right := by intro a u v; rw [(flatHermitianField hn x).map_smul_right]; ring
      conjugate_symmetric := by
        intro u v
        simpa only [star_mul', Complex.star_def, Complex.conj_ofReal] using
          congrArg (fun z : ℂ => ((1 / 2 : ℝ) : ℂ) * z)
            ((flatHermitianField hn x).conjugate_symmetric u v)
      self_adjoint := by
        intro u
        simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
          mul_zero, zero_mul, add_zero, (flatHermitianField hn x).self_adjoint]
      positive_definite := by
        intro u
        simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
        constructor
        · exact mul_nonneg (by norm_num) ((flatHermitianField hn x).positive_definite u).1
        · rw [mul_eq_zero, or_iff_right (by norm_num : (1 / 2 : ℝ) ≠ 0)]
          exact ((flatHermitianField hn x).positive_definite u).2 }

theorem euclideanHermitianField_apply (n : ℕ) (hn : 1 ≤ n)
    (x : (ComplexEuclideanManifold n hn).Carrier)
    (u v : TangentVector (ComplexEuclideanManifold n hn) x) :
    (euclideanHermitianField n hn x).toFun u v = ((1 / 2 : ℝ) : ℂ) *
      inner ℂ (tangentSpaceCastModel (ComplexModel n) x u)
        (tangentSpaceCastModel (ComplexModel n) x v) := by
  rfl

theorem euclidean_realMetricFn (n : ℕ) (hn : 1 ≤ n)
    (x : (ComplexEuclideanManifold n hn).Carrier) (z : ComplexVector n)
    (a b : RIdx n) :
    realMetricFn (euclideanHermitianField n hn) x z a b =
      (inner ℂ (realVec a) (realVec b)).re := by
  unfold realMetricFn
  rw [chartVec_euclidean, chartVec_euclidean, euclideanHermitianField_apply]
  change 2 * (((1 / 2 : ℝ) : ℂ) * inner ℂ (realVec a) (realVec b)).re = _
  simp

theorem euclidean_realMetricFn_eq_one (n : ℕ) (hn : 1 ≤ n)
    (x : (ComplexEuclideanManifold n hn).Carrier) (z : ComplexVector n) :
    realMetricFn (euclideanHermitianField n hn) x z = 1 := by
  ext a b
  rw [euclidean_realMetricFn]
  rcases a with ⟨i, a⟩
  rcases b with ⟨j, b⟩
  fin_cases a <;> fin_cases b <;> by_cases hij : i = j <;>
    simp [hij, realVec, EuclideanSpace.inner_single_left, EuclideanSpace.single,
      Matrix.one_apply, Prod.mk.injEq, norm_smul, PiLp.norm_single]

theorem euclidean_metricSmooth (n : ℕ) (hn : 1 ≤ n) :
    MetricSmooth (euclideanHermitianField n hn) := by
  intro x a b
  simp only [euclidean_realMetricFn]
  exact contDiffOn_const

theorem euclidean_kahlerFormFn (n : ℕ) (hn : 1 ≤ n)
    (x : (ComplexEuclideanManifold n hn).Carrier) (z : ComplexVector n)
    (a b : RIdx n) :
    kahlerFormFn (euclideanHermitianField n hn) x z a b =
      (inner ℂ (realVec a) (realVec b)).im := by
  unfold kahlerFormFn
  rw [chartVec_euclidean, chartVec_euclidean, euclideanHermitianField_apply]
  change 2 * (((1 / 2 : ℝ) : ℂ) * inner ℂ (realVec a) (realVec b)).im = _
  simp

theorem euclidean_kahlerClosed (n : ℕ) (hn : 1 ≤ n) :
    KahlerClosed (euclideanHermitianField n hn) := by
  intro x a b c
  simp [rDeriv, euclidean_kahlerFormFn]

theorem euclidean_hermitianNormSq (n : ℕ) (hn : 1 ≤ n)
    (x : (ComplexEuclideanManifold n hn).Carrier)
    (v : TangentVector (ComplexEuclideanManifold n hn) x) :
    hermitianNormSq (euclideanHermitianField n hn x) v =
      (1 / 2 : ℝ) * ‖tangentSpaceCastModel (ComplexModel n) x v‖ ^ 2 := by
  unfold hermitianNormSq
  rw [euclideanHermitianField_apply]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  exact congrArg (fun t : ℝ => (1 / 2 : ℝ) * t)
    (by simpa only [RCLike.re_to_complex] using
      (inner_self_eq_norm_sq (𝕜 := ℂ) (tangentSpaceCastModel (ComplexModel n) x v)))

theorem euclidean_realTangent_norm (n : ℕ) (hn : 1 ≤ n)
    (x : (ComplexEuclideanManifold n hn).Carrier)
    (v : TangentSpace 𝓘(ℝ, ComplexVector n) x) :
    letI := L12Aux.underlyingRealTangentNormedAddCommGroup (euclideanHermitianField n hn) x
    ‖v‖ = ‖tangentSpaceCastModel 𝓘(ℝ, ComplexVector n) x v‖ := by
  rw [L12Aux.underlyingRealTangent_norm, euclidean_hermitianNormSq]
  have he : tangentSpaceCastModel (ComplexModel n) x (L12Aux.realTangentEquiv x v) =
      tangentSpaceCastModel 𝓘(ℝ, ComplexVector n) x v := by
    change (tangentSpaceCastModel (ComplexModel n) x)
      ((tangentSpaceCastModel (ComplexModel n) x).symm
        (tangentSpaceCastModel 𝓘(ℝ, ComplexVector n) x v)) = _
    exact (tangentSpaceCastModel (ComplexModel n) x).apply_symm_apply _
  rw [he]
  rw [← mul_assoc, show 2 * (1 / 2 : ℝ) = 1 by norm_num, one_mul,
    Real.sqrt_sq (norm_nonneg _)]

end Yau.Proofs.C03Aux.FlatComplete
