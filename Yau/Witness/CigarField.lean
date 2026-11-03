import Yau.Geometry.Flat
import Yau.Proofs.C04BoundedGeometryChartsMetric

/-! The cigar Hermitian field on the standard complex line. Its factor one half
matches the real metric convention `G = 2 Re h`. -/

noncomputable section
open scoped Manifold Topology ContDiff

namespace Yau.Witness.Cigar

set_option backward.isDefEq.respectTransparency false

abbrev cigarPlane : ComplexManifold 1 :=
  ComplexEuclideanManifold 1 (by decide)

abbrev V := ComplexVector 1

def cigarDenom (z : V) : ℝ := 1 + ‖z‖ ^ 2

def cigarScale (z : V) : ℝ := (2 * cigarDenom z)⁻¹

abbrev cigarModelVec (z : cigarPlane.Carrier)
    (u : TangentVector cigarPlane z) : V :=
  tangentSpaceCastModel (ComplexModel 1) z u

theorem cigarDenom_pos (z : V) : 0 < cigarDenom z := by
  unfold cigarDenom
  positivity

theorem cigarScale_pos (z : V) : 0 < cigarScale z := by
  unfold cigarScale
  exact inv_pos.mpr (mul_pos (by norm_num) (cigarDenom_pos z))

def cigarField : HermitianField cigarPlane :=
  fun x =>
    { toFun u v :=
        (cigarScale x : ℂ) * (flatHermitianField (n := 1) (by decide) x).toFun u v
      map_add_left := by
        intro u v w
        rw [(flatHermitianField (n := 1) (by decide) x).map_add_left]
        ring
      map_smul_left := by
        intro a u v
        rw [(flatHermitianField (n := 1) (by decide) x).map_smul_left]
        ring
      map_add_right := by
        intro u v w
        rw [(flatHermitianField (n := 1) (by decide) x).map_add_right]
        ring
      map_smul_right := by
        intro a u v
        rw [(flatHermitianField (n := 1) (by decide) x).map_smul_right]
        ring
      conjugate_symmetric := by
        intro u v
        simpa only [star_mul', Complex.star_def, Complex.conj_ofReal] using
          congrArg (fun w : ℂ => (cigarScale x : ℂ) * w)
            ((flatHermitianField (n := 1) (by decide) x).conjugate_symmetric u v)
      self_adjoint := by
        intro u
        simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
          mul_zero, zero_mul, add_zero,
          (flatHermitianField (n := 1) (by decide) x).self_adjoint]
      positive_definite := by
        intro u
        simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
          zero_mul, sub_zero]
        constructor
        · exact mul_nonneg (cigarScale_pos x).le
            ((flatHermitianField (n := 1) (by decide) x).positive_definite u).1
        · rw [mul_eq_zero, or_iff_right (ne_of_gt (cigarScale_pos x))]
          exact ((flatHermitianField (n := 1) (by decide) x).positive_definite u).2 }

theorem cigarField_apply (z : cigarPlane.Carrier)
    (u v : TangentVector cigarPlane z) :
    (cigarField z).toFun u v =
      (cigarScale z : ℂ) * inner ℂ (cigarModelVec z u) (cigarModelVec z v) := rfl

@[simp] theorem cigar_chartPt (x y : cigarPlane.Carrier) : chartPt x y = y := by
  change extChartAt (ComplexModel 1) (x : V) y = y
  rw [extChartAt_model_space_eq_id]
  rfl

@[simp] theorem cigar_chartInv (x : cigarPlane.Carrier) (z : V) : chartInv x z = z := by
  change (extChartAt (ComplexModel 1) (x : V)).symm z = z
  rw [extChartAt_model_space_eq_id]
  rfl

@[simp] theorem cigar_chartTarget (x : cigarPlane.Carrier) : chartTarget x = Set.univ := by
  change (extChartAt (ComplexModel 1) (x : V)).target = Set.univ
  rw [extChartAt_model_space_eq_id]
  rfl

@[simp] theorem cigar_tangentCoords (x y : cigarPlane.Carrier)
    (u : TangentVector cigarPlane y) : tangentCoords x y u = cigarModelVec y u := by
  change mfderiv (ComplexModel 1) (ComplexModel 1)
    (extChartAt (ComplexModel 1) (x : V)) y u = _
  rw [extChartAt_model_space_eq_id, PartialEquiv.refl_coe, mfderiv_id]
  rfl

theorem cigar_norm_sq_coordinates (z : V) :
    ‖z‖ ^ 2 = (z 0).re ^ 2 + (z 0).im ^ 2 := by
  have hz : z = EuclideanSpace.single 0 (z 0) := by
    ext i
    fin_cases i
    simp
  calc
    ‖z‖ ^ 2 = ‖z 0‖ ^ 2 := by
      conv_lhs => rw [hz]
      rw [PiLp.norm_single]
    _ = _ := by rw [Complex.sq_norm, Complex.normSq_apply]; ring

theorem cigar_two_scale (z : V) : 2 * cigarScale z = (cigarDenom z)⁻¹ := by
  unfold cigarScale
  rw [mul_inv_rev]
  ring

theorem cigar_hermitianNormSq (z : cigarPlane.Carrier)
    (u : TangentVector cigarPlane z) :
    hermitianNormSq (cigarField z) u = ‖cigarModelVec z u‖ ^ 2 / (2 * cigarDenom z) := by
  unfold hermitianNormSq
  rw [cigarField_apply]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [show (inner ℂ (cigarModelVec z u) (cigarModelVec z u)).re =
      ‖cigarModelVec z u‖ ^ 2 by
    simpa only [RCLike.re_to_complex] using
      (inner_self_eq_norm_sq (𝕜 := ℂ) (cigarModelVec z u))]
  simp only [cigarScale, div_eq_mul_inv, mul_comm]

theorem cigar_realVec_inner_re (a b : RIdx 1) :
    (inner ℂ (realVec a) (realVec b)).re = if a = b then 1 else 0 := by
  rcases a with ⟨i, a⟩
  rcases b with ⟨j, b⟩
  fin_cases i <;> fin_cases j <;> fin_cases a <;> fin_cases b <;>
    simp [realVec, EuclideanSpace.inner_single_left, EuclideanSpace.single,
      norm_smul, PiLp.norm_single]

theorem cigar_realMetricFn (x : cigarPlane.Carrier) (z : V) (a b : RIdx 1) :
    realMetricFn cigarField x z a b = if a = b then (cigarDenom z)⁻¹ else 0 := by
  unfold realMetricFn
  rw [chartVec_euclidean, chartVec_euclidean, cigarField_apply, cigar_chartInv]
  change 2 * ((cigarScale z : ℂ) * inner ℂ (realVec a) (realVec b)).re = _
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [← mul_assoc, cigar_two_scale, cigar_realVec_inner_re]
  split_ifs <;> simp

theorem cigarDenom_contDiff : ContDiff ℝ ∞ cigarDenom := by
  exact contDiff_const.add (contDiff_norm_sq ℂ)

theorem cigar_metricSmooth : MetricSmooth cigarField := by
  intro x a b
  simp only [cigar_realMetricFn]
  by_cases hab : a = b
  · simp only [hab, ↓reduceIte]
    exact (cigarDenom_contDiff.inv fun z => (cigarDenom_pos z).ne').contDiffOn
  · simp only [hab, ↓reduceIte]
    exact contDiffOn_const

theorem cigar_kahlerFormFn (x : cigarPlane.Carrier) (z : V) (a b : RIdx 1) :
    kahlerFormFn cigarField x z a b =
      if a.2 = 0 then (if b.2 = 0 then 0 else (cigarDenom z)⁻¹)
      else (if b.2 = 0 then -(cigarDenom z)⁻¹ else 0) := by
  unfold kahlerFormFn
  rw [chartVec_euclidean, chartVec_euclidean, cigarField_apply, cigar_chartInv]
  change 2 * ((cigarScale z : ℂ) * inner ℂ (realVec a) (realVec b)).im = _
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
  rw [← mul_assoc, cigar_two_scale]
  rcases a with ⟨i, a⟩
  rcases b with ⟨j, b⟩
  fin_cases i <;> fin_cases j <;> fin_cases a <;> fin_cases b <;>
    simp [realVec, EuclideanSpace.inner_single_left, EuclideanSpace.single,
      norm_smul, PiLp.norm_single]

theorem cigar_kahlerClosed : KahlerClosed cigarField := by
  intro x a b c
  rcases a with ⟨i, a⟩
  rcases b with ⟨j, b⟩
  rcases c with ⟨k, c⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    fin_cases a <;> fin_cases b <;> fin_cases c <;>
      simp [cigar_kahlerFormFn, rDeriv]

theorem cigar_realTangentDerivative {x y : cigarPlane.Carrier}
    (γ : PiecewiseC1Curve x y) (t : ℝ) :
    cigarModelVec (γ t) (realTangentDerivative γ t) = deriv (F := V) γ.toFun t := by
  unfold realTangentDerivative
  change cigarModelVec (γ t)
    (mfderiv (ComplexModel 1) (ComplexModel 1)
      (extChartAt (ComplexModel 1) (γ t : V)).symm
      (extChartAt (ComplexModel 1) (γ t : V) (γ t))
      ((fderiv ℝ (fun s : ℝ => extChartAt (ComplexModel 1) (γ t : V) (γ s)) t) 1)) = _
  rw [extChartAt_model_space_eq_id]
  change cigarModelVec (γ t)
    (mfderiv (ComplexModel 1) (ComplexModel 1) (@id V) (γ t : V)
      ((fderiv ℝ (F := V) γ.toFun t) 1)) = _
  rw [mfderiv_id]
  rfl

theorem cigar_curveSpeed {x y : cigarPlane.Carrier}
    (γ : PiecewiseC1Curve x y) (t : ℝ) :
    curveSpeed cigarField γ t = ‖deriv (F := V) γ.toFun t‖ / Real.sqrt (cigarDenom (γ t)) := by
  unfold curveSpeed
  rw [cigar_hermitianNormSq, cigar_realTangentDerivative]
  rw [show 2 * (‖deriv (F := V) γ.toFun t‖ ^ 2 / (2 * cigarDenom (γ t))) =
      ‖deriv (F := V) γ.toFun t‖ ^ 2 / cigarDenom (γ t) by
    field_simp]
  rw [Real.sqrt_div (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]

end Yau.Witness.Cigar
