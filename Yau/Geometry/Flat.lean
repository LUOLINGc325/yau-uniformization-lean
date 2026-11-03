import Yau.Geometry.Basic

open scoped Manifold

noncomputable section

namespace Yau

/-- The standard Hermitian product on a tangent space of the Euclidean model,
transported through the canonical tangent-space identification. -/
def flatHermitianInnerProduct {n : ℕ} {hn : 1 ≤ n}
    (x : (ComplexEuclideanManifold n hn).Carrier) :
    HermitianInnerProduct (TangentVector (ComplexEuclideanManifold n hn) x) where
  toFun u v :=
    inner ℂ (tangentSpaceCastModel (ComplexModel n) x u)
      (tangentSpaceCastModel (ComplexModel n) x v)
  map_add_left u₁ u₂ v := by
    rw [(tangentSpaceCastModel (ComplexModel n) x).map_add]
    rw [inner_add_left]
  map_smul_left a u v := by
    rw [(tangentSpaceCastModel (ComplexModel n) x).map_smul]
    rw [inner_smul_left (𝕜 := ℂ)]
    simp only [starRingEnd_apply]
  map_add_right u v₁ v₂ := by
    rw [(tangentSpaceCastModel (ComplexModel n) x).map_add]
    rw [inner_add_right]
  map_smul_right a u v := by
    rw [(tangentSpaceCastModel (ComplexModel n) x).map_smul]
    rw [inner_smul_right (𝕜 := ℂ)]
    ring
  conjugate_symmetric u v := by
    exact (inner_conj_symm _ _).symm
  self_adjoint u := by
    exact inner_self_im (𝕜 := ℂ) (tangentSpaceCastModel (ComplexModel n) x u)
  positive_definite u := by
    constructor
    · exact inner_self_nonneg (𝕜 := ℂ)
    · constructor
      · intro h
        have him :
            (inner ℂ (tangentSpaceCastModel (ComplexModel n) x u)
              (tangentSpaceCastModel (ComplexModel n) x u)).im = 0 :=
          inner_self_im (𝕜 := ℂ) _
        have hz :
            inner ℂ (tangentSpaceCastModel (ComplexModel n) x u)
              (tangentSpaceCastModel (ComplexModel n) x u) = 0 := by
          exact Complex.ext h him
        exact (tangentSpaceCastModel (ComplexModel n) x).injective
          (inner_self_eq_zero.mp hz)
      · intro hu
        subst u
        simp

/-- The constant Euclidean Hermitian field on the flat manifold. -/
def flatHermitianField {n : ℕ} (hn : 1 ≤ n) :
    HermitianField (ComplexEuclideanManifold n hn) :=
  fun x => flatHermitianInnerProduct x

theorem chartTangentVector_euclidean {n : ℕ} {hn : 1 ≤ n}
    (x : (ComplexEuclideanManifold n hn).Carrier) (i : Fin n) :
    chartTangentVector x i = EuclideanSpace.single i 1 := by
  let x' : EuclideanSpace ℂ (Fin n) := x
  change mfderiv (ComplexModel n) (ComplexModel n)
      (extChartAt (ComplexModel n) x').symm
      (extChartAt (ComplexModel n) x' x') (EuclideanSpace.single i 1) = _
  rw [extChartAt_model_space_eq_id]
  rw [PartialEquiv.refl_coe]
  change mfderiv (ComplexModel n) (ComplexModel n)
    (@id (EuclideanSpace ℂ (Fin n))) x' (EuclideanSpace.single i 1) = _
  rw [mfderiv_id]
  rfl

/-- The standard constant coefficient matrix `gᵢĵ = δᵢⱼ` in the global
Euclidean coordinates.  This is the coordinate model used below to expose
flatness of the curvature formula. -/
def flatMetricCoefficient (n : ℕ) (x : EuclideanSpace ℂ (Fin n))
    (i j : Fin n) : ℂ :=
  if i = j then 1 else 0

theorem chartTangentVectorInChart_euclidean {n : ℕ} {hn : 1 ≤ n}
    (x y : (ComplexEuclideanManifold n hn).Carrier) (i : Fin n) :
    chartTangentVectorInChart x y i = EuclideanSpace.single i 1 := by
  let x' : EuclideanSpace ℂ (Fin n) := x
  let y' : EuclideanSpace ℂ (Fin n) := y
  change mfderiv (ComplexModel n) (ComplexModel n)
      (extChartAt (ComplexModel n) x').symm
      (extChartAt (ComplexModel n) x' y') (EuclideanSpace.single i 1) = _
  rw [extChartAt_model_space_eq_id]
  rw [PartialEquiv.refl_coe]
  change mfderiv (ComplexModel n) (ComplexModel n)
    (@id (EuclideanSpace ℂ (Fin n))) y' (EuclideanSpace.single i 1) = _
  rw [mfderiv_id]
  rfl

theorem flatHermitianField_coordinateCoefficientInChart {n : ℕ} {hn : 1 ≤ n}
    (x y : (ComplexEuclideanManifold n hn).Carrier) (i j : Fin n) :
    coordinateCoefficientInChart (flatHermitianField hn) x y i j =
      flatMetricCoefficient n (y : EuclideanSpace ℂ (Fin n)) i j := by
  unfold coordinateCoefficientInChart flatHermitianField flatHermitianInnerProduct
  rw [chartTangentVectorInChart_euclidean x y i,
    chartTangentVectorInChart_euclidean x y j]
  change inner ℂ (EuclideanSpace.single i (1 : ℂ))
      (EuclideanSpace.single j (1 : ℂ)) = _
  rw [EuclideanSpace.inner_single_left]
  simp [flatMetricCoefficient, EuclideanSpace.single]


theorem flatHermitianField_coordinateCoefficient {n : ℕ} {hn : 1 ≤ n}
    (x : (ComplexEuclideanManifold n hn).Carrier) (i j : Fin n) :
    coordinateCoefficient (flatHermitianField hn) x i j =
      flatMetricCoefficient n (x : EuclideanSpace ℂ (Fin n)) i j := by
  simpa [coordinateCoefficient] using
    flatHermitianField_coordinateCoefficientInChart x x i j

def flatMetricMatrix (n : ℕ) (x : EuclideanSpace ℂ (Fin n)) :
    Matrix (Fin n) (Fin n) ℂ :=
  fun i j => flatMetricCoefficient n x i j

theorem flatMetricCoefficient_eq_delta (n : ℕ) (x : EuclideanSpace ℂ (Fin n))
    (i j : Fin n) :
    flatMetricCoefficient n x i j = if i = j then 1 else 0 := by
  rfl

theorem flatMetricCoefficient_conjugate_symmetric (n : ℕ)
    (x : EuclideanSpace ℂ (Fin n)) (i j : Fin n) :
    flatMetricCoefficient n x i j = star (flatMetricCoefficient n x j i) := by
  by_cases h : i = j
  · subst j
    simp [flatMetricCoefficient]
  · have h' : j ≠ i := Ne.symm h
    simp [flatMetricCoefficient, h, h']

theorem flatMetricMatrix_eq_one (n : ℕ) (x : EuclideanSpace ℂ (Fin n)) :
    flatMetricMatrix n x = (1 : Matrix (Fin n) (Fin n) ℂ) := by
  funext i j
  simp [flatMetricMatrix, flatMetricCoefficient, Matrix.one_apply]

/-- The identity matrix is positive definite through the usual Euclidean
Hermitian quadratic form. -/
def flatMetricQuadratic (n : ℕ) (x : EuclideanSpace ℂ (Fin n))
    (u : ComplexVector n) : ℂ :=
  inner ℂ u u

theorem flatMetricQuadratic_nonneg (n : ℕ) (x : EuclideanSpace ℂ (Fin n))
    (u : ComplexVector n) :
    0 ≤ (flatMetricQuadratic n x u).re := by
  exact (inner_self_nonneg (𝕜 := ℂ) (x := u))

theorem flatMetricQuadratic_eq_zero_iff (n : ℕ) (x : EuclideanSpace ℂ (Fin n))
    (u : ComplexVector n) :
    (flatMetricQuadratic n x u).re = 0 ↔ u = 0 := by
  constructor
  · intro h
    have him : (flatMetricQuadratic n x u).im = 0 := by
      exact inner_self_im (𝕜 := ℂ) u
    exact inner_self_eq_zero.mp (Complex.ext h him)
  · intro hu
    subst u
    simp [flatMetricQuadratic]

/-- First coordinate derivatives of the constant Euclidean matrix. -/
def flatCoordinateDerivative (n : ℕ) (x : EuclideanSpace ℂ (Fin n))
    (i j k : Fin n) : ℂ :=
  fderiv ℂ (fun _ : EuclideanSpace ℂ (Fin n) => flatMetricCoefficient n x i j) x
    (EuclideanSpace.single k 1)

/-- Bar derivatives are the conjugates used by `curvatureComponent`. -/
def flatCoordinateBarDerivative (n : ℕ) (x : EuclideanSpace ℂ (Fin n))
    (i j k : Fin n) : ℂ :=
  star (flatCoordinateDerivative n x i j k)

/-- Second coordinate derivatives of the constant Euclidean matrix. -/
def flatCoordinateSecondDerivative (n : ℕ) (x : EuclideanSpace ℂ (Fin n))
    (i j k l : Fin n) : ℂ :=
  fderiv ℂ
      (fun z => fderiv ℂ
        (fun _ : EuclideanSpace ℂ (Fin n) => flatMetricCoefficient n x i j) z
        (EuclideanSpace.single k 1))
      x (EuclideanSpace.single l 1)

def flatCoordinateBarSecondDerivative (n : ℕ) (x : EuclideanSpace ℂ (Fin n))
    (i j k l : Fin n) : ℂ :=
  star (flatCoordinateSecondDerivative n x i j k l)

theorem flatCoordinateDerivative_eq_zero (n : ℕ)
    (x : EuclideanSpace ℂ (Fin n)) (i j k : Fin n) :
    flatCoordinateDerivative n x i j k = 0 := by
  simp [flatCoordinateDerivative, fderiv_const]

theorem flatHermitianField_coordinateDerivative_eq_zero
    {n : ℕ} {hn : 1 ≤ n}
    (x : (ComplexEuclideanManifold n hn).Carrier) (i j k : Fin n) :
    coordinateDerivative (flatHermitianField hn) x i j k = 0 := by
  unfold coordinateDerivative chartCoefficientFunction
  have hf :
      (fun y => coordinateCoefficientInChart (flatHermitianField hn) x y i j) =
        (fun _ : (ComplexEuclideanManifold n hn).Carrier =>
          if i = j then (1 : ℂ) else 0) := by
    funext y
    rw [flatHermitianField_coordinateCoefficientInChart x y i j]
    rfl
  rw [hf]
  have hc :
      (fun z : (ComplexEuclideanManifold n hn).Carrier =>
        if i = j then (1 : ℂ) else 0) ∘
          (extChartAt (ComplexModel n) x).symm =
        (fun _ : EuclideanSpace ℂ (Fin n) => if i = j then (1 : ℂ) else 0) := by
    funext z
    rfl
  simp only [writtenInExtChartAt]
  rw [hc]
  simp [holomorphicCoordinateDerivativeAt,
    realCoordinateDerivativeAt, realImaginaryCoordinateDerivativeAt, fderiv_const]

theorem flatHermitianField_coordinateBarDerivative_eq_zero
    {n : ℕ} {hn : 1 ≤ n}
    (x : (ComplexEuclideanManifold n hn).Carrier) (i j k : Fin n) :
    coordinateBarDerivative (flatHermitianField hn) x i j k = 0 := by
  unfold coordinateBarDerivative chartCoefficientFunction
  have hf :
      (fun y => coordinateCoefficientInChart (flatHermitianField hn) x y i j) =
        (fun _ : (ComplexEuclideanManifold n hn).Carrier =>
          if i = j then (1 : ℂ) else 0) := by
    funext y
    rw [flatHermitianField_coordinateCoefficientInChart x y i j]
    rfl
  rw [hf]
  simp only [writtenInExtChartAt]
  have hc :
      (fun z : (ComplexEuclideanManifold n hn).Carrier =>
        if i = j then (1 : ℂ) else 0) ∘
          (extChartAt (ComplexModel n) x).symm =
        (fun _ : EuclideanSpace ℂ (Fin n) => if i = j then (1 : ℂ) else 0) := by
    funext z
    rfl
  rw [hc]
  simp [antiholomorphicCoordinateDerivativeAt, realCoordinateDerivativeAt,
    realImaginaryCoordinateDerivativeAt]

theorem flatHermitianField_coordinateSecondDerivative_eq_zero
    {n : ℕ} {hn : 1 ≤ n}
    (x : (ComplexEuclideanManifold n hn).Carrier) (i j k l : Fin n) :
    coordinateSecondDerivative (flatHermitianField hn) x i j k l = 0 := by
  unfold coordinateSecondDerivative chartCoefficientFunction
  have hf :
      (fun y => coordinateCoefficientInChart (flatHermitianField hn) x y i j) =
        (fun _ : (ComplexEuclideanManifold n hn).Carrier =>
          if i = j then (1 : ℂ) else 0) := by
    funext y
    rw [flatHermitianField_coordinateCoefficientInChart x y i j]
    rfl
  rw [hf]
  simp only [writtenInExtChartAt]
  have hc :
      (fun z : (ComplexEuclideanManifold n hn).Carrier =>
        if i = j then (1 : ℂ) else 0) ∘
          (extChartAt (ComplexModel n) x).symm =
        (fun _ : EuclideanSpace ℂ (Fin n) => if i = j then (1 : ℂ) else 0) := by
    funext z
    rfl
  rw [hc]
  simp [antiholomorphicCoordinateDerivativeAt, holomorphicCoordinateDerivativeAt,
    realCoordinateDerivativeAt, realImaginaryCoordinateDerivativeAt]

theorem flatCoordinateBarDerivative_eq_zero (n : ℕ)
    (x : EuclideanSpace ℂ (Fin n)) (i j k : Fin n) :
    flatCoordinateBarDerivative n x i j k = 0 := by
  simp [flatCoordinateBarDerivative, flatCoordinateDerivative_eq_zero]

theorem flatCoordinateSecondDerivative_eq_zero (n : ℕ)
    (x : EuclideanSpace ℂ (Fin n)) (i j k l : Fin n) :
    flatCoordinateSecondDerivative n x i j k l = 0 := by
  simp [flatCoordinateSecondDerivative, fderiv_const]

theorem flatCoordinateBarSecondDerivative_eq_zero (n : ℕ)
    (x : EuclideanSpace ℂ (Fin n)) (i j k l : Fin n) :
    flatCoordinateBarSecondDerivative n x i j k l = 0 := by
  simp [flatCoordinateBarSecondDerivative, flatCoordinateSecondDerivative_eq_zero]

def flatInverseMetricMatrix (n : ℕ) (x : EuclideanSpace ℂ (Fin n)) :
    Matrix (Fin n) (Fin n) ℂ :=
  (flatMetricMatrix n x)⁻¹

theorem flatInverseMetricMatrix_eq_one (n : ℕ)
    (x : EuclideanSpace ℂ (Fin n)) :
    flatInverseMetricMatrix n x = (1 : Matrix (Fin n) (Fin n) ℂ) := by
  simp [flatInverseMetricMatrix, flatMetricMatrix_eq_one]

/-- The curvature component obtained by substituting the constant matrix and
its coordinate derivatives into the formula in `Basic`. -/
def flatCurvatureComponent (n : ℕ) (x : EuclideanSpace ℂ (Fin n))
    (i j k l : Fin n) : ℂ :=
  -flatCoordinateSecondDerivative n x i j k l +
    ∑ p, ∑ q, (flatInverseMetricMatrix n x) p q *
      flatCoordinateDerivative n x i q k * flatCoordinateBarDerivative n x p j l

theorem flatCurvatureComponent_eq_zero (n : ℕ)
    (x : EuclideanSpace ℂ (Fin n)) (i j k l : Fin n) :
    flatCurvatureComponent n x i j k l = 0 := by
  simp [flatCurvatureComponent, flatCoordinateSecondDerivative_eq_zero,
    flatCoordinateDerivative_eq_zero, flatCoordinateBarDerivative_eq_zero]

def flatBisectionalNumerator (n : ℕ) (x : EuclideanSpace ℂ (Fin n))
    (u v : ComplexVector n) : ℂ :=
  ∑ i, ∑ j, ∑ k, ∑ l,
    flatCurvatureComponent n x i j k l * u i * star (u j) * v k * star (v l)

theorem flatBisectionalNumerator_eq_zero (n : ℕ)
    (x : EuclideanSpace ℂ (Fin n)) (u v : ComplexVector n) :
    flatBisectionalNumerator n x u v = 0 := by
  simp [flatBisectionalNumerator, flatCurvatureComponent_eq_zero]

/-- Any field whose first and second coordinate derivatives vanish has zero
curvature under the actual `curvatureComponent` formula. -/
theorem curvatureComponent_eq_zero_of_flat_derivatives
    {n : ℕ} {M : ComplexManifold n} (h : HermitianField M)
    (h₁ : ∀ (x : M.Carrier) (i j k : Fin n),
      coordinateDerivative h x i j k = 0)
    (h₂ : ∀ (x : M.Carrier) (i j k l : Fin n),
      coordinateSecondDerivative h x i j k l = 0)
    (x : M.Carrier) (i j k l : Fin n) :
    curvatureComponent h x i j k l = 0 := by
  simp [curvatureComponent, coordinateBarDerivative, h₁, h₂]

theorem bisectionalNumerator_eq_zero_of_flat_derivatives
    {n : ℕ} {M : ComplexManifold n} (h : HermitianField M)
    (h₁ : ∀ (x : M.Carrier) (i j k : Fin n),
      coordinateDerivative h x i j k = 0)
    (h₂ : ∀ (x : M.Carrier) (i j k l : Fin n),
      coordinateSecondDerivative h x i j k l = 0)
    (x : M.Carrier) (u v : ComplexVector n) :
    bisectionalNumerator h x u v = 0 := by
  simp [bisectionalNumerator,
    curvatureComponent_eq_zero_of_flat_derivatives h h₁ h₂]

/-- The standard tangent-space field therefore has zero curvature components in
its Euclidean coordinates. -/
theorem flatHermitianField_curvatureComponent_eq_zero
    {n : ℕ} {hn : 1 ≤ n}
    (x : (ComplexEuclideanManifold n hn).Carrier) (i j k l : Fin n) :
    curvatureComponent (flatHermitianField hn) x i j k l = 0 := by
  apply curvatureComponent_eq_zero_of_flat_derivatives
    (flatHermitianField hn)
  · exact flatHermitianField_coordinateDerivative_eq_zero
  · exact flatHermitianField_coordinateSecondDerivative_eq_zero

/-- Consequently the bisectional numerator in `Basic` vanishes identically. -/
theorem flatHermitianField_bisectionalNumerator_eq_zero
    {n : ℕ} {hn : 1 ≤ n}
    (x : (ComplexEuclideanManifold n hn).Carrier) (u v : ComplexVector n) :
    bisectionalNumerator (flatHermitianField hn) x u v = 0 := by
  simp [bisectionalNumerator, flatHermitianField_curvatureComponent_eq_zero]

theorem flatHermitianField_hbc_zero
    {n : ℕ} {hn : 1 ≤ n}
    (x : (ComplexEuclideanManifold n hn).Carrier) (u v : ComplexVector n) :
    HolomorphicBisectionalCurvatureOfField (flatHermitianField hn) x u v = 0 := by
  simp [HolomorphicBisectionalCurvatureOfField,
    flatHermitianField_bisectionalNumerator_eq_zero]


/-! The paper convention is tested independently of the Chern coordinate
calculator: a constant real metric has zero Christoffel symbols and curvature. -/

theorem chartVec_euclidean {n : ℕ} {hn : 1 ≤ n}
    (x y : (ComplexEuclideanManifold n hn).Carrier) (v : ComplexVector n) :
    chartVec x y v = v := by
  let x' : EuclideanSpace ℂ (Fin n) := x
  let y' : EuclideanSpace ℂ (Fin n) := y
  let v' : EuclideanSpace ℂ (Fin n) := v
  change mfderiv (ComplexModel n) (ComplexModel n)
      (extChartAt (ComplexModel n) x').symm
      (extChartAt (ComplexModel n) x' y') v' = _
  rw [extChartAt_model_space_eq_id]
  rw [PartialEquiv.refl_coe]
  change mfderiv (ComplexModel n) (ComplexModel n)
    (@id (EuclideanSpace ℂ (Fin n))) y' v' = _
  rw [mfderiv_id]
  rfl

theorem flatHermitianField_realMetricFn {n : ℕ} {hn : 1 ≤ n}
    (x : (ComplexEuclideanManifold n hn).Carrier) (z : ComplexVector n)
    (a b : RIdx n) :
    realMetricFn (flatHermitianField hn) x z a b =
      2 * (inner ℂ (realVec a) (realVec b)).re := by
  unfold realMetricFn
  rw [chartVec_euclidean, chartVec_euclidean]
  rfl

theorem flatHermitianField_christoffel {n : ℕ} {hn : 1 ≤ n}
    (x : (ComplexEuclideanManifold n hn).Carrier) (z : ComplexVector n)
    (c a b : RIdx n) :
    christoffel (flatHermitianField hn) x z c a b = 0 := by
  simp [christoffel, rDeriv, flatHermitianField_realMetricFn]

theorem flatHermitianField_riemannCoeff {n : ℕ} {hn : 1 ≤ n}
    (x : (ComplexEuclideanManifold n hn).Carrier) (z : ComplexVector n)
    (i j k l : RIdx n) :
    riemannCoeff (flatHermitianField hn) x z i j k l = 0 := by
  simp [riemannCoeff, rDeriv, flatHermitianField_christoffel]

theorem flatHermitianField_paperRm {n : ℕ} {hn : 1 ≤ n}
    (x : (ComplexEuclideanManifold n hn).Carrier)
    (u v w z : TangentVector (ComplexEuclideanManifold n hn) x) :
    paperRm (flatHermitianField hn) x u v w z = 0 := by
  simp [paperRm, flatHermitianField_riemannCoeff]

theorem flatHermitianField_paperHBC {n : ℕ} {hn : 1 ≤ n}
    (x : (ComplexEuclideanManifold n hn).Carrier)
    (u v : TangentVector (ComplexEuclideanManifold n hn) x) :
    paperHolomorphicBisectionalCurvature (flatHermitianField hn) x u v = 0 := by
  simp [paperHolomorphicBisectionalCurvature, paperBisectionalNumerator,
    flatHermitianField_paperRm]

theorem flatHermitianField_not_paperPositive (n : ℕ) (hn : 1 ≤ n) :
    ¬ PaperPositiveBisectional (flatHermitianField hn) := by
  intro h
  let x : (ComplexEuclideanManifold n hn).Carrier := (0 : ComplexVector n)
  let i : Fin n := ⟨0, Nat.zero_lt_of_lt hn⟩
  let u : TangentVector (ComplexEuclideanManifold n hn) x :=
    (tangentSpaceCastModel (ComplexModel n) x).symm (EuclideanSpace.single i 1)
  have hu : u ≠ 0 := by
    intro hz
    have hz' := congrArg (tangentSpaceCastModel (ComplexModel n) x) hz
    have hsingle : EuclideanSpace.single i (1 : ℂ) = (0 : ComplexVector n) := by
      simpa [u] using hz'
    have hi := congrArg (fun v : ComplexVector n => v i) hsingle
    simpa [EuclideanSpace.single] using hi
  have hp := h x u u hu hu
  simpa [flatHermitianField_paperRm] using hp

end Yau
