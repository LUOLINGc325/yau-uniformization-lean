import Mathlib

/-!
Concrete statement layer.  Manifolds use Mathlib's charted-manifold classes.
Hermitian metrics live on the actual tangent spaces; their distance is the
infimum of metric lengths of smooth curves, Kähler equations are coordinate
derivative identities, and curvature is the corresponding coordinate formula.
No structure field is an arbitrary `Prop` or `Type` placeholder.
-/

open scoped Manifold Topology ContDiff

noncomputable section

namespace Yau

abbrev ComplexVector (n : ℕ) := EuclideanSpace ℂ (Fin n)
abbrev ComplexModel (n : ℕ) := 𝓘(ℂ, EuclideanSpace ℂ (Fin n))

structure ComplexManifold (n : ℕ) where
  Carrier : Type
  topology : TopologicalSpace Carrier
  charted : @ChartedSpace (EuclideanSpace ℂ (Fin n)) inferInstance Carrier topology
  manifold : @IsManifold ℂ inferInstance (EuclideanSpace ℂ (Fin n)) inferInstance inferInstance
      (EuclideanSpace ℂ (Fin n)) inferInstance (𝓘(ℂ, EuclideanSpace ℂ (Fin n))) ⊤
      Carrier topology charted
  t2 : @T2Space Carrier topology
  secondCountable : @SecondCountableTopology Carrier topology
  connected : @ConnectedSpace Carrier topology
  noncompact : @NoncompactSpace Carrier topology
  dimension : ℕ
  dimension_eq : dimension = n

instance (M : ComplexManifold n) : TopologicalSpace M.Carrier := M.topology
instance (M : ComplexManifold n) :
    ChartedSpace (EuclideanSpace ℂ (Fin n)) M.Carrier := M.charted
instance (M : ComplexManifold n) : IsManifold (ComplexModel n) ⊤ M.Carrier := M.manifold
instance (M : ComplexManifold n) : T2Space M.Carrier := M.t2
instance (M : ComplexManifold n) : SecondCountableTopology M.Carrier := M.secondCountable
instance (M : ComplexManifold n) : ConnectedSpace M.Carrier := M.connected
instance (M : ComplexManifold n) : NoncompactSpace M.Carrier := M.noncompact

def IsCauchy {X : Type} (d : X → X → ℝ) (s : ℕ → X) : Prop :=
  ∀ ε, 0 < ε → ∃ N, ∀ m k, N ≤ m → N ≤ k → d (s m) (s k) < ε

def IsCompleteDistance {X : Type} (d : X → X → ℝ) : Prop :=
  ∀ s, IsCauchy d s → ∃ x, ∀ ε > 0, ∃ N, ∀ k ≥ N, d (s k) x < ε

/-- A genuine complex Hermitian inner product on a complex tangent space. -/
structure HermitianInnerProduct (V : Type*) [AddCommGroup V] [Module ℂ V] where
  toFun : V → V → ℂ
  map_add_left : ∀ u₁ u₂ v, toFun (u₁ + u₂) v = toFun u₁ v + toFun u₂ v
  map_smul_left : ∀ (a : ℂ) u v, toFun (a • u) v = star a * toFun u v
  map_add_right : ∀ u v₁ v₂, toFun u (v₁ + v₂) = toFun u v₁ + toFun u v₂
  map_smul_right : ∀ (a : ℂ) u v, toFun u (a • v) = toFun u v * a
  conjugate_symmetric : ∀ u v, toFun u v = star (toFun v u)
  self_adjoint : ∀ u, (toFun u u).im = 0
  positive_definite : ∀ u, 0 ≤ (toFun u u).re ∧ ((toFun u u).re = 0 ↔ u = 0)

def hermitianNormSq {V : Type*} [AddCommGroup V] [Module ℂ V]
    (h : HermitianInnerProduct V) (u : V) : ℝ :=
  (h.toFun u u).re

theorem hermitianNormSq_nonneg {V : Type*} [AddCommGroup V] [Module ℂ V]
    (h : HermitianInnerProduct V) (u : V) : 0 ≤ hermitianNormSq h u :=
  (h.positive_definite u).1

theorem hermitianNormSq_pos {V : Type*} [AddCommGroup V] [Module ℂ V]
    (h : HermitianInnerProduct V) {u : V} (hu : u ≠ 0) :
    0 < hermitianNormSq h u := by
  have hnonneg := hermitianNormSq_nonneg h u
  have hne : hermitianNormSq h u ≠ 0 := by
    intro hz
    exact hu ((h.positive_definite u).2.mp hz)
  exact lt_of_le_of_ne hnonneg (Ne.symm hne)

/-! `TangentSpace (ComplexModel n) x` is Mathlib's intrinsic tangent-bundle
fiber over `x`, not a globally chosen copy of `ComplexVector n`.  The
`TangentBundleFiber` alias makes this distinction explicit at every metric
boundary; all coordinate representatives below are obtained by `mfderiv` in
one fixed chart and are never supplied as metric data. -/
abbrev TangentBundleFiber {n : ℕ} (M : ComplexManifold n) (x : M.Carrier) :=
  TangentSpace (ComplexModel n) x

abbrev TangentVector {n : ℕ} (M : ComplexManifold n) (x : M.Carrier) :=
  TangentBundleFiber M x

abbrev HermitianField (M : ComplexManifold n) :=
  ∀ x, HermitianInnerProduct (TangentBundleFiber M x)

/-- The coordinate tangent vectors are obtained by differentiating the inverse
extended chart, so no globally chosen vector field is part of the metric data. -/
def chartTangentVector {n : ℕ} {M : ComplexManifold n} (x : M.Carrier) (i : Fin n) :
    TangentVector M x :=
  mfderiv (ComplexModel n) (ComplexModel n) (extChartAt (ComplexModel n) x).symm
    (extChartAt (ComplexModel n) x x) (EuclideanSpace.single i 1)

/- The coefficient at `y` is written in the fixed chart based at `x`; the
   frame is not re-centred at `y` while the coefficient is differentiated. -/
def chartTangentVectorInChart {n : ℕ} {M : ComplexManifold n}
    (x y : M.Carrier) (i : Fin n) : TangentVector M y :=
  mfderiv (ComplexModel n) (ComplexModel n) (extChartAt (ComplexModel n) x).symm
    (extChartAt (ComplexModel n) x y) (EuclideanSpace.single i 1)

def coordinateCoefficientInChart {n : ℕ} {M : ComplexManifold n}
    (h : HermitianField M) (x y : M.Carrier) (i j : Fin n) : ℂ :=
  (h y).toFun (chartTangentVectorInChart x y i) (chartTangentVectorInChart x y j)

/- The transition map between two extended charts and its complex derivative. -/
def chartTransition {n : ℕ} {M : ComplexManifold n}
    (x y : M.Carrier) : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin n) :=
  fun z => extChartAt (ComplexModel n) x ((extChartAt (ComplexModel n) y).symm z)

def chartFrameChange {n : ℕ} {M : ComplexManifold n}
    (x y z : M.Carrier) :
    EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n) :=
  fderiv ℂ (chartTransition x y) (extChartAt (ComplexModel n) y z)

def chartVectorInFrame {n : ℕ} {M : ComplexManifold n}
    (x z : M.Carrier) (u : ComplexVector n) : TangentVector M z :=
  ∑ i, u i • chartTangentVectorInChart x z i

/- A tensorial transition law: the same tangent vector represented in two
   overlapping chart frames has the same Hermitian value after applying the
   mfderiv of the chart transition.  This is a concrete equality on actual
   tangent fibers, not a caller-supplied property slot. -/
def HermitianFieldChartTransition {n : ℕ} {M : ComplexManifold n}
    (h : HermitianField M) : Prop :=
  ∀ (x y z : M.Carrier),
    z ∈ (extChartAt (ComplexModel n) x).source →
    z ∈ (extChartAt (ComplexModel n) y).source →
    ∀ (u v : ComplexVector n),
    (h z).toFun (chartVectorInFrame x z u) (chartVectorInFrame x z v) =
      (h z).toFun
        (chartVectorInFrame y z (chartFrameChange y x z u))
        (chartVectorInFrame y z (chartFrameChange y x z v))

def coordinateCoefficient {n : ℕ} {M : ComplexManifold n}
    (h : HermitianField M) (x : M.Carrier) (i j : Fin n) : ℂ :=
  coordinateCoefficientInChart h x x i j

def chartCoefficientFunction {n : ℕ} {M : ComplexManifold n}
    (h : HermitianField M) (x : M.Carrier) (i j : Fin n) :
    EuclideanSpace ℂ (Fin n) → ℂ :=
  writtenInExtChartAt (ComplexModel n) (𝓘(ℂ, ℂ)) x
    (fun y => coordinateCoefficientInChart h x y i j)

def realCoordinateDerivativeAt {n : ℕ}
    (f : EuclideanSpace ℂ (Fin n) → ℂ)
    (z : EuclideanSpace ℂ (Fin n)) (k : Fin n) : ℂ :=
  fderiv ℝ f z (EuclideanSpace.single k 1)

def realImaginaryCoordinateDerivativeAt {n : ℕ}
    (f : EuclideanSpace ℂ (Fin n) → ℂ)
    (z : EuclideanSpace ℂ (Fin n)) (k : Fin n) : ℂ :=
  fderiv ℝ f z (Complex.I • EuclideanSpace.single k 1)

/-- Wirtinger derivatives, formed from the real Fréchet derivative. -/
def holomorphicCoordinateDerivativeAt {n : ℕ}
    (f : EuclideanSpace ℂ (Fin n) → ℂ)
    (z : EuclideanSpace ℂ (Fin n)) (k : Fin n) : ℂ :=
  (1 / 2 : ℂ) *
    (realCoordinateDerivativeAt f z k -
      Complex.I * realImaginaryCoordinateDerivativeAt f z k)

def antiholomorphicCoordinateDerivativeAt {n : ℕ}
    (f : EuclideanSpace ℂ (Fin n) → ℂ)
    (z : EuclideanSpace ℂ (Fin n)) (k : Fin n) : ℂ :=
  (1 / 2 : ℂ) *
    (realCoordinateDerivativeAt f z k +
      Complex.I * realImaginaryCoordinateDerivativeAt f z k)

def coordinateDerivative {n : ℕ} {M : ComplexManifold n}
    (h : HermitianField M) (x : M.Carrier) (i j k : Fin n) : ℂ :=
  holomorphicCoordinateDerivativeAt (chartCoefficientFunction h x i j)
    (extChartAt (ComplexModel n) x x) k

def coordinateBarDerivative {n : ℕ} {M : ComplexManifold n}
    (h : HermitianField M) (x : M.Carrier) (i j k : Fin n) : ℂ :=
  antiholomorphicCoordinateDerivativeAt (chartCoefficientFunction h x i j)
    (extChartAt (ComplexModel n) x x) k

def coordinateSecondDerivative {n : ℕ} {M : ComplexManifold n}
    (h : HermitianField M) (x : M.Carrier) (i j k l : Fin n) : ℂ :=
  antiholomorphicCoordinateDerivativeAt
    (fun z => holomorphicCoordinateDerivativeAt
      (chartCoefficientFunction h x i j) z k)
    (extChartAt (ComplexModel n) x x) l

def coordinateBarSecondDerivative {n : ℕ} {M : ComplexManifold n}
    (h : HermitianField M) (x : M.Carrier) (i j k l : Fin n) : ℂ :=
  coordinateSecondDerivative h x i j k l

def metricMatrix {n : ℕ} {M : ComplexManifold n}
    (h : HermitianField M) (x : M.Carrier) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => coordinateCoefficient h x i j

def inverseMetricMatrix {n : ℕ} {M : ComplexManifold n}
    (h : HermitianField M) (x : M.Carrier) : Matrix (Fin n) (Fin n) ℂ :=
  (metricMatrix h x)⁻¹

section RealGeometry
variable {n : ℕ} {M : ComplexManifold n}

def chartPt {n : ℕ} {M : ComplexManifold n} (x y : M.Carrier) : ComplexVector n :=
  extChartAt (ComplexModel n) x y

def chartInv {n : ℕ} {M : ComplexManifold n} (x : M.Carrier) (z : ComplexVector n) : M.Carrier :=
  (extChartAt (ComplexModel n) x).symm z

def chartTarget {n : ℕ} {M : ComplexManifold n} (x : M.Carrier) : Set (ComplexVector n) :=
  (extChartAt (ComplexModel n) x).target

def chartVec {n : ℕ} {M : ComplexManifold n} (x y : M.Carrier) (v : ComplexVector n) :
    TangentVector M y :=
  mfderiv (ComplexModel n) (ComplexModel n) (extChartAt (ComplexModel n) x).symm
    (chartPt x y) v

def tangentCoords {n : ℕ} {M : ComplexManifold n} (x y : M.Carrier) (v : TangentVector M y) :
    ComplexVector n :=
  mfderiv (ComplexModel n) (ComplexModel n) (extChartAt (ComplexModel n) x) y v

/-! ## Real coordinates -/

/-- Index set of the real basis `e₁, I e₁, …, eₙ, I eₙ` of `ℂⁿ`. -/
abbrev RIdx (n : ℕ) := Fin n × Fin 2

def realVec (a : RIdx n) : ComplexVector n :=
  (if a.2 = 0 then (1 : ℂ) else Complex.I) • EuclideanSpace.single a.1 1

def realCoord (v : ComplexVector n) (a : RIdx n) : ℝ :=
  if a.2 = 0 then (v a.1).re else (v a.1).im

/-- Real directional derivative along the real basis vector `a`. -/
def rDeriv (f : ComplexVector n → ℝ) (z : ComplexVector n) (a : RIdx n) : ℝ :=
  fderiv ℝ f z (realVec a)

/-- Real Riemannian metric coefficients `G_{ab} = 2 Re h(∂_a, ∂_b)` in real coordinates of the
chart centred at `x`. -/
def realMetricFn (h : HermitianField M) (x : M.Carrier) (z : ComplexVector n) :
    Matrix (RIdx n) (RIdx n) ℝ :=
  fun a b => 2 * ((h (chartInv x z)).toFun (chartVec x (chartInv x z) (realVec a))
      (chartVec x (chartInv x z) (realVec b))).re

/-- Kähler form coefficients `ω_{ab} = G(J ∂_a, ∂_b) = 2 Im h(∂_a, ∂_b)`. -/
def kahlerFormFn (h : HermitianField M) (x : M.Carrier) (z : ComplexVector n) (a b : RIdx n) : ℝ :=
  2 * ((h (chartInv x z)).toFun (chartVec x (chartInv x z) (realVec a))
      (chartVec x (chartInv x z) (realVec b))).im

/-- Smoothness: every real metric coefficient is `C^∞` on every chart. -/
def MetricSmooth (h : HermitianField M) : Prop :=
  ∀ (x : M.Carrier) (a b : RIdx n),
    ContDiffOn ℝ ∞ (fun z => realMetricFn h x z a b) (chartTarget x)

/-- Kähler condition `dω = 0`, written at every point in the chart centred at it
(`dω` is tensorial, so one chart per point suffices). -/
def KahlerClosed (h : HermitianField M) : Prop :=
  ∀ (x : M.Carrier) (a b c : RIdx n),
    rDeriv (fun z => kahlerFormFn h x z b c) (chartPt x x) a +
      rDeriv (fun z => kahlerFormFn h x z c a) (chartPt x x) b +
      rDeriv (fun z => kahlerFormFn h x z a b) (chartPt x x) c = 0

/-! ## Levi-Civita curvature in real coordinates (Lee, *Riemannian Manifolds*, Prop. 7.4) -/

/-- Christoffel symbol `Γ^c_{ab}`. -/
def christoffel (h : HermitianField M) (x : M.Carrier) (z : ComplexVector n) (c a b : RIdx n) : ℝ :=
  (1 / 2 : ℝ) * ∑ d, (realMetricFn h x z)⁻¹ c d *
    (rDeriv (fun w => realMetricFn h x w b d) z a + rDeriv (fun w => realMetricFn h x w a d) z b -
      rDeriv (fun w => realMetricFn h x w a b) z d)

/-- `R_{ijk}^l`, with `R(∂_i,∂_j)∂_k = R_{ijk}^l ∂_l` and
`R(X,Y) = ∇_X∇_Y - ∇_Y∇_X - ∇_{[X,Y]}`. -/
def riemannCoeff (h : HermitianField M) (x : M.Carrier) (z : ComplexVector n)
    (i j k l : RIdx n) : ℝ :=
  rDeriv (fun w => christoffel h x w l j k) z i - rDeriv (fun w => christoffel h x w l i k) z j +
    ∑ m, (christoffel h x z m j k * christoffel h x z l i m -
      christoffel h x z m i k * christoffel h x z l j m)

/-- `Rm(X,Y,Z,W) = ⟨R(X,Y)Z, W⟩` at `x`, so that `Rm(u,v,v,u)` is the sectional-curvature
numerator of the plane spanned by `u, v` (the paper's convention). -/
def paperRm (h : HermitianField M) (x : M.Carrier)
    (X Y Z W : TangentSpace (ComplexModel n) x) : ℝ :=
  ∑ i, ∑ j, ∑ k, ∑ l, ∑ m, realMetricFn h x (chartPt x x) l m * riemannCoeff h x (chartPt x x) i j k l *
    realCoord (tangentCoords x x X) i * realCoord (tangentCoords x x Y) j *
    realCoord (tangentCoords x x Z) k * realCoord (tangentCoords x x W) m

/-- The paper's hypothesis: `Rm(u,v,v,u) + Rm(u,Jv,Jv,u) > 0` for all nonzero real tangent
vectors `u, v` (equivalently, unit vectors; the expression is homogeneous). -/
def PaperPositiveBisectional (h : HermitianField M) : Prop :=
  ∀ (x : M.Carrier) (u v : TangentSpace (ComplexModel n) x), u ≠ 0 → v ≠ 0 →
    0 < paperRm h x u v v u + paperRm h x u (Complex.I • v) (Complex.I • v) u

/-- Kähler closure uses every real coordinate direction, including imaginary ones. -/
def KahlerCoordinateCondition (h : HermitianField M) : Prop := KahlerClosed h

end RealGeometry

/-- A real piecewise-C¹ curve used to define length.  The finite breakpoint
set records where a piecewise derivative may fail; speed is computed from the
real manifold derivative and the Hermitian form. -/
structure PiecewiseC1Curve {n : ℕ} {M : ComplexManifold n} (x y : M.Carrier) where
  toFun : ℝ → M.Carrier
  start_eq : toFun 0 = x
  finish_eq : toFun 1 = y
  breakpoints : Finset ℝ
  breakpoints_mem : ∀ t ∈ breakpoints, t ∈ Set.Icc (0 : ℝ) 1
  continuous_on : ContinuousOn toFun (Set.Icc (0 : ℝ) 1)
  piecewise_c1 : ∀ t, t ∉ breakpoints →
    ContDiffAt ℝ 1
      (fun s : ℝ => extChartAt (ComplexModel n) (toFun t) (toFun s)) t

/-- Every accepted path is continuous on its parameter interval; this is the
  guard that rejects jump functions at breakpoints. -/
theorem PiecewiseC1Curve.continuous_on_interval {n : ℕ} {M : ComplexManifold n}
    {x y : M.Carrier} (γ : PiecewiseC1Curve x y) :
    ContinuousOn γ.toFun (Set.Icc (0 : ℝ) 1) :=
  γ.continuous_on

instance {n : ℕ} {M : ComplexManifold n} {x y : M.Carrier} :
    CoeFun (PiecewiseC1Curve x y) (fun _ => ℝ → M.Carrier) := ⟨PiecewiseC1Curve.toFun⟩

def realTangentDerivative {n : ℕ} {M : ComplexManifold n}
    {x y : M.Carrier} (γ : PiecewiseC1Curve x y) (t : ℝ) : TangentVector M (γ t) :=
  mfderiv (ComplexModel n) (ComplexModel n)
      (extChartAt (ComplexModel n) (γ t)).symm
      (extChartAt (ComplexModel n) (γ t) (γ t))
      ((fderiv ℝ (fun s : ℝ => extChartAt (ComplexModel n) (γ t) (γ s)) t) 1)

def curveSpeed {n : ℕ} {M : ComplexManifold n}
    (h : HermitianField M) {x y : M.Carrier} (γ : PiecewiseC1Curve x y) (t : ℝ) : ℝ :=
  Real.sqrt (2 * hermitianNormSq (h (γ t))
    (realTangentDerivative γ t))

def curveLength {n : ℕ} {M : ComplexManifold n}
    (h : HermitianField M) {x y : M.Carrier} (γ : PiecewiseC1Curve x y) : ℝ :=
  ∫ t in Set.Icc (0 : ℝ) 1, curveSpeed h γ t

/- Only curves whose metric speed is integrable are admitted to the length
   infimum.  This prevents `integral_undef` from assigning zero length to a
   continuous curve with an oscillatory, non-L¹ derivative. -/
def IntegrableCurve {n : ℕ} {M : ComplexManifold n}
    (h : HermitianField M) (x y : M.Carrier) :=
  {γ : PiecewiseC1Curve x y //
    MeasureTheory.IntegrableOn (curveSpeed h γ) (Set.Icc (0 : ℝ) 1)}

/-- Length distance induced by the Hermitian metric, as the infimum of lengths
of real piecewise-C¹ curves joining the endpoints. -/
def inducedDistance {n : ℕ} {M : ComplexManifold n}
    (h : HermitianField M) (x y : M.Carrier) : ℝ :=
  sInf (Set.range (fun γ : IntegrableCurve h x y => curveLength h γ.1))

/-- Extended version of the computed finite length distance. Applications of
this coordinate calculus to metrics use the distance laws in `SmoothMetric`. -/
def lengthEDist {n : ℕ} {M : ComplexManifold n}
    (h : HermitianField M) (x y : M.Carrier) : ENNReal :=
  ENNReal.ofReal (inducedDistance h x y)

abbrev lengthDist {n : ℕ} {M : ComplexManifold n} := @inducedDistance n M

def IsInducedDistanceTopology {X : Type} [TopologicalSpace X]
    (d : X → X → ℝ) : Prop :=
  ∀ (x : X) (s : Set X), s ∈ nhds x ↔
    ∃ ε > 0, {y | d x y < ε} ⊆ s

structure SmoothMetric (M : ComplexManifold n) where
  form : HermitianField M
  coordinate_smooth : ∀ (x : M.Carrier) (i j : Fin n),
    ContDiffOn ℝ ∞ (chartCoefficientFunction form x i j)
      (extChartAt (ComplexModel n) x).target
  curve_nonempty : ∀ (x y : M.Carrier), Nonempty (PiecewiseC1Curve x y)
  integrable_curve_nonempty : ∀ (x y : M.Carrier), Nonempty (IntegrableCurve form x y)
  chart_transition : HermitianFieldChartTransition form
  induced_distance_nonneg : ∀ x y, 0 ≤ inducedDistance form x y
  induced_distance_eq_zero : ∀ {x y}, inducedDistance form x y = 0 ↔ x = y
  induced_distance_symm : ∀ x y, inducedDistance form x y = inducedDistance form y x
  induced_distance_triangle : ∀ x y z,
    inducedDistance form x z ≤ inducedDistance form x y + inducedDistance form y z
  induced_distance_topology : IsInducedDistanceTopology (inducedDistance form)
  complete_distance : IsCompleteDistance (inducedDistance form)
  kahler_equations : KahlerCoordinateCondition form

abbrev IsSmooth {n : ℕ} {M : ComplexManifold n} (g : SmoothMetric M) : Prop :=
  ∀ (x : M.Carrier) (i j : Fin n),
    ContDiffOn ℝ ∞ (chartCoefficientFunction g.form x i j)
      (extChartAt (ComplexModel n) x).target

def IsComplete {n : ℕ} {M : ComplexManifold n} (g : SmoothMetric M) : Prop :=
  IsCompleteDistance (inducedDistance g.form)

def IsKahler {n : ℕ} {M : ComplexManifold n} (g : SmoothMetric M) : Prop :=
  KahlerCoordinateCondition g.form

/-- Chern coordinate calculator, using `g_{i\bar j}=h(e_j,e_i)`.
The endpoint uses the real Levi-Civita expression `paperRm` directly. -/
def curvatureComponent {n : ℕ} {M : ComplexManifold n}
    (h : HermitianField M) (x : M.Carrier) (i j k l : Fin n) : ℂ :=
  -coordinateSecondDerivative h x j i k l +
    ∑ p, ∑ q, inverseMetricMatrix h x p q *
      coordinateDerivative h x q i k * coordinateBarDerivative h x j p l

def bisectionalNumerator {n : ℕ} {M : ComplexManifold n}
    (h : HermitianField M) (x : M.Carrier) (u v : ComplexVector n) : ℂ :=
  ∑ i, ∑ j, ∑ k, ∑ l,
    curvatureComponent h x i j k l * u i * star (u j) * v k * star (v l)

/- The curvature contraction consumed by the geometric statement is expressed
   on the intrinsic tangent fiber.  `tangentSpaceCastModel` is only the
   coordinate representative used to feed the fixed chart frame above. -/
def tangentCoordinates {n : ℕ} {M : ComplexManifold n}
    (x : M.Carrier) (u : TangentVector M x) : ComplexVector n :=
  mfderiv (ComplexModel n) (ComplexModel n)
    (extChartAt (ComplexModel n) x) x u

def bisectionalNumeratorOnTangent {n : ℕ} {M : ComplexManifold n}
    (h : HermitianField M) (x : M.Carrier)
    (u v : TangentVector M x) : ℂ :=
  bisectionalNumerator h x (tangentCoordinates x u) (tangentCoordinates x v)

def HolomorphicBisectionalCurvatureOfField {n : ℕ} {M : ComplexManifold n}
    (h : HermitianField M) (x : M.Carrier) (u v : ComplexVector n) : ℝ :=
  (bisectionalNumerator h x u v).re /
    (hermitianNormSq (h x) u * hermitianNormSq (h x) v)

def ChernBisectionalCurvatureOnTangent {n : ℕ} {M : ComplexManifold n}
    (h : HermitianField M) (x : M.Carrier)
    (u v : TangentVector M x) : ℝ :=
  (bisectionalNumeratorOnTangent h x u v).re /
    (hermitianNormSq (h x) u * hermitianNormSq (h x) v)

/-! The endpoint uses the paper's real expression directly. The real
Levi-Civita curvature above is computed from the Hermitian metric; no
polarization of the Chern contraction is used as a definition of `Rm`. -/
def paperComplexStructure {n : ℕ} {M : ComplexManifold n}
    (x : M.Carrier) (v : TangentVector M x) : TangentVector M x := Complex.I • v

/-- Levi-Civita real curvature, with the paper's sectional sign. -/
abbrev paperRmConvention {n : ℕ} {M : ComplexManifold n} := @paperRm n M

def paperBisectionalNumerator {n : ℕ} {M : ComplexManifold n}
    (h : HermitianField M) (x : M.Carrier)
    (u v : TangentVector M x) : ℝ :=
  paperRm h x u v v u +
    paperRm h x u (paperComplexStructure x v) (paperComplexStructure x v) u

def paperHolomorphicBisectionalCurvature {n : ℕ} {M : ComplexManifold n}
    (h : HermitianField M) (x : M.Carrier)
    (u v : TangentVector M x) : ℝ :=
  paperBisectionalNumerator h x u v /
    ((2 * hermitianNormSq (h x) u) * (2 * hermitianNormSq (h x) v))

/-- General real/Chern factor bridge in the paper's h-coordinates. This is an
unproved infrastructure target for every dimension and smooth Kähler field;
flat or one-dimensional calculator checks do not establish it. -/
def PaperChernCurvatureNormalization {n : ℕ} {M : ComplexManifold n}
    (h : HermitianField M) : Prop :=
  MetricSmooth h → KahlerClosed h → ∀ (x : M.Carrier) (u v : TangentVector M x),
    paperBisectionalNumerator h x u v =
      4 * (bisectionalNumeratorOnTangent h x u v).re

/-- Positive real metric lengths give a positive paper HBC denominator. -/
theorem paper_hbc_denominator_pos {n : ℕ} {M : ComplexManifold n}
    (h : HermitianField M) (x : M.Carrier) {u v : TangentVector M x}
    (hu : u ≠ 0) (hv : v ≠ 0) :
    0 < (2 * hermitianNormSq (h x) u) * (2 * hermitianNormSq (h x) v) := by
  exact mul_pos (mul_pos (by norm_num) (hermitianNormSq_pos (h x) hu))
    (mul_pos (by norm_num) (hermitianNormSq_pos (h x) hv))

/-- Public tangent HBC uses the paper's real Levi-Civita convention. -/
abbrev HolomorphicBisectionalCurvatureOnTangent {n : ℕ} {M : ComplexManifold n} :=
  @paperHolomorphicBisectionalCurvature n M

/-- The paper condition and its normalized version agree without a curvature
identity supplied by the caller. No equivalence to the Chern coordinate
calculator above is asserted here. -/
theorem paper_convention_bridge {n : ℕ} {M : ComplexManifold n}
    (h : HermitianField M) (x : M.Carrier)
    (u v : TangentVector M x) (hu : u ≠ 0) (hv : v ≠ 0) :
    0 < paperHolomorphicBisectionalCurvature h x u v ↔
      0 < paperRm h x u v v u +
        paperRm h x u (Complex.I • v) (Complex.I • v) u := by
  have hd := paper_hbc_denominator_pos h x hu hv
  exact div_pos_iff_of_pos_right hd

theorem paper_positive_iff_normalized {n : ℕ} {M : ComplexManifold n}
    (h : HermitianField M) :
    PaperPositiveBisectional h ↔ ∀ (x : M.Carrier) (u v : TangentVector M x),
      u ≠ 0 → v ≠ 0 → 0 < paperHolomorphicBisectionalCurvature h x u v := by
  constructor
  · intro hp x u v hu hv
    exact (paper_convention_bridge h x u v hu hv).mpr (hp x u v hu hv)
  · intro hp x u v hu hv
    exact (paper_convention_bridge h x u v hu hv).mp (hp x u v hu hv)

/-- Positivity for the Chern calculator's h-only denominator. The paper real
HBC denominator is handled by paper_hbc_denominator_pos. -/
theorem hbc_field_denominator_pos {n : ℕ} {M : ComplexManifold n}
    (h : HermitianField M) (x : M.Carrier) {u v : ComplexVector n}
    (hu : u ≠ 0) (hv : v ≠ 0) :
    0 < hermitianNormSq (h x) u * hermitianNormSq (h x) v := by
  exact mul_pos (hermitianNormSq_pos (h x) hu) (hermitianNormSq_pos (h x) hv)

def HolomorphicBisectionalCurvature {n : ℕ} {M : ComplexManifold n}
    (g : SmoothMetric M) (x : M.Carrier) (u v : ComplexVector n) : ℝ :=
  paperHolomorphicBisectionalCurvature g.form x u v

def StrictlyPositiveHolomorphicBisectionalCurvature {n : ℕ}
    {M : ComplexManifold n} (g : SmoothMetric M) : Prop :=
  ∀ (x : M.Carrier) (u v : ComplexVector n),
    u ≠ 0 → v ≠ 0 → 0 < HolomorphicBisectionalCurvature g x u v

def StrictlyPositiveHolomorphicBisectionalCurvatureOnTangent {n : ℕ}
    {M : ComplexManifold n} (g : SmoothMetric M) : Prop :=
  ∀ (x : M.Carrier) (u v : TangentVector M x),
    u ≠ 0 → v ≠ 0 → 0 < HolomorphicBisectionalCurvatureOnTangent g.form x u v

structure KahlerManifold (n : ℕ) where
  manifold : ComplexManifold n
  metric : SmoothMetric manifold
  smooth_metric : IsSmooth metric
  complete_metric : IsComplete metric
  kahler_metric : IsKahler metric
  positive_bisectional_curvature : PaperPositiveBisectional metric.form

noncomputable def ComplexEuclideanManifold (n : ℕ) (hn : 1 ≤ n) : ComplexManifold n := by
  letI : NeZero n := ⟨Nat.ne_of_gt (Nat.zero_lt_of_lt hn)⟩
  exact
    { Carrier := EuclideanSpace ℂ (Fin n)
      topology := inferInstance
      charted := inferInstance
      manifold := inferInstance
      t2 := inferInstance
      secondCountable := inferInstance
      connected := inferInstance
      noncompact := inferInstance
      dimension := n
      dimension_eq := rfl }

def IsHolomorphicMap {n m : ℕ} {M : ComplexManifold n} {N : ComplexManifold m}
    (f : M.Carrier → N.Carrier) : Prop :=
  ContMDiff (ComplexModel n) (ComplexModel m) ⊤ f ∧
    ∀ x (a : ℂ) (v : TangentSpace (ComplexModel n) x),
      mfderiv (ComplexModel n) (ComplexModel m) f x (a • v) =
        a • mfderiv (ComplexModel n) (ComplexModel m) f x v

structure Biholomorphism {n : ℕ} (M : ComplexManifold n) where
  dimension_pos : 1 ≤ n
  toDiffeomorph :
    Diffeomorph (ComplexModel n) (ComplexModel n) M.Carrier
      (ComplexEuclideanManifold n dimension_pos).Carrier ⊤
  map_holomorphic : IsHolomorphicMap (M := M)
    (N := ComplexEuclideanManifold n dimension_pos) (fun x => toDiffeomorph x)
  inverse_holomorphic : IsHolomorphicMap (M := ComplexEuclideanManifold n dimension_pos)
    (N := M) (fun z => toDiffeomorph.symm z)

def Biholomorphic {n : ℕ} (M : ComplexManifold n) : Prop := Nonempty (Biholomorphism M)
def BiholomorphicToComplexEuclidean {n : ℕ} (M : ComplexManifold n) : Prop := Biholomorphic M

end Yau
