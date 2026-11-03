import Yau.Geometry.Basic

/-!
# Computed operators for the paper contracts

The operators in this file are written in holomorphic charts of `M`, with the paper's
matrix convention (`introduction.tex:226-246`, `discs.tex:66-88`): a Hermitian form with
matrix `W` has quadratic value `v^* W v`.  Hence

* the metric matrix is the Gram matrix `h_{ab} = h(∂_a, ∂_b)` (`h` conjugate-linear first),
* the Levi matrix of a real function is `L_{ab} = ∂_b ∂̄_a f`, so `v^*Lv = Σ f_{a\bar b} v_a \bar v_b`,
* `tr_h A = tr(h⁻¹ A)`, `Δ_h f = tr_h ∂∂̄ f`, `Ric(h) = -∂∂̄ log det h`,
* the dual (cotangent) metric has column matrix `b = h^{-T}`, `N = ξ^* b ξ`.

Forms are ordered by `Matrix.PosSemidef` of the difference (Loewner order).
Metric inputs are Hermitian fields. Regularity and admissibility predicates below
constrain the displayed formulas; curvature and differential operators are never
independent data. The real Levi-Civita convention used by the endpoint lives in
`Basic`; no equivalence with the Chern calculator is assumed here.
-/

open scoped Manifold Topology ContDiff Matrix ComplexOrder
open MeasureTheory

noncomputable section

namespace Yau

variable {n : ℕ} {M : ComplexManifold n}

/-! ## Wirtinger calculus on complex vector spaces -/

/-- Standard basis vector of `ℂⁿ`. -/
def stdVec (i : Fin n) : ComplexVector n := EuclideanSpace.single i 1

/-- `∂_v f(z) = ½ (D f(z) v - i D f(z)(i v))` for a complex direction `v`. -/
def wirt {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (f : V → ℂ) (z v : V) : ℂ :=
  (1 / 2 : ℂ) * (fderiv ℝ f z v - Complex.I * fderiv ℝ f z (Complex.I • v))

/-- `∂̄_v f(z) = ½ (D f(z) v + i D f(z)(i v))`. -/
def wirtBar {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (f : V → ℂ) (z v : V) : ℂ :=
  (1 / 2 : ℂ) * (fderiv ℝ f z v + Complex.I * fderiv ℝ f z (Complex.I • v))

/-- Paper-convention Levi (complex Hessian) matrix of a real function in the complex
directions `dir`: entry `(a,b)` is `∂_{dir b} ∂̄_{dir a} f`, so `v^* L v = Σ f_{a\bar b} v_a \bar v_b`. -/
def leviMatrix {V ι : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (f : V → ℝ) (z : V) (dir : ι → V) : Matrix ι ι ℂ :=
  fun a b => wirt (fun w => wirtBar (fun u => (f u : ℂ)) w (dir a)) z (dir b)

/-- Levi matrix on `ℂⁿ` in the standard directions. -/
def leviC (f : ComplexVector n → ℝ) (z : ComplexVector n) : Matrix (Fin n) (Fin n) ℂ :=
  leviMatrix f z stdVec

/-! ## Chart expressions -/

def inChart {α : Type*} (x : M.Carrier) (f : M.Carrier → α) : ComplexVector n → α :=
  fun z => f (chartInv x z)

/-- `f` is `C^∞` in every chart. -/
def SmoothFn (f : M.Carrier → ℝ) : Prop :=
  ∀ x : M.Carrier, ContDiffOn ℝ ∞ (inChart x f) (chartTarget x)

/-- `f(x,t)` is jointly `C^∞` on `M × I` (one-sided derivatives at endpoints of `I`). -/
def SmoothSpaceTime (f : M.Carrier → ℝ → ℝ) (I : Set ℝ) : Prop :=
  ∀ x : M.Carrier, ContDiffOn ℝ ∞ (fun p : ComplexVector n × ℝ => f (chartInv x p.1) p.2)
    (chartTarget x ×ˢ I)

/-- Levi matrix of a real function at `x`, chart centred at `x`. -/
def levi (f : M.Carrier → ℝ) (x : M.Carrier) : Matrix (Fin n) (Fin n) ℂ :=
  leviC (inChart x f) (chartPt x x)

/-! ## Metric, trace, Laplacian, Ricci -/

/-- Gram matrix `h(∂_a, ∂_b)` of the chart-`x` frame at the point with coordinates `z`. -/
def hMat (h : HermitianField M) (x : M.Carrier) (z : ComplexVector n) : Matrix (Fin n) (Fin n) ℂ :=
  fun a b => (h (chartInv x z)).toFun (chartVec x (chartInv x z) (stdVec a))
    (chartVec x (chartInv x z) (stdVec b))

/-- Metric matrix at `x` in the chart centred at `x`. -/
def gMat (h : HermitianField M) (x : M.Carrier) : Matrix (Fin n) (Fin n) ℂ :=
  hMat h x (chartPt x x)

/-- `tr_H A = tr(H⁻¹ A)` (real part; both Hermitian). -/
def traceWith (H A : Matrix (Fin n) (Fin n) ℂ) : ℝ := (Matrix.trace (H⁻¹ * A)).re

/-- `Δ_h f = tr_h ∂∂̄ f` at `x`. -/
def laplacian (h : HermitianField M) (f : M.Carrier → ℝ) (x : M.Carrier) : ℝ :=
  traceWith (gMat h x) (levi f x)

/-- `log det h` in the chart centred at `x`. -/
def logDet (h : HermitianField M) (x : M.Carrier) (z : ComplexVector n) : ℝ :=
  Real.log (hMat h x z).det.re

/-- Ricci form `Ric(h) = -∂∂̄ log det h` at `x` (paper convention). -/
def ricci (h : HermitianField M) (x : M.Carrier) : Matrix (Fin n) (Fin n) ℂ :=
  -leviC (logDet h x) (chartPt x x)

/-- Scalar curvature `R_h = tr_h Ric(h)`. -/
def scalarCurvature (h : HermitianField M) (x : M.Carrier) : ℝ :=
  traceWith (gMat h x) (ricci h x)

/-- Least eigenvalue of `A` relative to `H` (`H > 0`): `inf_{v ≠ 0} v^*Av / v^*Hv`. -/
def relMinEigenvalue (H A : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  ⨅ v : {v : ComplexVector n // v ≠ 0},
    (star (WithLp.ofLp v.1) ⬝ᵥ (A *ᵥ WithLp.ofLp v.1)).re /
      (star (WithLp.ofLp v.1) ⬝ᵥ (H *ᵥ WithLp.ofLp v.1)).re

/-- Complex (Chern) curvature `R_{i\bar j k\bar l}` at `x`, with `g_{i\bar j} = h_{ji}` and
`R_{i\bar j k\bar l} = -∂_k∂̄_l g_{i\bar j} + g^{p\bar q} ∂_k g_{i\bar q} ∂̄_l g_{p\bar j}`. -/
def chernCurvature (h : HermitianField M) (x : M.Carrier) (i j k l : Fin n) : ℂ :=
  -(wirt (fun w => wirtBar (fun u => hMat h x u j i) w (stdVec l)) (chartPt x x) (stdVec k)) +
    ∑ p, ∑ q, (gMat h x)⁻¹ p q *
      wirt (fun u => hMat h x u q i) (chartPt x x) (stdVec k) *
      wirtBar (fun u => hMat h x u j p) (chartPt x x) (stdVec l)

/-- `R(ξ, \bar ξ, η, \bar η)` for `ξ, η ∈ T^{1,0}_x` in chart coordinates. -/
def bisectionalForm (h : HermitianField M) (x : M.Carrier) (ξ η : ComplexVector n) : ℝ :=
  (∑ i, ∑ j, ∑ k, ∑ l, chernCurvature h x i j k l * ξ i * star (ξ j) * η k * star (η l)).re

/-- Griffiths strict positivity of `T^{1,0}M` (complex form of positive bisectional curvature). -/
def GriffithsPositive (h : HermitianField M) : Prop :=
  ∀ (x : M.Carrier) (ξ η : ComplexVector n), ξ ≠ 0 → η ≠ 0 → 0 < bisectionalForm h x ξ η

/-- Nonnegative holomorphic bisectional curvature. -/
def NonnegBisectional (h : HermitianField M) : Prop :=
  ∀ (x : M.Carrier) (ξ η : ComplexVector n), 0 ≤ bisectionalForm h x ξ η

/-! ## Cotangent vectors and the dual norm -/

/-- Holomorphic cotangent vectors at any point (`T_y M = ℂⁿ` in Mathlib). -/
abbrev Covector (n : ℕ) := ComplexVector n →L[ℂ] ℂ

/-- Chart-`x` coordinates `ξ(∂_i)` of a covector `ξ ∈ T^*_y M`. -/
def covectorCoords (x y : M.Carrier) (ξ : Covector n) : ComplexVector n :=
  WithLp.toLp 2 (fun i => ξ (chartVec x y (stdVec i)))

/-- The covector at `y` with chart-`x` coordinates `η`. -/
def covectorOfCoords (x y : M.Carrier) (η : ComplexVector n) : Covector n :=
  (∑ i, η i • (EuclideanSpace.proj i : ComplexVector n →L[ℂ] ℂ)).comp
    (tangentCoordChange (ComplexModel n) y x y)

/-- Dual squared norm `ξ^* h^{-T} ξ` of coordinates `ξ` w.r.t. a metric matrix `H`. -/
def dualNormMat (H : Matrix (Fin n) (Fin n) ℂ) (ξ : ComplexVector n) : ℝ :=
  (star (WithLp.ofLp ξ) ⬝ᵥ ((H⁻¹)ᵀ *ᵥ WithLp.ofLp ξ)).re

/-- `N(y, ξ, h) = |ξ|²_{h^{-1}}` for a covector at `y`. -/
def dualNorm (h : HermitianField M) (y : M.Carrier) (ξ : Covector n) : ℝ :=
  dualNormMat (gMat h y) (covectorCoords y y ξ)

/-- `N` in induced cotangent coordinates `(z, ξ)` of the chart centred at `x`. -/
def dualNormChart (h : HermitianField M) (x : M.Carrier) (z ξ : ComplexVector n) : ℝ :=
  dualNormMat (hMat h x z) ξ

/-! ## Functions on `M`: holomorphic objects -/

def IsHolomorphicFn (f : M.Carrier → ℂ) : Prop := MDifferentiable (ComplexModel n) 𝓘(ℂ, ℂ) f

def IsHolomorphicVecMap {N : ℕ} (F : M.Carrier → ComplexVector N) : Prop :=
  MDifferentiable (ComplexModel n) (ComplexModel N) F

/-- Pointwise injective differential. -/
def IsImmersionMap {N : ℕ} (F : M.Carrier → ComplexVector N) : Prop :=
  ∀ x, Function.Injective (mfderiv (ComplexModel n) (ComplexModel N) F x)

/-- Vector fields (sections of `TM = T^{1,0}M`). -/
abbrev VectorField (M : ComplexManifold n) := (x : M.Carrier) → TangentSpace (ComplexModel n) x

def IsHolomorphicField (X : VectorField M) : Prop :=
  MDifferentiable (ComplexModel n) (ComplexModel n).tangent
    (fun x => (⟨x, X x⟩ : TangentBundle (ComplexModel n) M.Carrier))

/-- `f` agrees to order `k` at `p` with the polynomial `P` in chart-`p` coordinates centred
at `p` (all complex derivatives of order `≤ k` of the difference vanish). -/
def JetAgreeFn (f : M.Carrier → ℂ) (p : M.Carrier) (P : MvPolynomial (Fin n) ℂ) (k : ℕ) : Prop :=
  ∀ j ≤ k, iteratedFDeriv ℂ j
    (fun z => inChart p f z - MvPolynomial.eval (fun i => z i - chartPt p p i) P) (chartPt p p) = 0

/-- Chart-`p` components of a vector field. -/
def fieldCoords (X : VectorField M) (p : M.Carrier) (z : ComplexVector n) : ComplexVector n :=
  tangentCoords p (chartInv p z) (X (chartInv p z))

def JetAgreeField (X : VectorField M) (p : M.Carrier) (P : Fin n → MvPolynomial (Fin n) ℂ)
    (k : ℕ) : Prop :=
  ∀ j ≤ k, iteratedFDeriv ℂ j
    (fun z => fieldCoords X p z -
      WithLp.toLp 2 (fun i => MvPolynomial.eval (fun l => z l - chartPt p p l) (P i)))
    (chartPt p p) = 0

/-- Sections of the canonical bundle `K_M = Λ^n T^{*(1,0)}M`. -/
abbrev CanonicalSection (M : ComplexManifold n) :=
  (x : M.Carrier) → (TangentSpace (ComplexModel n) x) [⋀^Fin n]→L[ℂ] ℂ

def canonicalCoeff (S : CanonicalSection M) (x : M.Carrier) (z : ComplexVector n) : ℂ :=
  S (chartInv x z) (fun i => chartVec x (chartInv x z) (stdVec i))

def IsHolomorphicCanonical (S : CanonicalSection M) : Prop :=
  ∀ x, DifferentiableOn ℂ (canonicalCoeff S x) (chartTarget x)

/-- `|S|²_g = |s|² / det g` at `y` (chart centred at `y`). -/
def canonicalNormSq (g : HermitianField M) (S : CanonicalSection M) (y : M.Carrier) : ℝ :=
  ‖canonicalCoeff S y (chartPt y y)‖ ^ 2 / (gMat g y).det.re

/-- `|∂u|²_g`, the dual norm of the `(1,0)`-form `∂u`. -/
def gradNormSq (g : HermitianField M) (u : M.Carrier → ℝ) (y : M.Carrier) : ℝ :=
  dualNormMat (gMat g y)
    (WithLp.toLp 2 (fun i => wirt (fun z => (Complex.ofReal (inChart y u z))) (chartPt y y) (stdVec i)))

/-! ## Distance balls and the Riemannian volume -/

def distBall (h : HermitianField M) (o : M.Carrier) (L : ℝ) : Set M.Carrier :=
  {x | lengthEDist h o x < ENNReal.ofReal L}

/-- `r(x) = d_h(o, x)`. -/
def distFrom (h : HermitianField M) (o x : M.Carrier) : ℝ := lengthDist h o x

instance (M : ComplexManifold n) : MeasurableSpace M.Carrier := borel M.Carrier
instance (M : ComplexManifold n) : BorelSpace M.Carrier := ⟨rfl⟩

/-- Lebesgue measure on `ℂⁿ` in the real coordinates of `realVec`. -/
def lebesgueC (n : ℕ) : Measure (ComplexVector n) :=
  Measure.map (fun r : RIdx n → ℝ => ∑ a, r a • realVec a) volume

/-- `μ` is the Riemannian volume of `h`: on every chart it is `√det G · dLeb`. -/
def IsRiemannianVolume (h : HermitianField M) (μ : Measure M.Carrier) : Prop :=
  ∀ (x : M.Carrier) (s : Set M.Carrier), MeasurableSet s →
    s ⊆ (chartAt (ComplexVector n) x).source →
    μ s = ∫⁻ z in chartPt x '' s, ENNReal.ofReal (Real.sqrt (realMetricFn h x z).det) ∂lebesgueC n

/-- General length conversion to the real metric G=2 Re h. This target is
unproved: the chart/tangent reconstruction is needed for every curve, not just
a straight curve in a one-dimensional model. -/
def PaperLengthNormalization (h : HermitianField M) : Prop :=
  MetricSmooth h → ∀ {x y : M.Carrier} (γ : PiecewiseC1Curve x y),
    curveLength h γ = ∫ t in Set.Icc (0 : ℝ) 1,
      Real.sqrt (∑ a, ∑ b, realMetricFn h (γ t) (chartPt (γ t) (γ t)) a b *
        realCoord (tangentCoords (γ t) (γ t) (realTangentDerivative γ t)) a *
        realCoord (tangentCoords (γ t) (γ t) (realTangentDerivative γ t)) b)

/-- General coordinate volume factor for the same h, still unproved. Combined
with IsRiemannianVolume this gives density 2^n det(h) against real Lebesgue. -/
def PaperVolumeNormalization (h : HermitianField M) : Prop :=
  ∀ x z, z ∈ chartTarget x →
    Real.sqrt (realMetricFn h x z).det = (2 : ℝ) ^ n * (hMat h x z).det.re

/-- The paper complex cotangent norm is twice the real dual norm of Re ξ.
No rescaling of the complex covector is built into dualNorm. This general
inverse-metric/chart identity is an unproved infrastructure target. -/
def PaperDualNormNormalization (h : HermitianField M) : Prop :=
  ∀ (x : M.Carrier) (ξ : Covector n), dualNorm h x ξ =
    2 * ∑ a, ∑ b, (realMetricFn h x (chartPt x x))⁻¹ a b *
      (ξ (chartVec x x (realVec a))).re * (ξ (chartVec x x (realVec b))).re

/-- `∫_{B(o,L)} f dμ ≤ B · μ(B(o,L))` for a nonnegative integrand. -/
def BallIntegralLE (h : HermitianField M) (μ : Measure M.Carrier) (o : M.Carrier)
    (f : M.Carrier → ℝ) (L B : ℝ) : Prop :=
  ∫⁻ x in distBall h o L, ENNReal.ofReal (f x) ∂μ ≤ ENNReal.ofReal B * μ (distBall h o L)

/-! ## Time-dependent metrics and the Kähler–Ricci flow -/

/-- Jointly smooth family of Hermitian metrics on `M × I`. -/
def MetricFamilySmooth (h : ℝ → HermitianField M) (I : Set ℝ) : Prop :=
  ∀ (x : M.Carrier) (a b : RIdx n), ContDiffOn ℝ ∞
    (fun p : ComplexVector n × ℝ => realMetricFn (h p.2) x p.1 a b) (chartTarget x ×ˢ I)

/-- Smooth Kähler–Ricci flow `∂_t h = -Ric(h)` on `[0, ∞)` with `h_0 = g`
(one-sided time derivative at `t = 0`). -/
def IsKahlerRicciFlow (g : HermitianField M) (h : ℝ → HermitianField M) : Prop :=
  h 0 = g ∧ MetricFamilySmooth h (Set.Ici 0) ∧ (∀ t, 0 ≤ t → KahlerClosed (h t)) ∧
    ∀ (x : M.Carrier) (t : ℝ), 0 ≤ t → ∀ a b : Fin n,
      HasDerivWithinAt (fun s => gMat (h s) x a b) (-(ricci (h t) x a b)) (Set.Ici 0) t

/-! ## Viscosity inequalities for scalar parabolic operators on `M × (0,T)` -/

/-- `φ` is a `C^∞` test function near `(x₀,t₀)` (in the chart centred at `x₀`). -/
def SmoothNear (φ : M.Carrier → ℝ → ℝ) (x₀ : M.Carrier) (t₀ : ℝ) : Prop :=
  ContDiffAt ℝ ∞ (fun p : ComplexVector n × ℝ => φ (chartInv x₀ p.1) p.2) (chartPt x₀ x₀, t₀)

/-- `φ ≥ v` near `(x₀,t₀)` with equality there (touching from above). -/
def TouchesAbove (φ v : M.Carrier → ℝ → ℝ) (x₀ : M.Carrier) (t₀ : ℝ) : Prop :=
  φ x₀ t₀ = v x₀ t₀ ∧ ∀ᶠ p in 𝓝 (x₀, t₀), v p.1 p.2 ≤ φ p.1 p.2

/-- `φ ≤ v` near `(x₀,t₀)` with equality there (touching from below). -/
def TouchesBelow (φ v : M.Carrier → ℝ → ℝ) (x₀ : M.Carrier) (t₀ : ℝ) : Prop :=
  φ x₀ t₀ = v x₀ t₀ ∧ ∀ᶠ p in 𝓝 (x₀, t₀), φ p.1 p.2 ≤ v p.1 p.2

def timeDeriv (φ : M.Carrier → ℝ → ℝ) (x : M.Carrier) (t : ℝ) : ℝ := deriv (fun s => φ x s) t

/-- `∂_t v ≤ e^{-v} Δ_{h_t} v + (1 - e^{-v}) R_{h_t}` in the upper viscosity sense on
`M × (0,T)` (`flow.tex:539-546`). -/
def NonlinearViscositySub (h : ℝ → HermitianField M) (T : ℝ) (v : M.Carrier → ℝ → ℝ) : Prop :=
  ∀ (x₀ : M.Carrier) (t₀ : ℝ), 0 < t₀ → t₀ < T → ∀ φ : M.Carrier → ℝ → ℝ,
    SmoothNear φ x₀ t₀ → TouchesAbove φ v x₀ t₀ →
      timeDeriv φ x₀ t₀ ≤ Real.exp (-v x₀ t₀) * laplacian (h t₀) (fun y => φ y t₀) x₀ +
        (1 - Real.exp (-v x₀ t₀)) * scalarCurvature (h t₀) x₀

/-! ## Plurisubharmonic functions and holomorphic discs -/

/-- Normalized circle average `(2π)⁻¹ ∫₀^{2π} φ`. -/
def circleAverage (φ : ℝ → ℝ) : ℝ := (2 * Real.pi)⁻¹ * ∫ θ in (0 : ℝ)..(2 * Real.pi), φ θ

/-- Plurisubharmonic (possibly `-∞`-valued, not necessarily continuous): upper semicontinuous
and sub-mean-valued on every closed complex-affine disc in every chart.  The mean is tested
against continuous real majorants on the circle, which is equivalent for usc functions. -/
def IsPsh (u : M.Carrier → EReal) : Prop :=
  (∀ x, u x < ⊤) ∧ UpperSemicontinuous u ∧
    ∀ (x : M.Carrier) (z w : ComplexVector n),
      (∀ ζ : ℂ, ‖ζ‖ ≤ 1 → z + ζ • w ∈ chartTarget x) →
      ∀ φ : ℝ → ℝ, Continuous φ →
        (∀ θ : ℝ, u (chartInv x (z + Complex.exp (θ * Complex.I) • w)) ≤ (φ θ : EReal)) →
        u (chartInv x z) ≤ (circleAverage φ : EReal)

/-- Smooth strictly plurisubharmonic real function. -/
def IsSmoothStrictPsh (f : M.Carrier → ℝ) : Prop :=
  SmoothFn f ∧ ∀ x, (levi f x).PosDef

/-- Holomorphic disc `f : Δ̄ → M`, holomorphic on `Δ` and smooth up to the circle. -/
def IsHolomorphicDisc (f : ℂ → M.Carrier) : Prop :=
  ContMDiffOn 𝓘(ℂ, ℂ) (ComplexModel n) ∞ f (Metric.closedBall 0 1)

/-- Paper area `∫_Δ f^*ω_g = 2 ∫_Δ h(f',f') dA`, for ω=2 Im h.
The identification with the actual holomorphic pullback is an unproved bridge. -/
def discArea (g : HermitianField M) (f : ℂ → M.Carrier) : ENNReal :=
  2 * ∫⁻ ζ in Metric.ball (0 : ℂ) 1,
    ENNReal.ofReal (hermitianNormSq (g (f ζ)) (mfderiv 𝓘(ℂ, ℂ) (ComplexModel n) f ζ
      ((tangentSpaceCastModel 𝓘(ℂ, ℂ) ζ).symm 1)))

/-- Actual pullback of the computed Kähler form on the two real disc basis
vectors (1,i), expressed in the chart centred at f(ζ). -/
def pullbackKahlerDensity (g : HermitianField M) (f : ℂ → M.Carrier) (ζ : ℂ) : ℝ :=
  let df := mfderiv 𝓘(ℂ, ℂ) (ComplexModel n) f ζ
  let one := (tangentSpaceCastModel 𝓘(ℂ, ℂ) ζ).symm 1
  let imag := (tangentSpaceCastModel 𝓘(ℂ, ℂ) ζ).symm Complex.I
  ∑ a, ∑ b, kahlerFormFn g (f ζ) (chartPt (f ζ) (f ζ)) a b *
    realCoord (tangentCoords (f ζ) (f ζ) (df one)) a *
    realCoord (tangentCoords (f ζ) (f ζ) (df imag)) b

/-- General holomorphic pullback/area bridge, unproved for all dimensions and
all holomorphic discs. The flat identity disc check alone does not prove it. -/
def PaperDiscAreaNormalization (g : HermitianField M) : Prop :=
  MetricSmooth g → ∀ f : ℂ → M.Carrier, IsHolomorphicDisc f →
    (∀ ζ ∈ Metric.ball (0 : ℂ) 1, pullbackKahlerDensity g f ζ =
      2 * hermitianNormSq (g (f ζ)) (mfderiv 𝓘(ℂ, ℂ) (ComplexModel n) f ζ
        ((tangentSpaceCastModel 𝓘(ℂ, ℂ) ζ).symm 1))) ∧
    discArea g f = ∫⁻ ζ in Metric.ball (0 : ℂ) 1,
      ENNReal.ofReal (pullbackKahlerDensity g f ζ)

/-- A holomorphic disc in `Y = T^{*(1,0)}M`: a disc `f` in `M` with a covector `ξ ζ ∈ T^*_{f ζ}M`
whose coordinates in every chart are holomorphic up to the circle. -/
def IsCotangentDisc (f : ℂ → M.Carrier) (ξ : ℂ → Covector n) : Prop :=
  IsHolomorphicDisc f ∧ ∀ ζ₀ ∈ Metric.closedBall (0 : ℂ) 1,
    ContDiffWithinAt ℂ ∞ (fun ζ => covectorCoords (f ζ₀) (f ζ) (ξ ζ)) (Metric.closedBall 0 1) ζ₀

/-- `{(x, ξ) : x ∈ K, N(x, ξ, g) ≤ R}`, the compact subsets of `Y` used for boundary walls. -/
def InCotangentCompact (g : HermitianField M) (K : Set M.Carrier) (R : ℝ) (x : M.Carrier)
    (ξ : Covector n) : Prop :=
  x ∈ K ∧ dualNorm g x ξ ≤ R

/-- The raw disc envelope `v^raw(y,s)` of `discs.tex:17-29`. -/
def envelopeRaw (h : ℝ → HermitianField M) (T : ℝ) (y : M.Carrier) (ξ : Covector n) (s : ℝ) :
    EReal :=
  ⨅ (f : ℂ → M.Carrier) (ξd : ℂ → Covector n) (w : ℂ → ℂ)
    (_ : 0 < s ∧ s < T ∧ IsCotangentDisc f ξd ∧ ContDiffOn ℂ ∞ w (Metric.closedBall 0 1) ∧ f 0 = y ∧ ξd 0 = ξ ∧
      w 0 = 0 ∧ ∀ ζ ∈ Metric.closedBall (0 : ℂ) 1, s * Real.exp (2 * (w ζ).re) < T),
    ((circleAverage fun θ =>
        dualNorm (h (s * Real.exp (2 * (w (Complex.exp (θ * Complex.I))).re)))
          (f (Complex.exp (θ * Complex.I))) (ξd (Complex.exp (θ * Complex.I))) : ℝ) : EReal)

/-- The envelope in induced cotangent coordinates of the chart centred at `x`. -/
def envelopeRawChart (h : ℝ → HermitianField M) (T : ℝ) (x : M.Carrier)
    (p : ComplexVector n × ComplexVector n × ℝ) : EReal :=
  envelopeRaw h T (chartInv x p.1) (covectorOfCoords x (chartInv x p.1) p.2.1) p.2.2

/-- Lower semicontinuous regularization `v(y,s)` of the envelope (`discs.tex:29`). -/
def envelopeChart (h : ℝ → HermitianField M) (T : ℝ) (x : M.Carrier)
    (p : ComplexVector n × ComplexVector n × ℝ) : EReal :=
  Filter.liminf (envelopeRawChart h T x)
    (𝓝[ {q : ComplexVector n × ComplexVector n × ℝ |
      q.1 ∈ chartTarget x ∧ 0 < q.2.2 ∧ q.2.2 < T} ] p)

def envelope (h : ℝ → HermitianField M) (T : ℝ) (y : M.Carrier) (ξ : Covector n) (s : ℝ) :
    EReal :=
  envelopeChart h T y (chartPt y y, covectorCoords y y ξ, s)

/-! ## Symplectic Hessian operator (`discs.tex:61-88`) -/

/-- Directions `(e_i, 0)` and `(0, e_i)` of induced cotangent coordinates `(z, ξ)`. -/
def cotangentDir : Fin n ⊕ Fin n → ComplexVector n × ComplexVector n :=
  Sum.elim (fun i => (stdVec i, 0)) (fun i => (0, stdVec i))

/-- `p(W) = tr(A Cᵀ) - Σ B_{ij} \overline{B_{ji}}` for `W = [[A, B], [B^*, C]]`. -/
def symplecticP (W : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ) : ℝ :=
  (Matrix.trace (W.toBlocks₁₁ * W.toBlocks₂₂ᵀ) -
    ∑ i, ∑ j, W.toBlocks₁₂ i j * star (W.toBlocks₁₂ j i)).re

/-- Schur complement `A - B C⁻¹ B^*` of the vertical block. -/
def schurComplement (W : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  W.toBlocks₁₁ - W.toBlocks₁₂ * W.toBlocks₂₂⁻¹ * W.toBlocks₁₂ᴴ

end Yau
