import Yau.Geometry.Calculus
import spec.CHAIN.OperatorCandidates
import spec.CHAIN.ParabolicCandidates
import spec.CHAIN.DbarCandidates

/-!
Independent aggregate of planning targets. No external input is admitted here.
Neither the main proof nor its contracts import this module. L22 is a proposed
source input pending independent approval under D2; consumer bridges remain
internal. `LeafObligations.lean` closes all parameters
and groups the 22 active DAG leaves; `LEAF_TARGETS.json` is their exact registry.
Source equivalence and consumer bridges remain pending in `LEAF_LOCKS.md` and
the three specialist locks. Shared citations do not create extra assumptions.
-/
open MeasureTheory Filter
open scoped Topology Asymptotics InnerProductSpace Manifold ContDiff Matrix ComplexOrder Matrix.Norms.Frobenius
noncomputable section
namespace Yau.LeafCandidates

abbrev RV (m : ℕ) := EuclideanSpace ℝ (Fin m)

/-- Local form needed for semiconcave inf-convolutions, after negating and
subtracting a quadratic. Global convexity alone does not cover this use. -/
def Aleksandrov : Prop :=
  ∀ (m : ℕ) (O : Set (RV m)) (f : RV m → ℝ),
    IsOpen O → ConvexOn ℝ O f →
    ∀ᵐ x ∂((volume : Measure (RV m)).restrict O),
      ∃ (p : RV m →L[ℝ] ℝ) (A : RV m →L[ℝ] RV m →L[ℝ] ℝ),
        (∀ v w, A v w = A w v) ∧
        (fun y => f y - f x - p (y - x) - (1 / 2) * A (y - x) (y - x)) =o[𝓝 x]
          (fun y => ‖y - x‖ ^ 2)

/-- L04 contact target with a boundary gap, as consumed at ellipsoids:243-270.
It does not assume a strict isolated extremum and adds no strictifying quadratic
to the touching test. Negation converts semiconcavity to convexity. -/
def Jensen : Prop :=
  ∀ (m : ℕ) (φ : RV m → ℝ) (lam : ℝ) (xh : RV m) (r : ℝ) (O : Set (RV m)),
    0 < r → IsOpen O → xh ∈ O → IsCompact (closure O) →
    closure O ⊆ Metric.ball xh r →
    ConvexOn ℝ (Metric.ball xh (2 * r)) (fun x => -φ x + lam / 2 * ‖x‖ ^ 2) →
    (∀ y ∈ closure O \ O, φ xh < φ y) →
    ∃ δ₀, 0 < δ₀ ∧ ∀ δ, 0 < δ → δ ≤ δ₀ →
      0 < volume {x | x ∈ O ∧ ∃ p : RV m, ‖p‖ ≤ δ ∧
        ∀ y ∈ closure O, φ x - ⟪p, x⟫_ℝ ≤ φ y - ⟪p, y⟫_ℝ}

/-- The elementary compact minimization part of L04, not another external leaf. -/
def InfConvolutionAttainment : Prop :=
  ∀ (m : ℕ) (K : Set (RV m)) (v : RV m → ℝ),
    IsCompact K → K.Nonempty → LowerSemicontinuousOn v K →
    ∀ q : RV m, ∀ κ : ℝ, 0 < κ →
      ∃ z ∈ K, ∀ w ∈ K, v z + ‖q - z‖ ^ 2 / (2 * κ) ≤
        v w + ‖q - w‖ ^ 2 / (2 * κ)

variable {n : ℕ} {M : Yau.ComplexManifold n}

/-- P02's viscosity predicate, using global C∞ upper tests and compact-uniform
strict Levi lower bounds. This is not the classical premise of L22. In
particular, a pointwise `HermitianField` has no continuity built into its type. -/
def ContinuousStrictPsh (h : Yau.HermitianField M) (u : M.Carrier → ℝ) : Prop :=
  Continuous u ∧ ∀ K : Set M.Carrier, IsCompact K → ∃ ε : ℝ, 0 < ε ∧
    ∀ x ∈ K, ∀ φ : M.Carrier → ℝ,
      Yau.SmoothFn φ → φ x = u x → (∀ᶠ y in 𝓝 x, u y ≤ φ y) →
      (Yau.levi φ x - (ε : ℂ) • Yau.gMat h x).PosSemidef

/-- The classical continuous psh condition on an open coordinate domain: the
restriction to every complex-affine closed disc satisfies the circle submean
inequality. All discs, coordinate maps, and averages are the actual ones. -/
def ComplexLinePshOn (O : Set (Yau.ComplexVector n))
    (f : Yau.ComplexVector n → ℝ) : Prop :=
  ContinuousOn f O ∧ ∀ z w : Yau.ComplexVector n,
    (∀ ζ : ℂ, ‖ζ‖ ≤ 1 → z + ζ • w ∈ O) →
    f z ≤ Yau.circleAverage (fun θ => f (z + Complex.exp (θ * Complex.I) • w))

/-- Greene–Wu, §4, p.79, with η=0: locally subtract a smooth function whose
Levi form is positive at the base point and obtain a classical psh function.
The local function is represented by a total coordinate function, with no
condition outside its open domain. No background Hermitian field is needed. -/
def ClassicalStrictPsh (u : M.Carrier → ℝ) : Prop :=
  Continuous u ∧ ∀ p : M.Carrier,
    ∃ O : Set (Yau.ComplexVector n), IsOpen O ∧ Yau.chartPt p p ∈ O ∧
      O ⊆ Yau.chartTarget p ∧
      ∃ τ : Yau.ComplexVector n → ℝ,
        ContDiffOn ℝ ∞ τ O ∧ (Yau.leviC τ (Yau.chartPt p p)).PosDef ∧
          ComplexLinePshOn O (fun z => Yau.inChart p u z - τ z)

/-- L22: the first sentence of Greene–Wu, §4, Corollary 2 (p.80), on this
project's complex-manifold carriers. The C⁰ fine topology is expanded using
its p.49 definition. Both strict-psh occurrences use the classical definition;
viscosity conversion, computed-Levi conversion and one-sided errors are internal. -/
def RichbergApproximation : Prop :=
  ∀ (n : ℕ) (M : Yau.ComplexManifold n) (u ε : M.Carrier → ℝ),
    ClassicalStrictPsh u → Continuous ε → (∀ x, 0 < ε x) →
    ∃ ψ : M.Carrier → ℝ, Yau.SmoothFn ψ ∧ ClassicalStrictPsh ψ ∧
      ∀ x, |ψ x - u x| < ε x

/-- Concrete regularity needed by the internal P02 viscosity bridge. -/
def ContinuousHermitianCoefficients (h : Yau.HermitianField M) : Prop :=
  ∀ (p : M.Carrier) (i j : Fin n),
    ContinuousOn (Yau.chartCoefficientFunction h p i j) (Yau.chartTarget p)

/-- Unproved internal target, not a citation leaf: localize global upper tests,
use continuous positive metric coefficients, and pass from viscosity Levi
bounds to the classical complex-line submean definition. -/
def ViscosityToClassicalBridgeTarget : Prop :=
  ∀ (n : ℕ) (M : Yau.ComplexManifold n) (h : Yau.HermitianField M)
    (u : M.Carrier → ℝ),
    ContinuousHermitianCoefficients h → ContinuousStrictPsh h u → ClassicalStrictPsh u

/-- Unproved internal target, not a citation leaf: for a smooth function, the
classical local definition implies positivity of the project's computed Levi. -/
def SmoothClassicalLeviBridgeTarget : Prop :=
  ∀ (n : ℕ) (M : Yau.ComplexManifold n) (u : M.Carrier → ℝ),
    Yau.SmoothFn u → ClassicalStrictPsh u → ∀ x, (Yau.levi u x).PosDef

/-- The actual scalar heat equation; time zero is an initial trace, not a PDE
at zero. The operator is the computed complex Laplacian in Calculus.lean. -/
def PositiveHeatSolution (h : Yau.HermitianField M) (u : M.Carrier → ℝ → ℝ) : Prop :=
  Yau.SmoothSpaceTime u (Set.Ioi 0) ∧
    ∀ x t, 0 < t → 0 < u x t ∧
      deriv (u x) t = Yau.laplacian h (fun y => u y t) x

/-- A kernel must solve the PDE and have the delta initial trace. Stochastic
completeness and Gaussian/gradient estimates are deliberately not premises. -/
def ScalarHeatKernel (h : Yau.HermitianField M) (μ : Measure M.Carrier)
    (H : ℝ → M.Carrier → M.Carrier → ℝ) : Prop :=
  (∀ y, PositiveHeatSolution h (fun x t => H t x y)) ∧
  (∀ t, 0 < t → ∀ x y, H t x y = H t y x) ∧
  (∀ f : M.Carrier → ℝ, Continuous f → HasCompactSupport f → ∀ y,
    Tendsto (fun t => ∫ x, H t x y * f x ∂μ) (𝓝[>] 0) (𝓝 (f y)))

/-- L12: relative volume comparison, the common input at preliminaries:154,230.
The scalar nonnegative Ricci hypothesis is explicit; its geometric bridge is G4. -/
def BishopGromov : Prop :=
  ∀ (n : ℕ) (M : Yau.ComplexManifold n) (g : Yau.SmoothMetric M),
    Yau.IsComplete g → Yau.IsKahler g →
    (∀ x, (Yau.ricci g.form x).PosSemidef) →
    ∀ μ, Yau.IsRiemannianVolume g.form μ →
    ∀ x r R, 0 < r → r ≤ R →
      μ (Yau.distBall g.form x R) ≤
        ENNReal.ofReal ((R / r) ^ (2 * n)) * μ (Yau.distBall g.form x r)

/-- L18: exactly the p=1 nonnegative subharmonic mean-value input used for
canonical section norms; no canonical-section growth conclusion is assumed. -/
def LiSchoenMeanValue : Prop :=
  ∀ n : ℕ, 0 < n → ∃ C : ℝ, 0 < C ∧
    ∀ (M : Yau.ComplexManifold n) (g : Yau.SmoothMetric M),
      Yau.IsComplete g → Yau.IsKahler g →
      (∀ x, (Yau.ricci g.form x).PosSemidef) →
      ∀ μ, Yau.IsRiemannianVolume g.form μ →
      ∀ u : M.Carrier → ℝ, Yau.SmoothFn u →
        (∀ x, 0 ≤ u x ∧ 0 ≤ Yau.laplacian g.form u x) →
        ∀ x r, 0 < r →
          ENNReal.ofReal (u x) * μ (Yau.distBall g.form x r) ≤
            ENNReal.ofReal C * ∫⁻ y in Yau.distBall g.form x r, ENNReal.ofReal (u y) ∂μ

/-- L19 differential input, with the complex-Laplacian normalization. Its
coefficient n must be checked against the real gradient/heat conventions before
source approval. This target also supplies the two positive-translate argument. -/
def LiYauDifferential : Prop :=
  ∀ (n : ℕ) (M : Yau.ComplexManifold n) (g : Yau.SmoothMetric M),
    Yau.IsComplete g → Yau.IsKahler g →
    (∀ x, (Yau.ricci g.form x).PosSemidef) →
    ∀ u : M.Carrier → ℝ → ℝ, PositiveHeatSolution g.form u → ∀ x t, 0 < t →
      Yau.gradNormSq g.form (fun y => Real.log (u y t)) x -
        deriv (fun s => Real.log (u x s)) t ≤ (n : ℝ) / t

/-- L19 Gaussian input, kept separate from the differential estimate. The
symmetric volume denominator is what F03 consumes. -/
def LiYauGaussian : Prop :=
  ∀ n : ℕ, 0 < n → ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    ∀ (M : Yau.ComplexManifold n) (g : Yau.SmoothMetric M),
      Yau.IsComplete g → Yau.IsKahler g →
      (∀ x, (Yau.ricci g.form x).PosSemidef) →
      ∀ μ, Yau.IsRiemannianVolume g.form μ →
      ∀ H, ScalarHeatKernel g.form μ H → ∀ t, 0 < t → ∀ x y,
        H t x y ≤ C * Real.exp (-c * Yau.distFrom g.form x y ^ 2 / t) /
          Real.sqrt ((μ (Yau.distBall g.form x (Real.sqrt t))).toReal *
            (μ (Yau.distBall g.form y (Real.sqrt t))).toReal)

/-- L24: the kernel-gradient consequence actually used; not the entire local
Souplet--Zhang theorem. The Gaussian derivation remains internal. -/
def HeatKernelGradient : Prop :=
  ∀ n : ℕ, 0 < n → ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    ∀ (M : Yau.ComplexManifold n) (g : Yau.SmoothMetric M),
      Yau.IsComplete g → Yau.IsKahler g →
      (∀ x, (Yau.ricci g.form x).PosSemidef) →
      ∀ μ, Yau.IsRiemannianVolume g.form μ →
      ∀ H, ScalarHeatKernel g.form μ H → ∀ t, 0 < t → ∀ x y,
        Real.sqrt (Yau.gradNormSq g.form (fun z => H t z y) x) ≤
          C / Real.sqrt t * Real.exp (-c * Yau.distFrom g.form x y ^ 2 / t) /
            Real.sqrt ((μ (Yau.distBall g.form x (Real.sqrt t))).toReal *
              (μ (Yau.distBall g.form y (Real.sqrt t))).toReal)

/-- Pullback coefficient of a Hermitian background under a holomorphic local
parametrization. The differential is computed, never supplied as a free frame. -/
def pullbackCoefficient (g : Yau.HermitianField M)
    (e : Yau.ComplexVector n → M.Carrier) (z : Yau.ComplexVector n) (i j : Fin n) : ℂ :=
  (g (e z)).toFun
    (mfderiv (Yau.ComplexModel n) (Yau.ComplexModel n) e z (Yau.stdVec i))
    (mfderiv (Yau.ComplexModel n) (Yau.ComplexModel n) e z (Yau.stdVec j))

/-- A concrete all-orders bounded-geometry hypothesis in holomorphic charts.
The radii and coefficient bounds are chosen before the center point. It is a
strong smooth specialization; equivalence to Lee--Tam Definition 2.1 is pending. -/
def HermitianBoundedGeometry (g : Yau.HermitianField M) : Prop :=
  ∃ r : ℝ, 0 < r ∧ ∃ C : ℕ → ℝ, (∀ k, 0 < C k) ∧
    ∀ p : M.Carrier,
      ∃ e : OpenPartialHomeomorph (Yau.ComplexVector n) M.Carrier,
        e 0 = p ∧ Metric.closedBall 0 r ⊆ e.source ∧
        MDifferentiableOn (Yau.ComplexModel n) (Yau.ComplexModel n) e e.source ∧
        MDifferentiableOn (Yau.ComplexModel n) (Yau.ComplexModel n) e.symm e.target ∧
        (∀ z ∈ Metric.ball (0 : Yau.ComplexVector n) r,
          ((Matrix.of (fun i j => pullbackCoefficient g e z i j)) -
            ((C 0)⁻¹ : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).PosSemidef ∧
          ((C 0 : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) -
            (Matrix.of (fun i j => pullbackCoefficient g e z i j))).PosSemidef) ∧
        (∀ i j, ContDiffOn ℝ ∞ (fun z => pullbackCoefficient g e z i j) (Metric.ball 0 r)) ∧
        ∀ k z, z ∈ Metric.ball 0 r → ∀ i j,
          ‖iteratedFDeriv ℝ k (fun w => pullbackCoefficient g e w i j) z‖ ≤ C k

/-- L17: complete Hermitian short-time potential flow, not a Kähler-only
replacement for the conformal approximating backgrounds in flow:74.
Continuation at flow:252 stays internal and also requires L05/L16. -/
def HermitianShortTimeFlow : Prop :=
  ∀ (n : ℕ) (M : Yau.ComplexManifold n) (g : Yau.HermitianField M),
    Yau.MetricSmooth g → Yau.IsCompleteDistance (Yau.inducedDistance g) →
    HermitianBoundedGeometry g →
    ∃ T C : ℝ, 0 < T ∧ 1 ≤ C ∧
      ∃ (h : ℝ → Yau.HermitianField M) (U : M.Carrier → ℝ → ℝ),
        h 0 = g ∧ Yau.MetricFamilySmooth h (Set.Icc 0 T) ∧
        Yau.SmoothSpaceTime U (Set.Icc 0 T) ∧ (∀ x, U x 0 = 0) ∧
        ∀ x t, t ∈ Set.Icc 0 T →
          (Yau.gMat (h t) x - ((C⁻¹ : ℝ) : ℂ) • Yau.gMat g x).PosSemidef ∧
          ((C : ℂ) • Yau.gMat g x - Yau.gMat (h t) x).PosSemidef ∧
          Yau.gMat (h t) x = Yau.gMat g x - (t : ℂ) • Yau.ricci g x +
            Yau.levi (fun y => U y t) x ∧
          HasDerivWithinAt (U x)
            (Real.log ((Yau.gMat (h t) x).det.re / (Yau.gMat g x).det.re))
            (Set.Icc 0 T) t

/-- Lie bracket of smooth Euclidean real vector fields, used to compute N_J. -/
def bracket (V W : Yau.ComplexVector n → Yau.ComplexVector n)
    (x : Yau.ComplexVector n) : Yau.ComplexVector n :=
  fderiv ℝ W x (V x) - fderiv ℝ V x (W x)

def nijenhuis (J : Yau.ComplexVector n → Yau.ComplexVector n →L[ℝ] Yau.ComplexVector n)
    (x v w : Yau.ComplexVector n) : Yau.ComplexVector n :=
  bracket (fun y => J y v) (fun y => J y w) x -
    J x (bracket (fun y => J y v) (fun _ => w) x) -
    J x (bracket (fun _ => v) (fun y => J y w) x)

/-- L13/L21: the common smooth Newlander--Nirenberg input on a real coordinate
ball. The chart intertwines J with multiplication by i, and has a smooth inverse. -/
def SmoothNewlanderNirenberg : Prop :=
  ∀ (n : ℕ) (O : Set (Yau.ComplexVector n))
    (J : Yau.ComplexVector n → Yau.ComplexVector n →L[ℝ] Yau.ComplexVector n),
    IsOpen O → ContDiffOn ℝ ∞ J O →
    (∀ x ∈ O, ∀ v, J x (J x v) = -v) →
    (∀ x ∈ O, ∀ v w, nijenhuis J x v w = 0) →
    ∀ p ∈ O, ∃ e : OpenPartialHomeomorph (Yau.ComplexVector n) (Yau.ComplexVector n),
      p ∈ e.source ∧ e.source ⊆ O ∧
      ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target ∧
      ∀ x ∈ e.source, ∀ v,
        fderiv ℝ e x (J x v) = Complex.I • fderiv ℝ e x v

/-- Matrix operator norm in the standard Hermitian Euclidean space. -/
def matrixOpNorm {r : ℕ} (A : Matrix (Fin r) (Fin r) ℂ) : ℝ :=
  ‖(Matrix.toEuclideanLin A).toContinuousLinearMap‖

/-- L02/L27 common factorization input. The quantitative half-Sobolev estimates
are proved in the paper and remain D05/V04 internal obligations. -/
def SmoothBoundaryFactorization : Prop :=
  ∀ (r : ℕ) (L : ℂ → Matrix (Fin r) (Fin r) ℂ) (m M : ℝ),
    ContDiffOn ℝ ∞ L (Metric.sphere 0 1) → 0 < m → m ≤ M →
    (∀ z ∈ Metric.sphere (0 : ℂ) 1,
      (L z - (m : ℂ) • (1 : Matrix (Fin r) (Fin r) ℂ)).PosSemidef ∧
      ((M : ℂ) • (1 : Matrix (Fin r) (Fin r) ℂ) - L z).PosSemidef) →
    ∃ H Hinv : ℂ → Matrix (Fin r) (Fin r) ℂ,
      ContDiffOn ℝ ∞ H (Metric.closedBall 0 1) ∧
      ContDiffOn ℝ ∞ Hinv (Metric.closedBall 0 1) ∧
      DifferentiableOn ℂ H (Metric.ball 0 1) ∧
      DifferentiableOn ℂ Hinv (Metric.ball 0 1) ∧
      (∀ z ∈ Metric.closedBall (0 : ℂ) 1, H z * Hinv z = 1 ∧ Hinv z * H z = 1 ∧
        matrixOpNorm (H z) ≤ Real.sqrt M ∧ matrixOpNorm (Hinv z) ≤ 1 / Real.sqrt m) ∧
      (∀ z ∈ Metric.sphere (0 : ℂ) 1, L z = (H z).conjTranspose * H z)

/-- Distributional gradient on a planar domain, using compactly supported
smooth real tests. Both v and the gradient are actual integrable functions. -/
def WeakPlanarGradient (O : Set ℂ) (v : ℂ → ℝ) (g : ℂ → RV 2) : Prop :=
  IntegrableOn v O volume ∧ IntegrableOn g O volume ∧
    ∀ φ : ℂ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ O →
      ∀ i : Fin 2,
        (∫ z in O, v z * fderiv ℝ φ z (if i = 0 then 1 else Complex.I)) =
          -(∫ z in O, g z i * φ z)

/-- L09 Morrey input exactly in the dimension and exponent consumed by D04.
Continuity chooses the representative; the constant never depends on v's
values or on the target point p used for a distance function. -/
def PlanarMorrey : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (z₀ : ℂ) (r : ℝ), 0 < r →
    ∀ (v : ℂ → ℝ) (g : ℂ → RV 2),
      ContinuousOn v (Metric.ball z₀ (2 * r)) →
      WeakPlanarGradient (Metric.ball z₀ (2 * r)) v g →
      MemLp g 3 (volume.restrict (Metric.ball z₀ (2 * r))) →
      ∀ z ∈ Metric.ball z₀ r, ∀ w ∈ Metric.ball z₀ r,
        |v z - v w| ≤ C * (eLpNorm g 3 (volume.restrict (Metric.ball z₀ (2 * r)))).toReal *
          ‖z - w‖ ^ (1 / 3 : ℝ)

/-- An explicit integer-order L² Sobolev norm on a Euclidean coordinate ball.
Integrability of every summand is a separate premise in the estimate below. -/
def sobolevNormSq (O : Set (Yau.ComplexVector n)) (u : Yau.ComplexVector n → ℂ)
    (s : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (s + 1), ∫ z in O, ‖iteratedFDeriv ℝ j u z‖ ^ 2 ∂Yau.lebesgueC n

/-- L09 Sobolev embedding used at charts:273, in real dimension 2n.
This is the smooth-function version the already smooth corrections consume. -/
def InteriorSobolevEmbedding : Prop :=
  ∀ (n k s : ℕ), k + n < s → ∀ r R : ℝ, 0 < r → r < R →
    ∃ C : ℝ, 0 < C ∧ ∀ u : Yau.ComplexVector n → ℂ,
      ContDiffOn ℝ ∞ u (Metric.ball 0 R) →
      (∀ j ≤ s, IntegrableOn (fun z => ‖iteratedFDeriv ℝ j u z‖ ^ 2)
        (Metric.ball 0 R) (Yau.lebesgueC n)) →
      ∀ z ∈ Metric.ball (0 : Yau.ComplexVector n) r,
        ‖iteratedFDeriv ℝ k u z‖ ≤ C * Real.sqrt
          (sobolevNormSq (Metric.ball (0 : Yau.ComplexVector n) R) u s)

/-- Scalar second-order elliptic operator in fixed real coordinates. -/
def ellipticOp (a : Yau.ComplexVector n → Matrix (Yau.RIdx n) (Yau.RIdx n) ℝ)
    (b : Yau.ComplexVector n → Yau.RIdx n → ℝ)
    (u : Yau.ComplexVector n → ℂ) (z : Yau.ComplexVector n) : ℂ :=
  (∑ i, ∑ j, (a z i j : ℂ) *
    fderiv ℝ (fun w => fderiv ℝ u w (Yau.realVec j)) z (Yau.realVec i)) +
    ∑ i, (b z i : ℂ) * fderiv ℝ u z (Yau.realVec i)

/-- L10, GT 8.8/8.10: the smooth interior H^{s+2} estimate actually consumed
at charts:266. Quantifiers preserve the uniformity in the sequence index:
C depends on coefficient bounds, ellipticity and nested radii, not on u. -/
def InteriorEllipticEstimate : Prop :=
  ∀ (n s : ℕ) (r R ell A : ℝ), 0 < r → r < R → 0 < ell → 0 < A →
    ∃ C : ℝ, 0 < C ∧
      ∀ (a : Yau.ComplexVector n → Matrix (Yau.RIdx n) (Yau.RIdx n) ℝ)
        (b : Yau.ComplexVector n → Yau.RIdx n → ℝ),
        (∀ i j, ContDiffOn ℝ ∞ (fun z => a z i j) (Metric.ball 0 R)) →
        (∀ i, ContDiffOn ℝ ∞ (fun z => b z i) (Metric.ball 0 R)) →
        (∀ z ∈ Metric.ball 0 R, (a z).IsSymm ∧
          ∀ v : Yau.RIdx n → ℝ,
            ell * ∑ i, v i ^ 2 ≤ ∑ i, ∑ j, a z i j * v i * v j) →
        (∀ k ≤ s + 1, ∀ z ∈ Metric.ball 0 R, ∀ i j,
          ‖iteratedFDeriv ℝ k (fun w => a w i j) z‖ ≤ A ∧
          ‖iteratedFDeriv ℝ k (fun w => b w i) z‖ ≤ A) →
        ∀ u : Yau.ComplexVector n → ℂ, ContDiffOn ℝ ∞ u (Metric.ball 0 R) →
          (∀ k ≤ s + 2, IntegrableOn (fun z => ‖iteratedFDeriv ℝ k u z‖ ^ 2)
            (Metric.ball 0 R) (Yau.lebesgueC n)) →
          (∀ k ≤ s, IntegrableOn (fun z => ‖iteratedFDeriv ℝ k (ellipticOp a b u) z‖ ^ 2)
            (Metric.ball 0 R) (Yau.lebesgueC n)) →
          Real.sqrt (sobolevNormSq (Metric.ball 0 r) u (s + 2)) ≤ C *
            (Real.sqrt (sobolevNormSq (Metric.ball 0 R) u 0) +
              Real.sqrt (sobolevNormSq (Metric.ball 0 R) (ellipticOp a b u) s))

/-- Real planar Laplacian, with complex-valued output; Δ=4∂ζ∂barζ. -/
def planarLaplacian (u : ℂ → ℂ) (z : ℂ) : ℂ :=
  fderiv ℝ (fun w => fderiv ℝ u w 1) z 1 +
    fderiv ℝ (fun w => fderiv ℝ u w Complex.I) z Complex.I

/-- L10, GT 9.15/9.17/8.13: the zero-Dirichlet inverse on the unit disc.
Only smooth input on the closed disc is required by the paper's b_ik.
No arbitrary inverse operator is accepted as input. -/
def DiscDirichletEstimate : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ f : ℂ → ℂ,
    ContDiffOn ℝ ∞ f (Metric.closedBall 0 1) →
    ∃ u : ℂ → ℂ, ContDiffOn ℝ ∞ u (Metric.closedBall 0 1) ∧
      (∀ z ∈ Metric.sphere (0 : ℂ) 1, u z = 0) ∧
      (∀ z ∈ Metric.ball (0 : ℂ) 1, planarLaplacian u z = f z) ∧
      Real.sqrt (∑ k ∈ Finset.range 3, ∫ z in Metric.ball (0 : ℂ) 1,
        ‖iteratedFDeriv ℝ k u z‖ ^ 2) ≤ C *
          Real.sqrt (∫ z in Metric.ball (0 : ℂ) 1, ‖f z‖ ^ 2)

/-- Subharmonicity on an actual planar open set, allowing logarithmic poles.
Submeans use continuous majorants, so no undefined integral of -∞ is introduced. -/
def DiscSubharmonic (O : Set ℂ) (u : ℂ → EReal) : Prop :=
  (∀ z ∈ O, u z < ⊤) ∧ UpperSemicontinuousOn u O ∧
    ∀ z : ℂ, ∀ r : ℝ, 0 < r → Metric.closedBall z r ⊆ O →
      ∀ φ : ℝ → ℝ, Continuous φ →
        (∀ θ : ℝ, u (z + r * Complex.exp (θ * Complex.I)) ≤ (φ θ : EReal)) →
        u z ≤ (Yau.circleAverage φ : EReal)

/-- Local L¹ includes finiteness almost everywhere; EReal.toReal alone would
silently turn both infinities into zero. -/
def LocallyL1 (O : Set ℂ) (u : ℂ → EReal) : Prop :=
  ∀ K : Set ℂ, IsCompact K → K ⊆ O →
    (∀ᵐ z ∂(volume.restrict K), u z ≠ ⊥ ∧ u z ≠ ⊤) ∧
      IntegrableOn (fun z => (u z).toReal) K volume

/-- The local L¹ conclusion has concrete functions, measure and subsequence. -/
def LocallyL1Converges (O : Set ℂ) (u : ℕ → ℂ → EReal) (v : ℂ → EReal) : Prop :=
  LocallyL1 O v ∧ ∀ K : Set ℂ, IsCompact K → K ⊆ O →
    Tendsto (fun j => ∫ z in K, |(u j z).toReal - (v z).toReal|) atTop (𝓝 0)

/-- L08, Demailly I.4.21: the L¹-bounded subharmonic compactness input.
Moving lower anchors and exhausting domains remain the paper's D04 argument. -/
def SubharmonicL1Compactness : Prop :=
  ∀ (O : Set ℂ) (u : ℕ → ℂ → EReal), IsOpen O →
    (∀ j, DiscSubharmonic O (u j) ∧ LocallyL1 O (u j)) →
    (∀ K : Set ℂ, IsCompact K → K ⊆ O → ∃ C : ℝ, ∀ j,
      ∫ z in K, |(u j z).toReal| ≤ C) →
    ∃ (σ : ℕ → ℕ) (v : ℂ → EReal), StrictMono σ ∧
      DiscSubharmonic O v ∧ LocallyL1Converges O (fun j => u (σ j)) v

/-- The Hartogs upper bound used when the L¹ limit is constant. -/
def SubharmonicHartogs : Prop :=
  ∀ (O : Set ℂ) (u : ℕ → ℂ → EReal) (c : ℝ), IsOpen O →
    (∀ j, DiscSubharmonic O (u j) ∧ LocallyL1 O (u j)) →
    LocallyL1Converges O u (fun _ => (c : EReal)) →
    ∀ K : Set ℂ, IsCompact K → K ⊆ O → ∀ ε : ℝ, 0 < ε →
      ∀ᶠ j in atTop, ∀ z ∈ K, u j z ≤ ((c + ε : ℝ) : EReal)

/-- Ordinary real planar Laplacian, matching Δ_eucl in discs.tex:348. -/
def realPlanarLaplacian (u : ℂ → ℝ) (z : ℂ) : ℝ :=
  (planarLaplacian (fun w => (u w : ℂ)) z).re

/-- The Riesz measure of a smooth subharmonic function on a disc; no logarithmic
singularity is evaluated as a point mass in the potential below. -/
def smoothRieszMeasure (u : ℂ → ℝ) (z₀ : ℂ) (R : ℝ) : Measure ℂ :=
  ((volume : Measure ℂ).withDensity
    (fun z => ENNReal.ofReal (realPlanarLaplacian u z / (2 * Real.pi)))).restrict
      (Metric.ball z₀ R)

/-- Exactly the smooth-sequence use of DemaillyBook I.4.22 in discs:355–367.
The ψ_l in that application are smooth. This does not claim a representation
of the limiting EReal-valued potential at its atoms using Real.log 0. -/
def SmoothPlanarRieszDecomposition : Prop :=
  ∀ (u : ℂ → ℝ) (z₀ : ℂ) (R : ℝ), 0 < R →
    (∃ O : Set ℂ, IsOpen O ∧ Metric.closedBall z₀ R ⊆ O ∧
      ContDiffOn ℝ ∞ u O ∧ ∀ z ∈ O, 0 ≤ realPlanarLaplacian u z) →
    let μ := smoothRieszMeasure u z₀ R
    μ Set.univ < ⊤ ∧ (∀ z : ℂ, μ {z} = 0) ∧
    ∃ h : ℂ → ℝ, ContDiffOn ℝ ∞ h (Metric.ball z₀ R) ∧
      (∀ z ∈ Metric.ball z₀ R, realPlanarLaplacian h z = 0) ∧
      ∀ z ∈ Metric.ball z₀ R,
        Integrable (fun w => Real.log ‖z - w‖) μ ∧
        u z = h z + ∫ w, Real.log ‖z - w‖ ∂μ

/-- Local-finiteness of the possible bad atoms, a measure-theory obligation
separate from the paper's inverse-Jacobian/Jensen argument. -/
def LocallyFiniteLargeAtoms : Prop :=
  ∀ (O : Set ℂ) (μ : Measure ℂ), IsOpen O →
    (∀ K : Set ℂ, IsCompact K → K ⊆ O → μ K < ⊤) →
    ∀ K : Set ℂ, IsCompact K → K ⊆ O → Set.Finite {z | z ∈ K ∧ (1 : ENNReal) ≤ μ {z}}

/-- L25 is Mathlib reuse. No external approval is requested. Its analytic local
ring and finite quotient-module instantiation remains a separate D03 obligation. -/
def KrullIntersection (R M : Type*) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] : Prop :=
  ∀ I : Ideal R, I ≠ ⊤ → (⨅ k : ℕ, I ^ k • ⊤ : Submodule R M) = ⊥

end Yau.LeafCandidates
