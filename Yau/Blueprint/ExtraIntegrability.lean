import Yau.Blueprint.BundlePresentation

/-! The full D03 target is `BundleExtraIntegrability`, for arbitrary intrinsic
Hermitian holomorphic bundles as in discs.tex:159–170. The earlier
`EmbeddedExtraIntegrability` is only an auxiliary theorem target. The actual
A-to-image constructions are in BundlePresentation; the transport obligations
below are explicit unproved targets. None is an extra hypothesis of D03. -/
open scoped Manifold Topology ContDiff Matrix ComplexOrder
open MeasureTheory
noncomputable section
namespace Yau.Blueprint
open Yau

abbrev EmbeddedFibers (q : ℕ) := ℂ → Submodule ℂ (ComplexVector q)
abbrev EmbeddedMetric {q : ℕ} (E : EmbeddedFibers q) :=
  (z : ℂ) → HermitianInnerProduct (E z)

def frameLinear {q r : ℕ} (B : Matrix (Fin q) (Fin r) ℂ) :
    ComplexVector r →ₗ[ℂ] ComplexVector q :=
  Matrix.toEuclideanLin B

def LocalEmbeddedFrame {q r : ℕ} (E : EmbeddedFibers q)
    (F : ℂ → Matrix (Fin q) (Fin r) ℂ) (U : Set ℂ) : Prop :=
  IsOpen U ∧ U ⊆ puncturedUnitDisc ∧ DifferentiableOn ℂ F U ∧
    ∀ z ∈ U, LinearMap.range (frameLinear (F z)) = E z ∧
      Function.Injective (frameLinear (F z))

def HolomorphicEmbeddedBundle {q : ℕ} (E : EmbeddedFibers q) (r : ℕ) : Prop :=
  ∀ z ∈ puncturedUnitDisc, ∃ U : Set ℂ, z ∈ U ∧
    ∃ F : ℂ → Matrix (Fin q) (Fin r) ℂ, LocalEmbeddedFrame E F U

/-- Values outside a valid local frame are irrelevant. Membership is explicitly
required by LocalEmbeddedFrame, so no zero fallback is used on its domain. -/
def frameLift {q r : ℕ} (E : EmbeddedFibers q)
    (F : ℂ → Matrix (Fin q) (Fin r) ℂ) (z : ℂ) (i : Fin r) : E z := by
  classical
  exact if hz : frameLinear (F z) (stdVec i) ∈ E z then
    ⟨frameLinear (F z) (stdVec i), hz⟩ else 0

def embeddedGram {q r : ℕ} (E : EmbeddedFibers q) (k : EmbeddedMetric E)
    (F : ℂ → Matrix (Fin q) (Fin r) ℂ) (z : ℂ) : Matrix (Fin r) (Fin r) ℂ :=
  fun a b => (k z).toFun (frameLift E F z a) (frameLift E F z b)

/-- The lowered Chern curvature -∂bar∂H + (∂bar H)H⁻¹(∂H) on a complex curve. -/
def embeddedChernCurvature {q r : ℕ} (E : EmbeddedFibers q) (k : EmbeddedMetric E)
    (F : ℂ → Matrix (Fin q) (Fin r) ℂ) (z : ℂ) : Matrix (Fin r) (Fin r) ℂ :=
  fun a b =>
    -wirtBar (fun w => wirt (fun u => embeddedGram E k F u a b) w 1) z 1 +
      ∑ p, ∑ l,
        wirtBar (fun w => embeddedGram E k F w a p) z 1 *
          (embeddedGram E k F z)⁻¹ p l *
          wirt (fun w => embeddedGram E k F w l b) z 1

def EmbeddedSmoothGriffithsNonnegative {q : ℕ} (E : EmbeddedFibers q)
    (k : EmbeddedMetric E) (r : ℕ) : Prop :=
  ∀ (U : Set ℂ) (F : ℂ → Matrix (Fin q) (Fin r) ℂ), LocalEmbeddedFrame E F U →
    (∀ a b, ContDiffOn ℝ ∞ (fun z => embeddedGram E k F z a b) U) ∧
      ∀ z ∈ U, (embeddedChernCurvature E k F z).PosSemidef

def embeddedNormSq {q : ℕ} (E : EmbeddedFibers q) (k : EmbeddedMetric E)
    (a : ℂ → ComplexVector q) (z : ℂ) : ℝ := by
  classical
  exact if hz : a z ∈ E z then hermitianNormSq (k z) ⟨a z, hz⟩ else 0

/-- Exact extra-integrability conclusion in the image-bundle presentation.
All integral measures are ordinary area dA on the punctured complex disc. -/
def EmbeddedExtraIntegrability : Prop :=
  ∀ (q r : ℕ) (E : EmbeddedFibers q) (k : EmbeddedMetric E),
    HolomorphicEmbeddedBundle E r → EmbeddedSmoothGriffithsNonnegative E k r →
    (∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ puncturedUnitDisc, ∀ u : E z,
      ‖u.1‖ ^ 2 ≤ C * hermitianNormSq (k z) u) →
    ∀ a : ℂ → ComplexVector q, DifferentiableOn ℂ a puncturedUnitDisc →
      (∀ z ∈ puncturedUnitDisc, a z ∈ E z) →
      (∫⁻ z in puncturedUnitDisc, ENNReal.ofReal (embeddedNormSq E k a z)
        ∂(volume : Measure ℂ)) < ⊤ →
      ∃ r₀ σ : ℝ, 0 < r₀ ∧ r₀ < 1 ∧ 0 < σ ∧
        (∫⁻ z in {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ < r₀},
          ENNReal.ofReal (embeddedNormSq E k a z * ‖z‖ ^ (-σ))
            ∂(volume : Measure ℂ)) < ⊤

/-- Full paper lemma, with every input quantified in the original bundle API.
The global coordinate concerns the base Δ* only. The normed-space instances
support Mathlib's bundle API; boundedness and L² use the supplied metric k.
No frame, tensor realization, image-transport theorem, completeness of k, or
extension across zero occurs among the hypotheses. r₀ and σ depend on s and
all preceding bundle data; no uniform exponent is asserted.

The base-coordinate construction is separately scheduled as
`BundlePresentation.StandardDiscRealization`; it is not assumed proved here.
This definition, rather than EmbeddedExtraIntegrability, must be attached to
the D03 contract. -/
def BundleExtraIntegrability : Prop :=
  ∀ (M : ComplexManifold 1) (c : BundlePresentation.DiscCoordinate M),
    BundlePresentation.IsDiscCoordinate c →
    ∀ (r q : ℕ) (E : M.Carrier → Type)
      [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
      [∀ x, NormedSpace ℝ (E x)] [∀ x, IsScalarTower ℝ ℂ (E x)]
      [TopologicalSpace (Bundle.TotalSpace (ComplexVector r) E)]
      [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]
      (k : BundleDbar.Metric E) (A : BundlePresentation.MapToTrivial E q),
      BundleDbar.Holomorphic (r := r) E → BundleDbar.SmoothMetric (r := r) E k →
      BundleDbar.GriffithsNonnegative (r := r) E k →
      BundlePresentation.HolomorphicMap (r := r) E A →
      BundlePresentation.PointwiseInjective E A → BundlePresentation.BoundedMap E k A →
      ∀ s : BundlePresentation.Section E,
        BundlePresentation.HolomorphicSection (r := r) E s →
        BundlePresentation.sectionIntegral E c k s < ⊤ →
        ∃ r₀ σ : ℝ, 0 < r₀ ∧ r₀ < 1 ∧ 0 < σ ∧
          BundlePresentation.weightedSectionIntegral E c k s r₀ σ < ⊤

namespace BundlePresentation

variable {M : ComplexManifold 1} {r q : ℕ}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (Bundle.TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

/-- Local holomorphic image frames are the actual images of the original
atlas frames. Their domains cover Δ*. No global frame is requested. -/
def ImageLocalFrameTransport : Prop :=
  ∀ (c : DiscCoordinate M), IsDiscCoordinate c →
    ∀ (A : MapToTrivial E q), BundleDbar.Holomorphic (r := r) E →
      HolomorphicMap (r := r) E A → PointwiseInjective E A →
      (∀ a, LocalEmbeddedFrame (imageFibers E c A)
        (imageFrame (r := r) E c A a) (imageFrameDomain (r := r) E c a)) ∧
      HolomorphicEmbeddedBundle (imageFibers E c A) r

/-- The metric is fixed by A^{-1}, both intrinsically and in each actual
local image frame. These equations exclude replacing it by ambient Euclidean
metric or by a freely supplied positive matrix. -/
def ImageMetricTransport : Prop :=
  ∀ (c : DiscCoordinate M), IsDiscCoordinate c →
    ∀ (k : BundleDbar.Metric E) (A : MapToTrivial E q) (hA : PointwiseInjective E A),
      (∀ z (u v : E (c.symm z)),
        (imageMetric E c k A hA z).toFun
          (imageEquiv E c A hA z u) (imageEquiv E c A hA z v) =
            (k (c.symm z)).toFun u v) ∧
      ∀ a z, z ∈ imageFrameDomain (r := r) E c a →
        embeddedGram (imageFibers E c A) (imageMetric E c k A hA)
          (imageFrame (r := r) E c A a) z =
            BundleDbar.metricMatrix (r := r) E k a (baseChange c a z)

/-- The computed lowered Chern curvature transforms by |dw/dz|² under
the base-coordinate change w = chart_a(c^{-1}(z)). It is not arbitrary
curvature data. This includes the expansion of -H dbar(H^{-1} dH) used by
the embedded calculator. -/
def ImageCurvatureTransport : Prop :=
  ∀ (c : DiscCoordinate M), IsDiscCoordinate c →
    ∀ (k : BundleDbar.Metric E) (A : MapToTrivial E q) (hA : PointwiseInjective E A),
      BundleDbar.Holomorphic (r := r) E → BundleDbar.SmoothMetric (r := r) E k →
      HolomorphicMap (r := r) E A →
      ∀ a z, z ∈ imageFrameDomain (r := r) E c a →
        embeddedChernCurvature (imageFibers E c A) (imageMetric E c k A hA)
          (imageFrame (r := r) E c A a) z =
            (Complex.normSq (deriv (fun w => baseChange c a w 0) z) : ℂ) •
              BundleDbar.curvature (r := r) E k a (baseChange c a z) 0 0

/-- Positivity and smoothness in every valid local embedded frame require
the genuine holomorphic frame-change/tensoriality argument. This target is
stronger than checking only the images of one chosen atlas. -/
def ImagePositivityTransport : Prop :=
  ∀ (c : DiscCoordinate M), IsDiscCoordinate c →
    ∀ (k : BundleDbar.Metric E) (A : MapToTrivial E q) (hA : PointwiseInjective E A),
      BundleDbar.Holomorphic (r := r) E → BundleDbar.SmoothMetric (r := r) E k →
      BundleDbar.GriffithsNonnegative (r := r) E k → HolomorphicMap (r := r) E A →
      EmbeddedSmoothGriffithsNonnegative (imageFibers E c A) (imageMetric E c k A hA) r

def ImageSectionTransport : Prop :=
  ∀ (c : DiscCoordinate M), IsDiscCoordinate c →
    ∀ (A : MapToTrivial E q), BundleDbar.Holomorphic (r := r) E →
      HolomorphicMap (r := r) E A → ∀ s : Section E,
      HolomorphicSection (r := r) E s →
        DifferentiableOn ℂ (imageSection E c A s) puncturedUnitDisc ∧
          ∀ z ∈ puncturedUnitDisc, imageSection E c A s z ∈ imageFibers E c A z

/-- Transport preserves the same numerical bound C. -/
def ImageBoundTransport : Prop :=
  ∀ (c : DiscCoordinate M) (k : BundleDbar.Metric E)
    (A : MapToTrivial E q) (hA : PointwiseInjective E A) (C : ℝ),
    (∀ x v, ‖A x v‖ ^ 2 ≤ C * hermitianNormSq (k x) v) →
    ∀ z ∈ puncturedUnitDisc, ∀ u : imageFibers E c A z,
      ‖u.1‖ ^ 2 ≤ C * hermitianNormSq (imageMetric E c k A hA z) u

/-- Both exact integrals are transported, including the radial weight and
the shrinking domain. Thus an image-bundle conclusion yields the original
section conclusion with the same radius and exponent. -/
def ImageIntegralTransport : Prop :=
  ∀ (c : DiscCoordinate M), IsDiscCoordinate c →
    ∀ (k : BundleDbar.Metric E) (A : MapToTrivial E q) (hA : PointwiseInjective E A),
      BundleDbar.Holomorphic (r := r) E → BundleDbar.SmoothMetric (r := r) E k →
      HolomorphicMap (r := r) E A → ∀ s : Section E,
      HolomorphicSection (r := r) E s →
        (sectionIntegral E c k s =
          ∫⁻ z in puncturedUnitDisc, ENNReal.ofReal
            (embeddedNormSq (imageFibers E c A) (imageMetric E c k A hA)
              (imageSection E c A s) z) ∂(volume : Measure ℂ)) ∧
        ∀ ρ σ : ℝ, 0 < ρ → ρ < 1 →
          weightedSectionIntegral E c k s ρ σ =
            ∫⁻ z in {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ < ρ}, ENNReal.ofReal
              (embeddedNormSq (imageFibers E c A) (imageMetric E c k A hA)
                (imageSection E c A s) z * ‖z‖ ^ (-σ)) ∂(volume : Measure ℂ)

end BundlePresentation

/-- Final reduction target after proving the concrete transport obligations.
This implication is not supplied as an axiom, nor substituted for the full
D03 endpoint. The standard base realization and tensor/Hörmander bridges are
separate infrastructure targets. -/
def BundleToEmbeddedReduction : Prop :=
  EmbeddedExtraIntegrability → BundleExtraIntegrability

end Yau.Blueprint
