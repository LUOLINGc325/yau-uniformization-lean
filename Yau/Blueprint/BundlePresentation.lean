import Yau.Geometry.HolomorphicBundle

/-! Intrinsic input for discs.tex:159–170. A coordinate trivializes the base
disc only; E is an arbitrary Mathlib vector bundle with its own local atlas.
The coordinate realization and all analytic/tensor transport declarations are
unproved targets, not hypotheses silently attached to D03. In particular no
global frame of E and no extension of its metric across zero are supplied. -/
open scoped Manifold Topology ContDiff Matrix ComplexOrder ENNReal
open MeasureTheory Bundle
noncomputable section

namespace Yau.Blueprint
open Yau

def puncturedUnitDisc : Set ℂ := {z | 0 < ‖z‖ ∧ ‖z‖ < 1}

namespace BundlePresentation

/-- A global coordinate on the base, with its actual inverse. It is not a
frame of the coefficient bundle. The values of the inverse off its target
are unused by the area measure and by every regularity condition. -/
abbrev DiscCoordinate (M : ComplexManifold 1) := OpenPartialHomeomorph M.Carrier ℂ

def IsDiscCoordinate {M : ComplexManifold 1} (c : DiscCoordinate M) : Prop :=
  c.source = Set.univ ∧ c.target = puncturedUnitDisc ∧
    ContMDiff (ComplexModel 1) 𝓘(ℂ, ℂ) ⊤ c ∧
    ContMDiffOn 𝓘(ℂ, ℂ) (ComplexModel 1) ⊤ c.symm puncturedUnitDisc

/-- The standard punctured disc must be realized in the `ComplexVector 1`
manifold API. This existence target is a separate infrastructure obligation;
it is neither an input to BundleExtraIntegrability nor an established result.
The displayed source, target and two holomorphicity conditions fix the entire
base geometry, rather than merely postulating a manifold called a disc. -/
def StandardDiscRealization : Prop :=
  ∃ (M : ComplexManifold 1) (c : DiscCoordinate M), IsDiscCoordinate c

/-- The complete cusp metric, normalized so that its real metric is
|dz|² / (|z|² log²|z|) under G = 2 Re h. -/
def completeDiscDensity (z : ℂ) : ℝ :=
  (2 * ‖z‖ ^ 2 * (Real.log ‖z‖) ^ 2)⁻¹

/-- Construct the auxiliary complete Kähler metric needed to invoke L14.
Its form is fixed by the displayed pullback formula; completeness and the
actual chart-volume law must be proved, not added as D03 assumptions. -/
def CompleteDiscMetricRealization : Prop :=
  ∀ (M : ComplexManifold 1) (c : DiscCoordinate M), IsDiscCoordinate c →
    ∃ (g : Yau.SmoothMetric M) (μ : Measure M.Carrier),
      IsRiemannianVolume g.form μ ∧ ∀ x (u v : TangentVector M x),
        (g.form x).toFun u v = (completeDiscDensity (c x) : ℂ) *
          star (show ℂ from mfderiv (ComplexModel 1) 𝓘(ℂ, ℂ) c x u) *
            (show ℂ from mfderiv (ComplexModel 1) 𝓘(ℂ, ℂ) c x v)

/-- Ordinary Euclidean dA, pulled to the base using the inverse coordinate.
No auxiliary complete metric or caller-chosen measure enters this definition. -/
def discArea {M : ComplexManifold 1} (c : DiscCoordinate M) : Measure M.Carrier :=
  Measure.map c.symm ((volume : Measure ℂ).restrict puncturedUnitDisc)

/-- In particular the computed measure cannot be replaced by zero. -/
def DiscAreaTransport : Prop :=
  ∀ (M : ComplexManifold 1) (c : DiscCoordinate M), IsDiscCoordinate c →
    Measure.map c (discArea c) = (volume : Measure ℂ).restrict puncturedUnitDisc ∧
      ∀ f : ℂ → ℝ≥0∞, Measurable f →
        (∫⁻ x, f (c x) ∂discArea c) = ∫⁻ z in puncturedUnitDisc, f z ∂volume

variable {M : ComplexManifold 1} {r q : ℕ}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

abbrev Section := ∀ x, E x
abbrev MapToTrivial (q : ℕ) := ∀ x, E x →L[ℂ] ComplexVector q

def sectionCoefficients (s : Section E) (a : M.Carrier) (z : ComplexVector 1) :
    ComplexVector r :=
  (BundleDbar.localTriv (r := r) E a).continuousLinearMapAt ℂ (chartInv a z)
    (s (chartInv a z))

def HolomorphicSection (s : Section E) : Prop :=
  ∀ a, DifferentiableOn ℂ (sectionCoefficients (r := r) E s a)
    (BundleDbar.localDomain (r := r) E a)

def mapCoefficients (A : MapToTrivial E q) (a : M.Carrier) (z : ComplexVector 1) :
    Matrix (Fin q) (Fin r) ℂ :=
  fun i j => A (chartInv a z)
    ((BundleDbar.localTriv (r := r) E a).symmL ℂ (chartInv a z) (stdVec j)) i

/-- Holomorphicity of the actual fibre map in the given bundle atlas. -/
def HolomorphicMap (A : MapToTrivial E q) : Prop :=
  ∀ a, DifferentiableOn ℂ (mapCoefficients (r := r) E A a)
    (BundleDbar.localDomain (r := r) E a)

def PointwiseInjective (A : MapToTrivial E q) : Prop :=
  ∀ x, Function.Injective (A x)

/-- The operator bound uses the specified Hermitian metric on E, not the
auxiliary normed-space structures needed to instantiate Mathlib's bundles. -/
def BoundedMap (k : BundleDbar.Metric E) (A : MapToTrivial E q) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ x v, ‖A x v‖ ^ 2 ≤ C * hermitianNormSq (k x) v

def sectionIntegral (c : DiscCoordinate M) (k : BundleDbar.Metric E)
    (s : Section E) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (hermitianNormSq (k x) (s x)) ∂discArea c

def weightedSectionIntegral (c : DiscCoordinate M) (k : BundleDbar.Metric E)
    (s : Section E) (ρ σ : ℝ) : ℝ≥0∞ :=
  ∫⁻ x in {x | 0 < ‖c x‖ ∧ ‖c x‖ < ρ},
    ENNReal.ofReal (hermitianNormSq (k x) (s x) * ‖c x‖ ^ (-σ)) ∂discArea c

/-- The fibres are the range of this A, not an independently chosen image. -/
def imageFibers (c : DiscCoordinate M) (A : MapToTrivial E q)
    (z : ℂ) : Submodule ℂ (ComplexVector q) :=
  LinearMap.range (A (c.symm z)).toLinearMap

def imageEquiv (c : DiscCoordinate M) (A : MapToTrivial E q)
    (hA : PointwiseInjective E A) (z : ℂ) :
    E (c.symm z) ≃ₗ[ℂ] imageFibers E c A z :=
  LinearEquiv.ofInjective (A (c.symm z)).toLinearMap (hA (c.symm z))

/-- Transport through an actual linear equivalence; no metric is chosen. -/
def transportMetric {V W : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (k : HermitianInnerProduct V)
    (e : V ≃ₗ[ℂ] W) : HermitianInnerProduct W where
  toFun u v := k.toFun (e.symm u) (e.symm v)
  map_add_left := by intros; simpa using k.map_add_left _ _ _
  map_smul_left := by intros; simpa using k.map_smul_left _ _ _
  map_add_right := by intros; simpa using k.map_add_right _ _ _
  map_smul_right := by intros; simpa using k.map_smul_right _ _ _
  conjugate_symmetric := by intros; exact k.conjugate_symmetric _ _
  self_adjoint := by intros; exact k.self_adjoint _
  positive_definite := by
    intro u
    exact ⟨(k.positive_definite _).1, (k.positive_definite _).2.trans (by simp)⟩

def imageMetric (c : DiscCoordinate M) (k : BundleDbar.Metric E)
    (A : MapToTrivial E q) (hA : PointwiseInjective E A) (z : ℂ) :
    HermitianInnerProduct (imageFibers E c A z) :=
  transportMetric (k (c.symm z)) (imageEquiv E c A hA z)

def imageSection (c : DiscCoordinate M) (A : MapToTrivial E q)
    (s : Section E) (z : ℂ) : ComplexVector q :=
  A (c.symm z) (s (c.symm z))

/-- Only one genuine local trivialization at a time is sent through A. -/
def imageFrame (c : DiscCoordinate M) (A : MapToTrivial E q)
    (a : M.Carrier) (z : ℂ) : Matrix (Fin q) (Fin r) ℂ :=
  fun i j => A (c.symm z)
    ((BundleDbar.localTriv (r := r) E a).symmL ℂ (c.symm z) (stdVec j)) i

def imageFrameDomain (c : DiscCoordinate M) (a : M.Carrier) : Set ℂ :=
  c '' ((BundleDbar.localTriv (r := r) E a).baseSet ∩
    (chartAt (ComplexVector 1) a).source)

def baseChange (c : DiscCoordinate M) (a : M.Carrier) (z : ℂ) : ComplexVector 1 :=
  chartPt a (c.symm z)

/-- Exact intrinsic equation u = s dz in the existing mixed alternating
tensor API. Here dz is the derivative of the actual base coordinate. -/
def IsSectionTopForm (c : DiscCoordinate M) (s : Section E)
    (u : BundleDbar.NQForm E 0) : Prop :=
  ∀ x (v : Fin 0 → TangentVector M x) (w : Fin 1 → TangentVector M x),
    ((u x).1 v) w = (show ℂ from mfderiv (ComplexModel 1) 𝓘(ℂ, ℂ) c x (w 0)) • s x

/-- Constructing the actual tensor and its local coordinate formula is an
obligation, not a global frame assumption or a supplied tensor proxy. -/
def SectionTopFormRealization : Prop :=
  ∀ (c : DiscCoordinate M), IsDiscCoordinate c → ∀ s : Section E,
    ∃ u : BundleDbar.NQForm E 0, IsSectionTopForm E c s u ∧
      ∀ a z, z ∈ BundleDbar.localDomain (r := r) E a →
        BundleDbar.coefficients (r := r) E u a z Fin.elim0 =
          wirt (fun w => c (chartInv a w)) z (stdVec 0) •
            sectionCoefficients (r := r) E s a z

/-- In particular this must recover the section from the possibly only
locally L² top form produced by Hörmander. It imposes no holomorphicity
on that unknown section. The equation fixes the section uniquely. -/
def TopFormSectionRecovery : Prop :=
  ∀ (c : DiscCoordinate M), IsDiscCoordinate c →
    ∀ u : BundleDbar.NQForm E 0, ∃! s : Section E, IsSectionTopForm E c s u

def discDbarScalar (c : DiscCoordinate M) (χ : M.Carrier → ℝ) (x : M.Carrier) : ℂ :=
  wirtBar (fun z : ℂ => (χ (c.symm z) : ℂ)) (c x) 1

def discLeviScalar (c : DiscCoordinate M) (φ : M.Carrier → ℝ) (x : M.Carrier) : ℝ :=
  (wirt (fun z : ℂ => wirtBar (fun w => (φ (c.symm w) : ℂ)) z 1) (c x) 1).re

/-- The dimension-one Griffiths-to-Nakano and weight-curvature bridge,
with both curvature tensors computed by the existing bundle API. -/
def CurveWeightedNakanoTransport : Prop :=
  ∀ (c : DiscCoordinate M), IsDiscCoordinate c →
    ∀ (k : BundleDbar.Metric E) (φ : M.Carrier → ℝ),
      BundleDbar.Holomorphic (r := r) E → BundleDbar.SmoothMetric (r := r) E k →
      BundleDbar.GriffithsNonnegative (r := r) E k → SmoothFn φ →
      (∀ x, 0 ≤ discLeviScalar c φ x) →
      BundleDbar.WeightedNakanoNonnegative (r := r) E k φ

/-- The actual source tensor s dbar χ ∧ dz, with the antiholomorphic slot
first, as in BundleDbar.coefficients. No proxy coefficient form is supplied. -/
def IsCutoffSourceForm (c : DiscCoordinate M) (s : Section E) (χ : M.Carrier → ℝ)
    (f : BundleDbar.NQForm E 1) : Prop :=
  ∀ x (v w : Fin 1 → TangentVector M x),
    ((f x).1 v) w =
      (discDbarScalar c χ x *
        star (show ℂ from mfderiv (ComplexModel 1) 𝓘(ℂ, ℂ) c x (v 0)) *
          (show ℂ from mfderiv (ComplexModel 1) 𝓘(ℂ, ℂ) c x (w 0))) • s x

/-- Construct the source in the genuine tensor API and verify the regularity
and closedness consumed by L14. Gluing is part of this target. -/
def CutoffSourceFormRealization : Prop :=
  ∀ (c : DiscCoordinate M), IsDiscCoordinate c → BundleDbar.Holomorphic (r := r) E →
    ∀ (s : Section E) (χ : M.Carrier → ℝ),
      HolomorphicSection (r := r) E s → SmoothFn χ →
      ∃ f : BundleDbar.NQForm E 1, IsCutoffSourceForm E c s χ f ∧
        BundleDbar.SmoothForm (r := r) E f ∧ BundleDbar.WeaklyClosed (r := r) E f

/-- Dropping the nonnegative curvature of k in the actual variational
inverse-curvature pairing gives this source bound. Together with the top-form
volume identity below, the same factor 2 cancels. This general bound is an
unproved bridge; it does not supply the weighted solve or D03. -/
def CutoffInverseCurvatureBound : Prop :=
  ∀ (c : DiscCoordinate M), IsDiscCoordinate c →
    ∀ (g : HermitianField M) (μ : Measure M.Carrier) (k : BundleDbar.Metric E)
      (φ χ : M.Carrier → ℝ),
      MetricSmooth g → IsRiemannianVolume g μ → BundleDbar.Holomorphic (r := r) E →
      BundleDbar.SmoothMetric (r := r) E k → BundleDbar.GriffithsNonnegative (r := r) E k →
      SmoothFn φ → SmoothFn χ → (∀ x, 0 < discLeviScalar c φ x) →
      ∀ (s : Section E) (f : BundleDbar.NQForm E 1),
        HolomorphicSection (r := r) E s → IsCutoffSourceForm E c s χ f →
        BundleDbar.inverseCurvatureIntegral (r := r) E g k μ φ f ≤
          2 * ∫⁻ x, ENNReal.ofReal
            (hermitianNormSq (k x) (s x) * ‖discDbarScalar c χ x‖ ^ 2 /
              discLeviScalar c φ x * Real.exp (-φ x)) ∂discArea c

/-- Actual norm/volume transport for the top form, against any smooth
auxiliary base metric. In the current G=2 Re h convention the factor is 2;
it cancels from both sides of the q=1 estimate. This identity remains unproved. -/
def SectionTopFormVolumeTransport : Prop :=
  ∀ (c : DiscCoordinate M), IsDiscCoordinate c →
    ∀ (g : HermitianField M) (μ : Measure M.Carrier) (k : BundleDbar.Metric E)
      (φ : M.Carrier → ℝ),
      MetricSmooth g → IsRiemannianVolume g μ → BundleDbar.Holomorphic (r := r) E →
      BundleDbar.SmoothMetric (r := r) E k → SmoothFn φ →
      ∀ (s : Section E) (u : BundleDbar.NQForm E 0),
        BundleDbar.LocallyL2 (r := r) E u → IsSectionTopForm E c s u →
        BundleDbar.weightedNormSq (r := r) E g k μ φ u =
          2 * ∫⁻ x, ENNReal.ofReal
            (hermitianNormSq (k x) (s x) * Real.exp (-φ x)) ∂discArea c

end BundlePresentation
end Yau.Blueprint
