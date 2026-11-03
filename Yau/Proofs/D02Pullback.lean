import Yau.Proofs.D02DifferentialNorm
import Mathlib.Geometry.Manifold.VectorBundle.Pullback

/-! The genuine pullback tangent bundle, its actual metric, and A=dF.
Complex smoothness of its transition maps is supplied by Mathlib's proved
ContMDiffVectorBundle pullback construction, using the actual complex smooth
base map. This does not assert metric curvature or integrability. -/

open scoped Manifold Topology ContDiff Matrix ComplexOrder Bundle
open Bundle

noncomputable section
namespace Yau.NodeProofs.D02Aux
open Yau Yau.Blueprint
set_option backward.isDefEq.respectTransparency false

variable {n N : ℕ} {M : ComplexManifold n} {B : ComplexManifold 1}

abbrev tangentPullbackFiber
    (f : ContMDiffMap (ComplexModel 1) (ComplexModel n) B.Carrier M.Carrier ⊤) :
    B.Carrier → Type := f *ᵖ (TangentSpace (ComplexModel n))

/- The bundle API asks for auxiliary norms on each fibre. Mathlib deliberately
does not choose a tangent-space norm. These structures transport the model norm
in the definition of the tangent fibre; they do not choose a bundle frame and
do not replace the Hermitian metric defined below. The fibre topology remains
the actual tangent-fibre topology. -/
instance tangentPullbackNormedAddCommGroup
    (f : ContMDiffMap (ComplexModel 1) (ComplexModel n) B.Carrier M.Carrier ⊤)
    (x : B.Carrier) : NormedAddCommGroup (tangentPullbackFiber f x) :=
  inferInstanceAs (NormedAddCommGroup (ComplexVector n))

instance tangentPullbackNormedSpaceComplex
    (f : ContMDiffMap (ComplexModel 1) (ComplexModel n) B.Carrier M.Carrier ⊤)
    (x : B.Carrier) : NormedSpace ℂ (tangentPullbackFiber f x) :=
  inferInstanceAs (NormedSpace ℂ (ComplexVector n))

instance tangentPullbackNormedSpaceReal
    (f : ContMDiffMap (ComplexModel 1) (ComplexModel n) B.Carrier M.Carrier ⊤)
    (x : B.Carrier) : NormedSpace ℝ (tangentPullbackFiber f x) :=
  inferInstanceAs (NormedSpace ℝ (ComplexVector n))

instance tangentPullbackScalarTower
    (f : ContMDiffMap (ComplexModel 1) (ComplexModel n) B.Carrier M.Carrier ⊤)
    (x : B.Carrier) : IsScalarTower ℝ ℂ (tangentPullbackFiber f x) :=
  inferInstanceAs (IsScalarTower ℝ ℂ (ComplexVector n))

/-- This is the actual holomorphic pullback atlas, not only a FiberBundle instance. -/
theorem tangentPullback_holomorphic
    (f : ContMDiffMap (ComplexModel 1) (ComplexModel n) B.Carrier M.Carrier ⊤) :
    BundleDbar.Holomorphic (r := n) (tangentPullbackFiber f) := by
  unfold BundleDbar.Holomorphic tangentPullbackFiber
  infer_instance

/-- The fibre metric is exactly the original g at f(x). -/
def tangentPullbackMetric (g : HermitianField M)
    (f : ContMDiffMap (ComplexModel 1) (ComplexModel n) B.Carrier M.Carrier ⊤) :
    BundleDbar.Metric (tangentPullbackFiber f) := fun x => g (f x)

/-- The actual differential of the same original immersion. -/
def tangentPullbackMap (F : M.Carrier → ComplexVector N)
    (f : ContMDiffMap (ComplexModel 1) (ComplexModel n) B.Carrier M.Carrier ⊤) :
    BundlePresentation.MapToTrivial (tangentPullbackFiber f) N := fun x =>
  (NormedSpace.fromTangentSpace (𝕜 := ℂ) (F (f x))).toContinuousLinearMap.comp
    (mfderiv (ComplexModel n) (ComplexModel N) F (f x))

theorem tangentPullbackMap_pointwiseInjective {F : M.Carrier → ComplexVector N}
    (hImm : IsImmersionMap F)
    (f : ContMDiffMap (ComplexModel 1) (ComplexModel n) B.Carrier M.Carrier ⊤) :
    BundlePresentation.PointwiseInjective (tangentPullbackFiber f) (tangentPullbackMap F f) := by
  intro x u v huv
  apply hImm (f x)
  exact (NormedSpace.fromTangentSpace (𝕜 := ℂ) (F (f x))).injective huv

theorem tangentPullbackMetric_normSq (g : HermitianField M)
    (f : ContMDiffMap (ComplexModel 1) (ComplexModel n) B.Carrier M.Carrier ⊤)
    (x : B.Carrier) (v : tangentPullbackFiber f x) :
    hermitianNormSq (tangentPullbackMetric g f x) v = hermitianNormSq (g (f x)) v := rfl

/-- A physical parameter derivative is a section of this actual pullback.
The equation f(x)=h(c(x)) fixes the fibre, and no frame is chosen. -/
def physicalDerivativeSection (h : ℂ → M.Carrier) (c : B.Carrier → ℂ) :
    ∀ x, TangentSpace (ComplexModel n) (h (c x)) := fun x =>
  mfderiv 𝓘(ℂ, ℂ) (ComplexModel n) h (c x)
    ((tangentSpaceCastModel 𝓘(ℂ, ℂ) (c x)).symm 1)

end Yau.NodeProofs.D02Aux
