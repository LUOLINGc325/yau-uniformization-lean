import Yau.Blueprint.Nodes
import Yau.Blueprint.HeatSmoothing
import Yau.Blueprint.ModelAssembly
import Yau.Blueprint.ExtraIntegrability
import Yau.Blueprint.HodgeContracts
import Yau.Blueprint.VariationContracts

/-! Concrete additional planning obligations, layered after the base predicates
so disc geometry can use base envelope/Schur definitions without an import cycle. -/
namespace Yau.Blueprint
open Yau
/-- Closed geometry obligations for the original arbitrary bundle and its
image presentation. These are targets, never extra assumptions of D03. -/
def B01 : Prop :=
  BundlePresentation.StandardDiscRealization ∧
  BundlePresentation.CompleteDiscMetricRealization ∧
  BundlePresentation.DiscAreaTransport ∧ BundleToEmbeddedReduction ∧
  ∀ (M : ComplexManifold 1) (r q : ℕ) (E : M.Carrier → Type)
    [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
    [∀ x, NormedSpace ℝ (E x)] [∀ x, IsScalarTower ℝ ℂ (E x)]
    [TopologicalSpace (Bundle.TotalSpace (ComplexVector r) E)]
    [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E],
    BundlePresentation.ImageLocalFrameTransport (r := r) (q := q) E ∧
    BundlePresentation.ImageMetricTransport (r := r) (q := q) E ∧
    BundlePresentation.ImageCurvatureTransport (r := r) (q := q) E ∧
    BundlePresentation.ImagePositivityTransport (r := r) (q := q) E ∧
    BundlePresentation.ImageSectionTransport (r := r) (q := q) E ∧
    BundlePresentation.ImageBoundTransport (q := q) E ∧
    BundlePresentation.ImageIntegralTransport (r := r) (q := q) E ∧
    BundlePresentation.SectionTopFormRealization (r := r) E ∧
    BundlePresentation.TopFormSectionRecovery E ∧
    BundlePresentation.CutoffSourceFormRealization (r := r) E ∧
    BundlePresentation.CurveWeightedNakanoTransport (r := r) E ∧
    BundlePresentation.CutoffInverseCurvatureBound (r := r) E ∧
    BundlePresentation.SectionTopFormVolumeTransport (r := r) E

def D03 : Prop := BundleExtraIntegrability

def P06 : Prop := ∀ (n : ℕ) (X : KahlerManifold n), HodgeSmoothBoundedTarget X ∧ LipschitzHessianHeatTarget X

def D05 : Prop := ∀ (n : ℕ) (X : KahlerManifold n), DiscFramesContract X.manifold

def V02 : Prop := ∀ (n : ℕ) (X : KahlerManifold n), V02Contract X

def V03 : Prop := ∀ (n : ℕ) (X : KahlerManifold n), V03Contract X

def V04 : Prop := ∀ (n : ℕ) (X : KahlerManifold n), V04Contract X


def Y01 : Prop := Alignment.CanonicalModelConstruction
def Y03 : Prop := Alignment.Y03
def Y04 : Prop := Alignment.Y04
def Y05 : Prop := Alignment.Y05
def Y06 : Prop := Alignment.Y06
def Y07 : Prop := Alignment.CanonicalGridTail

end Yau.Blueprint
