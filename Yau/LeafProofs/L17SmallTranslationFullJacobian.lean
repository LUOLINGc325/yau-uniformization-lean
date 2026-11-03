import Yau.LeafProofs.L17SmallTranslationJacobian
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

open Set Metric
open scoped Topology ContDiff
noncomputable section
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17SmallTranslationAux

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

def cutoffFullMap (χ : E → ℝ) (p : E × E) : E × E := (p.1,cutoffTranslation χ p.1 p.2)

theorem cutoffFullMap_contDiff {χ : E → ℝ} (hχ : ContDiff ℝ ∞ χ) :
    ContDiff ℝ ∞ (cutoffFullMap χ) := contDiff_fst.prodMk (cutoffTranslation_joint_contDiff hχ)

def cutoffFullJacobianEquiv (χ : E → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hDf : ∀ z, ‖fderiv ℝ χ z‖ ≤ L) (θ : E) (hθ : ‖θ‖ < smallTranslationRadius L) (z : E) :
    (E × E) ≃L[ℝ] (E × E) :=
  blockTriangularEquiv (χ z • ContinuousLinearMap.id ℝ E) (cutoffJacobianEquiv χ L hL hDf θ hθ z)

theorem cutoffFullMap_hasFDerivAt {χ : E → ℝ} (hχ : ContDiff ℝ ∞ χ) {L : ℝ} (hL : 0 ≤ L)
    (hDf : ∀ z, ‖fderiv ℝ χ z‖ ≤ L) {θ : E} (hθ : ‖θ‖ < smallTranslationRadius L) (z : E) :
    HasFDerivAt (cutoffFullMap χ) (cutoffFullJacobianEquiv χ L hL hDf θ hθ z).toContinuousLinearMap (θ,z) := by
  have hfst : HasFDerivAt (fun p : E × E => p.1) (ContinuousLinearMap.fst ℝ E E) (θ,z) :=
    (ContinuousLinearMap.fst ℝ E E).hasFDerivAt
  have hsnd : HasFDerivAt (fun p : E × E => p.2) (ContinuousLinearMap.snd ℝ E E) (θ,z) :=
    (ContinuousLinearMap.snd ℝ E E).hasFDerivAt
  have hχpair := ((hχ.differentiable (by simp) z).hasFDerivAt).comp (θ,z) hsnd
  have h := hfst.prodMk (hsnd.add (hχpair.smul hfst))
  convert h using 1
  · funext p
    rfl
  · apply ContinuousLinearMap.ext
    intro p
    rcases p with ⟨a,b⟩
    change (a,χ z • a+(b+(fderiv ℝ χ z b) • θ))=
      (a,b+(χ z • a+(fderiv ℝ χ z b) • θ))
    congr 1
    abel

end Yau.LeafProofs.L17SmallTranslationAux
