import Yau.LeafProofs.L17LocalHolderAlgebraBilinear
import Yau.LeafProofs.L17LocalHolderAlgebraBasic
import Yau.LeafProofs.L17LocalHolderBanachAlgebraConstants

noncomputable section
open scoped ContDiff
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17BootstrapMetricAux
open L17Aux L17HolderAux L17SchauderAux L17LocalHolderAlgebraAux
open L17LocalHolderBanachAlgebraAux
variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}
variable (P : UniformChartPartition g) (T gamma : ℝ)
variable {F G H : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- A coefficient in the actual Banach wrapper acts on the original local jet graph. -/
def banachLocalBilinearCLM (B : F →L[ℝ] G →L[ℝ] H) :
    LocalHolderBanach F P T gamma →L[ℝ]
      LocalHolderSpace G P T gamma →L[ℝ] LocalHolderBanach H P T gamma :=
  ((ContinuousLinearMap.compL ℝ (LocalHolderSpace G P T gamma)
      (LocalHolderSpace H P T gamma) (LocalHolderBanach H P T gamma))
    (valueContinuousLinearEquiv H P T gamma).symm.toContinuousLinearMap).comp
      ((localBilinearCLM B).comp
        (valueContinuousLinearEquiv F P T gamma).toContinuousLinearMap)

theorem banachLocalBilinearCLM_value (B : F →L[ℝ] G →L[ℝ] H)
    (c : LocalHolderBanach F P T gamma) (u : LocalHolderSpace G P T gamma)
    (q : LocalCylinder P T) :
    banachLocalBilinearCLM P T gamma B c u q=B (c q) (localFun G u q) := rfl

def coefficientActionCLM :
    LocalHolderBanach (F →L[ℝ] G) P T gamma →L[ℝ]
      LocalHolderSpace F P T gamma →L[ℝ] LocalHolderBanach G P T gamma :=
  banachLocalBilinearCLM P T gamma (ContinuousLinearMap.id ℝ (F →L[ℝ] G))

theorem coefficientActionCLM_value
    (c : LocalHolderBanach (F →L[ℝ] G) P T gamma) (u : LocalHolderSpace F P T gamma)
    (q : LocalCylinder P T) :
    coefficientActionCLM P T gamma c u q=c q (localFun F u q) := rfl

theorem coefficientActionCLM_contDiff :
    ContDiff ℝ ∞ (fun p : LocalHolderBanach (F →L[ℝ] G) P T gamma ×
      LocalHolderSpace F P T gamma => coefficientActionCLM P T gamma p.1 p.2) :=
  ((coefficientActionCLM (F := F) (G := G) P T gamma).contDiff.comp contDiff_fst).clm_apply contDiff_snd

/-- A constant coefficient acts by the same pointwise linear map on every local jet. -/
theorem coefficientActionCLM_const (L : F →L[ℝ] G) (u : LocalHolderSpace F P T gamma) :
    coefficientActionCLM P T gamma (const (F →L[ℝ] G) P T gamma L) u =
      (valueContinuousLinearEquiv G P T gamma).symm (localMapCLM L u) := by
  apply L17LocalHolderBanachAlgebraAux.ext
  intro q
  rfl

end Yau.LeafProofs.L17BootstrapMetricAux
