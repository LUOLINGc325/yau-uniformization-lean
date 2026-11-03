import Yau.LeafProofs.L17BootstrapTransportPullback
import Yau.LeafProofs.L17BootstrapTransportLocalOperations
import Yau.LeafProofs.L17BootstrapTransportCoefficients
import Yau.LeafProofs.L17LocalHolderAlgebraBilinear
import Yau.LeafProofs.L17SchauderSpaceNorm

open Set Metric
open scoped Topology ContDiff
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17BootstrapTransportAux
open L17Aux L17HolderAux L17SchauderAux L17BootstrapPatchAux L17SmallTranslationAux
open L17LocalHolderAlgebraAux
variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}
variable {P : UniformChartPartition g} {x : M.Carrier} {T gamma : ℝ} {hT : 0 < T}

local instance transportRawD1NormedAddCommGroup (n : ℕ) : NormedAddCommGroup (D1 n) := inferInstance
local instance transportRawD1NormedSpace (n : ℕ) : NormedSpace ℝ (D1 n) := inferInstance
local instance transportRawD2NormedAddCommGroup (n : ℕ) : NormedAddCommGroup (D2 n) := inferInstance
local instance transportRawD2NormedSpace (n : ℕ) : NormedSpace ℝ (D2 n) := inferInstance
local instance transportRawEndNormedAddCommGroup (n : ℕ) : NormedAddCommGroup (ComplexVector n →L[ℝ] ComplexVector n) := inferInstance
local instance transportRawEndNormedSpace (n : ℕ) : NormedSpace ℝ (ComplexVector n →L[ℝ] ComplexVector n) := inferInstance
local instance transportRawKNormedAddCommGroup (n : ℕ) : NormedAddCommGroup (ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ComplexVector n) := inferInstance
local instance transportRawKNormedSpace (n : ℕ) : NormedSpace ℝ (ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ComplexVector n) := inferInstance
local instance transportRawEndD1NormedAddCommGroup (n : ℕ) : NormedAddCommGroup ((ComplexVector n →L[ℝ] ComplexVector n) →L[ℝ] D1 n) := inferInstance
local instance transportRawEndD1NormedSpace (n : ℕ) : NormedSpace ℝ ((ComplexVector n →L[ℝ] ComplexVector n) →L[ℝ] D1 n) := inferInstance
local instance transportRawEndD2NormedAddCommGroup (n : ℕ) : NormedAddCommGroup ((ComplexVector n →L[ℝ] ComplexVector n) →L[ℝ] D2 n) := inferInstance
local instance transportRawEndD2NormedSpace (n : ℕ) : NormedSpace ℝ ((ComplexVector n →L[ℝ] ComplexVector n) →L[ℝ] D2 n) := inferInstance
local instance transportRawKD2NormedAddCommGroup (n : ℕ) : NormedAddCommGroup ((ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ComplexVector n) →L[ℝ] D2 n) := inferInstance
local instance transportRawKD2NormedSpace (n : ℕ) : NormedSpace ℝ ((ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ComplexVector n) →L[ℝ] D2 n) := inferInstance
local instance transportRawD2D2NormedAddCommGroup (n : ℕ) : NormedAddCommGroup (D2 n →L[ℝ] D2 n) := inferInstance
local instance transportRawD2D2NormedSpace (n : ℕ) : NormedSpace ℝ (D2 n →L[ℝ] D2 n) := inferInstance

def gradientComposition : D1 n →L[ℝ] (ComplexVector n →L[ℝ] ComplexVector n) →L[ℝ] D1 n :=
  ContinuousLinearMap.compL ℝ (ComplexVector n) (ComplexVector n) ℝ

def hessianFirstComposition : D2 n →L[ℝ] (ComplexVector n →L[ℝ] ComplexVector n) →L[ℝ] D2 n :=
  ContinuousLinearMap.compL ℝ (ComplexVector n) (ComplexVector n) (D1 n)

def hessianSecondComposition : (ComplexVector n →L[ℝ] ComplexVector n) →L[ℝ] D2 n →L[ℝ] D2 n :=
  (ContinuousLinearMap.compL ℝ (ComplexVector n) (D1 n) (D1 n)).comp
    (ContinuousLinearMap.compL ℝ (ComplexVector n) (ComplexVector n) ℝ).flip

def gradientHessianComposition : D1 n →L[ℝ]
    (ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ComplexVector n) →L[ℝ] D2 n :=
  (ContinuousLinearMap.compL ℝ (ComplexVector n)
    (ComplexVector n →L[ℝ] ComplexVector n) (D1 n)).comp
      (ContinuousLinearMap.compL ℝ (ComplexVector n) (ComplexVector n) ℝ)

def rawFunctionLocal (u : SchauderSpace P T gamma hT) : LocalHolderSpace ℝ P T gamma :=
  holderRestrictionCLM u.val.1.1

def rawTimeLocal (u : SchauderSpace P T gamma hT) : LocalHolderSpace ℝ P T gamma :=
  holderRestrictionCLM u.val.2.2

theorem rawFunctionLocal_norm_le (u : SchauderSpace P T gamma hT) : ‖rawFunctionLocal u‖ ≤ ‖u‖ :=
  (holderRestrictionCLM_norm_le u.val.1.1).trans ((le_max_left _ _).trans (le_max_left _ _))

theorem rawTimeLocal_norm_le (u : SchauderSpace P T gamma hT) : ‖rawTimeLocal u‖ ≤ ‖u‖ :=
  (holderRestrictionCLM_norm_le u.val.2.2).trans ((le_max_right _ _).trans (le_max_right _ _))

theorem rawGradient_norm_le (u : SchauderSpace P T gamma hT) : ‖u.val.1.2‖ ≤ ‖u‖ :=
  (le_max_right _ _).trans (le_max_left _ _)

theorem rawHessian_norm_le (u : SchauderSpace P T gamma hT) : ‖u.val.2.1‖ ≤ ‖u‖ :=
  (le_max_left _ _).trans (le_max_right _ _)

variable (D : BootstrapPatch P x) {theta : ComplexVector n} (htheta : ‖theta‖ < D.smallRadius)
variable (hgamma0 : 0 ≤ gamma) (hgamma1 : gamma ≤ 1) (hTime : T ≤ P.radius^2) (hr : P.radius ≤ 1)

def rawCorrectionValue (u : SchauderSpace P T gamma hT) : LocalHolderSpace ℝ P T gamma :=
  localPullbackCLM D htheta ℝ hgamma0 hgamma1 (rawFunctionLocal u)-rawFunctionLocal u

def rawCorrectionTime (u : SchauderSpace P T gamma hT) : LocalHolderSpace ℝ P T gamma :=
  localPullbackCLM D htheta ℝ hgamma0 hgamma1 (rawTimeLocal u)-rawTimeLocal u

def rawCorrectionGradient (u : SchauderSpace P T gamma hT) : LocalHolderSpace (D1 n) P T gamma :=
  localBilinearElement gradientComposition
    (localPullbackCLM D htheta (D1 n) hgamma0 hgamma1 u.val.1.2)
    (coordinateJacobianHolder D theta hTime hgamma1 hr)-u.val.1.2

def rawCorrectionHessian (u : SchauderSpace P T gamma hT) : LocalHolderSpace (D2 n) P T gamma :=
  localBilinearElement hessianSecondComposition (coordinateJacobianHolder D theta hTime hgamma1 hr)
    (localBilinearElement hessianFirstComposition
      (localPullbackCLM D htheta (D2 n) hgamma0 hgamma1 u.val.2.1)
      (coordinateJacobianHolder D theta hTime hgamma1 hr))+
    localBilinearElement gradientHessianComposition
      (localPullbackCLM D htheta (D1 n) hgamma0 hgamma1 u.val.1.2)
      (scaledCoordinateHessianHolder D theta hTime hgamma1 hr)-u.val.2.1

def jacobianBudget : ℝ := 1+4*D.bound*P.radius
def hessianBudget : ℝ := 4*P.radius^2*D.bound

theorem jacobianBudget_nonneg : 0 ≤ jacobianBudget D := by
  dsimp only [jacobianBudget]
  have hB := zero_le_one.trans D.bound_ge_one
  have hr := P.radius_pos
  positivity

theorem hessianBudget_nonneg : 0 ≤ hessianBudget D := by
  dsimp only [hessianBudget]
  have hB := zero_le_one.trans D.bound_ge_one
  positivity

include htheta hgamma0 in
theorem coordinateJacobianHolder_norm_le_budget :
    ‖coordinateJacobianHolder D theta hTime hgamma1 hr‖ ≤ jacobianBudget D := by
  apply (coordinateJacobianHolder_norm_le D theta hTime hgamma1 hr hgamma0).trans
  dsimp only [jacobianBudget]
  have ht : ‖theta‖ ≤ P.radius := (htheta.trans_le D.smallRadius_le_radius).le
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_left ht
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) (zero_le_one.trans D.bound_ge_one)))

include htheta hgamma0 in
theorem scaledCoordinateHessianHolder_norm_le_budget :
    ‖scaledCoordinateHessianHolder D theta hTime hgamma1 hr‖ ≤ hessianBudget D := by
  apply (scaledCoordinateHessianHolder_norm_le D theta hTime hgamma1 hr hgamma0).trans
  have ht : ‖theta‖ ≤ P.radius := (htheta.trans_le D.smallRadius_le_radius).le
  dsimp only [hessianBudget]
  nlinarith [mul_le_mul_of_nonneg_left ht
    (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 4) P.radius_pos.le)
      (zero_le_one.trans D.bound_ge_one))]

theorem rawCorrectionValue_norm_le (u : SchauderSpace P T gamma hT) :
    ‖rawCorrectionValue D htheta hgamma0 hgamma1 u‖ ≤ 3*‖u‖ := by
  apply (norm_sub_le _ _).trans
  have hp := localPullbackElement_norm_le D htheta ℝ hgamma0 hgamma1 (rawFunctionLocal u)
  change ‖localPullbackCLM D htheta ℝ hgamma0 hgamma1 (rawFunctionLocal u)‖ ≤ _ at hp
  linarith [rawFunctionLocal_norm_le u]

theorem rawCorrectionTime_norm_le (u : SchauderSpace P T gamma hT) :
    ‖rawCorrectionTime D htheta hgamma0 hgamma1 u‖ ≤ 3*‖u‖ := by
  apply (norm_sub_le _ _).trans
  have hp := localPullbackElement_norm_le D htheta ℝ hgamma0 hgamma1 (rawTimeLocal u)
  change ‖localPullbackCLM D htheta ℝ hgamma0 hgamma1 (rawTimeLocal u)‖ ≤ _ at hp
  linarith [rawTimeLocal_norm_le u]

theorem rawCorrectionGradient_norm_le (u : SchauderSpace P T gamma hT) :
    ‖rawCorrectionGradient D htheta hgamma0 hgamma1 hTime hr u‖ ≤
      (4*‖gradientComposition (n := n)‖*jacobianBudget D+1)*‖u‖ := by
  have hp := localPullbackElement_norm_le D htheta (D1 n) hgamma0 hgamma1 u.val.1.2
  change ‖localPullbackCLM D htheta (D1 n) hgamma0 hgamma1 u.val.1.2‖ ≤ _ at hp
  have hprod := localBilinearElement_norm_le gradientComposition
    (localPullbackCLM D htheta (D1 n) hgamma0 hgamma1 u.val.1.2)
    (coordinateJacobianHolder D theta hTime hgamma1 hr)
  have hprod' : ‖localBilinearElement gradientComposition
      (localPullbackCLM D htheta (D1 n) hgamma0 hgamma1 u.val.1.2)
      (coordinateJacobianHolder D theta hTime hgamma1 hr)‖ ≤
      2*‖gradientComposition (n := n)‖*(2*‖u‖)*jacobianBudget D := by
    apply hprod.trans
    gcongr
    · exact hp.trans (mul_le_mul_of_nonneg_left (rawGradient_norm_le u) (by norm_num))
    · exact coordinateJacobianHolder_norm_le_budget D htheta hgamma0 hgamma1 hTime hr
  apply (norm_sub_le _ _).trans
  nlinarith [rawGradient_norm_le u]

theorem rawCorrectionHessian_norm_le (u : SchauderSpace P T gamma hT) :
    ‖rawCorrectionHessian D htheta hgamma0 hgamma1 hTime hr u‖ ≤
      (8*‖hessianSecondComposition (n := n)‖*‖hessianFirstComposition (n := n)‖*(jacobianBudget D)^2+
        4*‖gradientHessianComposition (n := n)‖*hessianBudget D+1)*‖u‖ := by
  have hj0 := jacobianBudget_nonneg D
  let Ju := coordinateJacobianHolder D theta hTime hgamma1 hr
  let Ku := scaledCoordinateHessianHolder D theta hTime hgamma1 hr
  let Qu := localPullbackCLM D htheta (D2 n) hgamma0 hgamma1 u.val.2.1
  let pu := localPullbackCLM D htheta (D1 n) hgamma0 hgamma1 u.val.1.2
  have hJ : ‖Ju‖ ≤ jacobianBudget D :=
    coordinateJacobianHolder_norm_le_budget D htheta hgamma0 hgamma1 hTime hr
  have hK : ‖Ku‖ ≤ hessianBudget D :=
    scaledCoordinateHessianHolder_norm_le_budget D htheta hgamma0 hgamma1 hTime hr
  have hQ : ‖Qu‖ ≤ 2*‖u‖ := by
    exact (localPullbackElement_norm_le D htheta (D2 n) hgamma0 hgamma1 u.val.2.1).trans
      (mul_le_mul_of_nonneg_left (rawHessian_norm_le u) (by norm_num))
  have hp : ‖pu‖ ≤ 2*‖u‖ := by
    exact (localPullbackElement_norm_le D htheta (D1 n) hgamma0 hgamma1 u.val.1.2).trans
      (mul_le_mul_of_nonneg_left (rawGradient_norm_le u) (by norm_num))
  have hFirst : ‖localBilinearElement hessianFirstComposition Qu Ju‖ ≤
      4*‖hessianFirstComposition (n := n)‖*‖u‖*jacobianBudget D := by
    apply (localBilinearElement_norm_le hessianFirstComposition Qu Ju).trans
    calc
      _ ≤ 2*‖hessianFirstComposition (n := n)‖*(2*‖u‖)*jacobianBudget D := by gcongr
      _ = _ := by ring
  have hSecond : ‖localBilinearElement hessianSecondComposition Ju
      (localBilinearElement hessianFirstComposition Qu Ju)‖ ≤
      8*‖hessianSecondComposition (n := n)‖*‖hessianFirstComposition (n := n)‖*(jacobianBudget D)^2*‖u‖ := by
    apply (localBilinearElement_norm_le hessianSecondComposition Ju _).trans
    calc
      _ ≤ 2*‖hessianSecondComposition (n := n)‖*jacobianBudget D*
          (4*‖hessianFirstComposition (n := n)‖*‖u‖*jacobianBudget D) := by gcongr
      _ = _ := by ring
  have hGrad : ‖localBilinearElement gradientHessianComposition pu Ku‖ ≤
      4*‖gradientHessianComposition (n := n)‖*hessianBudget D*‖u‖ := by
    apply (localBilinearElement_norm_le gradientHessianComposition pu Ku).trans
    calc
      _ ≤ 2*‖gradientHessianComposition (n := n)‖*(2*‖u‖)*hessianBudget D := by gcongr
      _ = _ := by ring
  change ‖localBilinearElement hessianSecondComposition Ju
      (localBilinearElement hessianFirstComposition Qu Ju)+
      localBilinearElement gradientHessianComposition pu Ku-u.val.2.1‖ ≤ _
  calc
    _ ≤ (‖localBilinearElement hessianSecondComposition Ju
        (localBilinearElement hessianFirstComposition Qu Ju)‖+
        ‖localBilinearElement gradientHessianComposition pu Ku‖)+‖u.val.2.1‖ :=
      (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ (8*‖hessianSecondComposition (n := n)‖*‖hessianFirstComposition (n := n)‖*(jacobianBudget D)^2*‖u‖+
        4*‖gradientHessianComposition (n := n)‖*hessianBudget D*‖u‖)+‖u‖ :=
      add_le_add (add_le_add hSecond hGrad) (rawHessian_norm_le u)
    _ = _ := by ring

def strongTransportBudget : ℝ := 4+(3+P.radius)*D.bound*P.radius

def transportBudget : ℝ :=
  4+(4*‖gradientComposition (n := n)‖*jacobianBudget D+1)+
    (8*‖hessianSecondComposition (n := n)‖*‖hessianFirstComposition (n := n)‖*(jacobianBudget D)^2+
      4*‖gradientHessianComposition (n := n)‖*hessianBudget D+1)+strongTransportBudget D

theorem transportBudget_pos : 0 < transportBudget D := by
  have hj := jacobianBudget_nonneg D
  have hk := hessianBudget_nonneg D
  have hB := zero_le_one.trans D.bound_ge_one
  have hr := P.radius_pos
  unfold transportBudget strongTransportBudget
  positivity

theorem rawCorrection_norms_le (u : SchauderSpace P T gamma hT) :
    ‖rawCorrectionValue D htheta hgamma0 hgamma1 u‖ ≤ transportBudget D*‖u‖ ∧
    ‖rawCorrectionGradient D htheta hgamma0 hgamma1 hTime hr u‖ ≤ transportBudget D*‖u‖ ∧
    ‖rawCorrectionHessian D htheta hgamma0 hgamma1 hTime hr u‖ ≤ transportBudget D*‖u‖ ∧
    ‖rawCorrectionTime D htheta hgamma0 hgamma1 u‖ ≤ transportBudget D*‖u‖ := by
  have hj := jacobianBudget_nonneg D
  have hk := hessianBudget_nonneg D
  have hB := zero_le_one.trans D.bound_ge_one
  have hrho := P.radius_pos
  have hs : 0 ≤ strongTransportBudget D := by dsimp only [strongTransportBudget]; positivity
  have hg : 0 ≤ 4*‖gradientComposition (n := n)‖*jacobianBudget D+1 := by positivity
  have hH : 0 ≤ 8*‖hessianSecondComposition (n := n)‖*‖hessianFirstComposition (n := n)‖*(jacobianBudget D)^2+
      4*‖gradientHessianComposition (n := n)‖*hessianBudget D+1 := by positivity
  have h3 : 3 ≤ transportBudget D := by unfold transportBudget; linarith
  have hgC : 4*‖gradientComposition (n := n)‖*jacobianBudget D+1 ≤ transportBudget D := by
    unfold transportBudget
    linarith
  have hHC : 8*‖hessianSecondComposition (n := n)‖*‖hessianFirstComposition (n := n)‖*(jacobianBudget D)^2+
      4*‖gradientHessianComposition (n := n)‖*hessianBudget D+1 ≤ transportBudget D := by
    unfold transportBudget
    linarith
  exact ⟨(rawCorrectionValue_norm_le D htheta hgamma0 hgamma1 u).trans
      (mul_le_mul_of_nonneg_right h3 (norm_nonneg u)),
    (rawCorrectionGradient_norm_le D htheta hgamma0 hgamma1 hTime hr u).trans
      (mul_le_mul_of_nonneg_right hgC (norm_nonneg u)),
    (rawCorrectionHessian_norm_le D htheta hgamma0 hgamma1 hTime hr u).trans
      (mul_le_mul_of_nonneg_right hHC (norm_nonneg u)),
    (rawCorrectionTime_norm_le D htheta hgamma0 hgamma1 u).trans
      (mul_le_mul_of_nonneg_right h3 (norm_nonneg u))⟩

end Yau.LeafProofs.L17BootstrapTransportAux
