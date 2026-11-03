import Yau.LeafProofs.L17BootstrapTransportRawSup
import Yau.LeafProofs.L17BootstrapHolderInterpolationSpace

open Set Metric
open scoped Topology ContDiff
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17BootstrapTransportAux
open L17Aux L17HolderAux L17SchauderAux L17BootstrapPatchAux
open L17BootstrapHolderInterpolationAux
attribute [local instance] transportRawD1NormedAddCommGroup transportRawD1NormedSpace
  transportRawD2NormedAddCommGroup transportRawD2NormedSpace
  transportRawEndNormedAddCommGroup transportRawEndNormedSpace
  transportRawKNormedAddCommGroup transportRawKNormedSpace
  transportRawEndD1NormedAddCommGroup transportRawEndD1NormedSpace
  transportRawEndD2NormedAddCommGroup transportRawEndD2NormedSpace
  transportRawKD2NormedAddCommGroup transportRawKD2NormedSpace
  transportRawD2D2NormedAddCommGroup transportRawD2D2NormedSpace
variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}
variable {P : UniformChartPartition g} {x : M.Carrier} {T gamma : ℝ} {hT : 0 < T}
variable (D : BootstrapPatch P x)

theorem strongTransportBudget_ge_one : 1 ≤ strongTransportBudget D := by
  have hB := zero_le_one.trans D.bound_ge_one
  have hr := P.radius_pos.le
  have h := mul_nonneg (mul_nonneg (by linarith : 0 ≤ 3+P.radius) hB) hr
  dsimp only [strongTransportBudget]
  linarith

theorem gradientCap_le_strongTransportBudget : 2+D.bound*P.radius ≤ strongTransportBudget D := by
  have hB := zero_le_one.trans D.bound_ge_one
  have hr := P.radius_pos.le
  have h1 := mul_nonneg hB hr
  have h2 := mul_nonneg hr h1
  dsimp only [strongTransportBudget]
  nlinarith

theorem strongTransportBudget_le_transportBudget : strongTransportBudget D ≤ transportBudget D := by
  have hj := jacobianBudget_nonneg D
  have hk := hessianBudget_nonneg D
  have hg : 0 ≤ 4*‖gradientComposition (n := n)‖*jacobianBudget D+1 := by positivity
  have hH : 0 ≤ 8*‖hessianSecondComposition (n := n)‖*‖hessianFirstComposition (n := n)‖*(jacobianBudget D)^2+
      4*‖gradientHessianComposition (n := n)‖*hessianBudget D+1 := by positivity
  dsimp only [transportBudget]
  linarith

variable {theta : ComplexVector n} (htheta : ‖theta‖ < D.smallRadius)
variable (hgamma0 : 0 ≤ gamma) (hgamma1 : gamma ≤ 1) (hTime : T ≤ P.radius^2) (hr : P.radius ≤ 1)

theorem rawCorrection_sup_norms_le (u : SchauderSpace P T gamma hT) (q : LocalCylinder P T) :
    ‖localFun ℝ (rawCorrectionValue D htheta hgamma0 hgamma1 u) q‖ ≤
        transportBudget D*‖u‖*(‖theta‖/P.radius)^gamma ∧
    ‖localFun (D1 n) (rawCorrectionGradient D htheta hgamma0 hgamma1 hTime hr u) q‖ ≤
        transportBudget D*‖u‖*(‖theta‖/P.radius)^gamma ∧
    ‖localFun (D2 n) (rawCorrectionHessian D htheta hgamma0 hgamma1 hTime hr u) q‖ ≤
        transportBudget D*‖u‖*(‖theta‖/P.radius)^gamma ∧
    ‖localFun ℝ (rawCorrectionTime D htheta hgamma0 hgamma1 u) q‖ ≤
        transportBudget D*‖u‖*(‖theta‖/P.radius)^gamma := by
  have hPow := Real.rpow_nonneg (BootstrapPatch.parameter_fraction_nonneg (P := P) theta) gamma
  have hN : 0 ≤ ‖u‖*(‖theta‖/P.radius)^gamma := mul_nonneg (norm_nonneg u) hPow
  have h1 : 1 ≤ transportBudget D := (strongTransportBudget_ge_one D).trans
    (strongTransportBudget_le_transportBudget D)
  have hg := (gradientCap_le_strongTransportBudget D).trans (strongTransportBudget_le_transportBudget D)
  have hH := strongTransportBudget_le_transportBudget D
  have h0cap : ‖u‖*(‖theta‖/P.radius)^gamma ≤ transportBudget D*‖u‖*(‖theta‖/P.radius)^gamma := by
    simpa only [one_mul,mul_assoc] using mul_le_mul_of_nonneg_right h1 hN
  have hgcap : (2+D.bound*P.radius)*‖u‖*(‖theta‖/P.radius)^gamma ≤
      transportBudget D*‖u‖*(‖theta‖/P.radius)^gamma := by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hg hN
  have hHcap : strongTransportBudget D*‖u‖*(‖theta‖/P.radius)^gamma ≤
      transportBudget D*‖u‖*(‖theta‖/P.radius)^gamma := by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hH hN
  exact ⟨(rawCorrectionValue_sup_le D htheta hgamma0 hgamma1 u q).trans h0cap,
    (rawCorrectionGradient_sup_le D htheta hgamma0 hgamma1 hTime hr u q).trans hgcap,
    (rawCorrectionHessian_sup_le D htheta hgamma0 hgamma1 hTime hr u q).trans hHcap,
    (rawCorrectionTime_sup_le D htheta hgamma0 hgamma1 u q).trans h0cap⟩

theorem half_quarter_localWeaken_norm_le {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {A eps : ℝ} (hTime : T ≤ P.radius^2) (hA : 0 ≤ A) (heps : 0 ≤ eps) (heps1 : eps ≤ 1)
    (u : LocalHolderSpace F P T (1/2)) (hSup : ∀ q, ‖localFun F u q‖ ≤ A*eps^(1/2 : ℝ))
    (hNorm : ‖u‖ ≤ A) :
    ‖localWeakenElement F P hTime (by norm_num : (1/4 : ℝ) ≤ 1/2) u‖ ≤ 4*A*eps^(1/4 : ℝ) := by
  have h := localWeaken_norm_le_interpolation P hTime
    (by norm_num : 0 < (1/4 : ℝ) ∧ (1/4 : ℝ) < 1/2)
    (mul_nonneg hA (Real.rpow_nonneg heps _)) (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hA)
    u hSup (hNorm.trans (by linarith))
  exact h.trans (half_quarter_budget_le hA heps heps1)

def quarterCorrectionValue (hTime : T ≤ P.radius^2) (u : SchauderSpace P T (1/2) hT) :
    LocalHolderSpace ℝ P T (1/4) :=
  localWeakenElement ℝ P hTime (by norm_num : (1/4 : ℝ) ≤ 1/2)
    (rawCorrectionValue D htheta (by norm_num) (by norm_num) u)

def quarterCorrectionGradient (hTime : T ≤ P.radius^2) (hr : P.radius ≤ 1)
    (u : SchauderSpace P T (1/2) hT) : LocalHolderSpace (D1 n) P T (1/4) :=
  localWeakenElement (D1 n) P hTime (by norm_num : (1/4 : ℝ) ≤ 1/2)
    (rawCorrectionGradient D htheta (by norm_num) (by norm_num) hTime hr u)

def quarterCorrectionHessian (hTime : T ≤ P.radius^2) (hr : P.radius ≤ 1)
    (u : SchauderSpace P T (1/2) hT) : LocalHolderSpace (D2 n) P T (1/4) :=
  localWeakenElement (D2 n) P hTime (by norm_num : (1/4 : ℝ) ≤ 1/2)
    (rawCorrectionHessian D htheta (by norm_num) (by norm_num) hTime hr u)

def quarterCorrectionTime (hTime : T ≤ P.radius^2) (u : SchauderSpace P T (1/2) hT) :
    LocalHolderSpace ℝ P T (1/4) :=
  localWeakenElement ℝ P hTime (by norm_num : (1/4 : ℝ) ≤ 1/2)
    (rawCorrectionTime D htheta (by norm_num) (by norm_num) u)

theorem quarterCorrection_norms_le (hTime : T ≤ P.radius^2) (hr : P.radius ≤ 1)
    (u : SchauderSpace P T (1/2) hT) :
    ‖quarterCorrectionValue D htheta hTime u‖ ≤ 4*(transportBudget D*‖u‖)*(‖theta‖/P.radius)^(1/4 : ℝ) ∧
    ‖quarterCorrectionGradient D htheta hTime hr u‖ ≤ 4*(transportBudget D*‖u‖)*(‖theta‖/P.radius)^(1/4 : ℝ) ∧
    ‖quarterCorrectionHessian D htheta hTime hr u‖ ≤ 4*(transportBudget D*‖u‖)*(‖theta‖/P.radius)^(1/4 : ℝ) ∧
    ‖quarterCorrectionTime D htheta hTime u‖ ≤ 4*(transportBudget D*‖u‖)*(‖theta‖/P.radius)^(1/4 : ℝ) := by
  have hA := mul_nonneg (transportBudget_pos D).le (norm_nonneg u)
  have heps := BootstrapPatch.parameter_fraction_nonneg (P := P) theta
  have heps1 := (D.parameter_fraction_lt_one htheta).le
  have hNorm := rawCorrection_norms_le D htheta (by norm_num : (0 : ℝ) ≤ 1/2)
    (by norm_num : (1/2 : ℝ) ≤ 1) hTime hr u
  have hSup := rawCorrection_sup_norms_le D htheta (by norm_num : (0 : ℝ) ≤ 1/2)
    (by norm_num : (1/2 : ℝ) ≤ 1) hTime hr u
  exact ⟨half_quarter_localWeaken_norm_le hTime hA heps heps1 _ (fun q => (hSup q).1) hNorm.1,
    half_quarter_localWeaken_norm_le hTime hA heps heps1 _ (fun q => (hSup q).2.1) hNorm.2.1,
    half_quarter_localWeaken_norm_le hTime hA heps heps1 _ (fun q => (hSup q).2.2.1) hNorm.2.2.1,
    half_quarter_localWeaken_norm_le hTime hA heps heps1 _ (fun q => (hSup q).2.2.2) hNorm.2.2.2⟩

end Yau.LeafProofs.L17BootstrapTransportAux
