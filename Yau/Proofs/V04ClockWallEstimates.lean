import Yau.Proofs.V04ClockWallAverage
import Yau.Proofs.V04ClockTaylorTimeJets

/-! The fourth original clock conclusion uses the actual computed
time-derivative density's smoothness, proved from the physical time jets. -/

open Filter
open scoped Topology ContDiff
noncomputable section
namespace Yau.Blueprint.V04Proof
open Yau Yau.Blueprint ClockErrorAux

variable {n q : ℕ} {X : KahlerManifold n}

theorem clockBoundaryDensity_contDiff {d : VariationData X q} (hd : VariationSetup d)
    {k : ClockData X} (hk : ClockCutoffs d k) {j a : ℕ} {F : VariationDisc X}
    (hF : AdmissibleVariationDisc d j F) :
    ContDiff ℝ ∞ (clockBoundaryDensity d k j a F) := by
  have hh := ClockTaylorAux.clockBoundaryCost_integrand_contDiff (a := a) hd hk hF
  change ContDiff ℝ ∞ (clockBoundaryDensity d k j a F) at hh
  exact hh

theorem clockWallEstimates {d : VariationData X q} (hd : VariationSetup d)
    {k : ClockData X} (hk : ClockCutoffs d k) (hFiber : FiberWallError d k) (hBase : BaseWallError d k)
    {a : ℕ} (ha : 3 ≤ 4 * a) (hpa : k.fiberPower ≤ 4 * a) (hpc : k.fiberPower ≤ k.dampingPower)
    (hc : 0 < k.dampingPower) (hloc : LocalizationEstimates d)
    (F : ℕ → ℝ → ℕ → VariationDisc X) (hF : LocalizedMinimizers d F) :
    ∀ r, 0 < r → ∀ᶠ j in atTop, ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ᶠ ν in atTop,
      clockSymplecticCost d k j a (F j ε ν) ≤ clockBoundaryCost d k j a (F j ε ν) + r :=
  clockWall_fourth_of_continuous hd hk hFiber hBase ha hpa hpc hc hloc
    (fun _ _ hA => (clockBoundaryDensity_contDiff hd hk hA).continuous) hF

end Yau.Blueprint.V04Proof
