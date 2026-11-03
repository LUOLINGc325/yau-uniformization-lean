import Yau.Proofs.V04ClockLossLocalization
import Yau.Proofs.V04ClockWallEstimates
import Yau.Proofs.V04ClockTaylor

open Filter
open scoped Topology
noncomputable section
namespace Yau.Blueprint.V04Proof
open Yau Yau.Blueprint

variable {n q : ℕ} {X : KahlerManifold n}

theorem clockEstimates_of_original_inputs {d : VariationData X q} (hd : VariationSetup d)
    {k : ClockData X} (hk : ClockCutoffs d k) (hFiber : FiberWallError d k) (hBase : BaseWallError d k)
    {a : ℕ} (ha : 3 ≤ 4 * a) (hpa : k.fiberPower ≤ 4 * a)
    (hpc : k.fiberPower ≤ k.dampingPower) (hc : 0 < k.dampingPower)
    (hloc : LocalizationEstimates d) : ClockEstimates d k a := by
  obtain ⟨C, hC, hTaylor⟩ := ClockTaylorAux.clockEstimates_fifth hd hk hloc a
  refine ⟨C, hC, fun F hF => ?_⟩
  have hnormal := clockNormalization_losses_localized hd hk hloc a hF
  exact ⟨clockWeightRaw_loss_localized hd hk hloc a hF,
    hnormal.1, hnormal.2,
    clockWallEstimates hd hk hFiber hBase ha hpa hpc hc hloc F hF,
    hTaylor F hF⟩

end Yau.Blueprint.V04Proof
