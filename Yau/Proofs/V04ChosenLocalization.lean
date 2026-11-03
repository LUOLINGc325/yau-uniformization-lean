import Yau.Proofs.V04WallErrorFiber
import Yau.Proofs.V04RadiusErrorTransport
import Yau.Proofs.V04ClockCutoffs

/-! One wall coefficient is fixed before enlarging the localization.
Both old and enlarged data use that same clock and coefficient. -/

open scoped Topology
noncomputable section
namespace Yau.Blueprint.V04Proof
open Yau Yau.Blueprint

variable {n q : ℕ} {X : KahlerManifold n}

theorem exists_chosen_clock_localization {d : VariationData X q} (hd : VariationSetup d) :
    ∃ C : ℕ → ℝ, (∀ j, 1 ≤ C j) ∧
      FiberWallError d (chosenClockData X C) ∧ BaseWallError d (chosenClockData X C) ∧
      ∃ B : ℕ → ℝ, (∀ j, d.B j ≤ B j) ∧
        VariationSetup {d with B := B} ∧ ClockCutoffs {d with B := B} (chosenClockData X C) ∧
        FiberWallError {d with B := B} (chosenClockData X C) ∧
        BaseWallError {d with B := B} (chosenClockData X C) := by
  obtain ⟨C, hC, hFiber, hBase⟩ := WallErrorAux.exists_chosen_wall_errors hd
  obtain ⟨B, hB, hdb, hk⟩ := exists_clock_cutoff_enlargement hd C hC
  exact ⟨C, hC, hFiber, hBase, B, hB, hdb, hk,
    fiberWallError_update_B hFiber B, baseWallError_update_B hBase B⟩

end Yau.Blueprint.V04Proof
