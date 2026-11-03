import Yau.Blueprint.ConcreteExtensions
import Yau.Proofs.V04ChosenLocalization
import Yau.Proofs.V04FejerEstimates
import Yau.Proofs.V04FrequencySelection
import Yau.Proofs.V04NegativePartEstimates
import Yau.Proofs.V04SpectralCenter
import Yau.Proofs.V04ClockEstimates
import Yau.Proofs.V04BackwardClockRealization
import Yau.Proofs.V04PositiveReplacement
import Yau.Proofs.V04SymplecticSubmean

/-! The original nine conclusions use one clock, selected before the localization radius is enlarged. The same enlarged data supplies every subsequent analytic component. -/

open Filter
open scoped Topology
noncomputable section
namespace Yau.Blueprint.V04Proof
open Yau Yau.Blueprint

variable {n : ℕ} (X : KahlerManifold n)

theorem v04Contract : V04Contract X := by
  intro q d hd
  obtain ⟨C, hC, hFiber, hBase, B, hB, hdb, hk, hFiberB, hBaseB⟩ :=
    exists_chosen_clock_localization hd
  refine ⟨chosenClockData X C, hFiber, hBase, B, hB, hdb, hk, 4, le_rfl, ?_, ?_, ?_⟩
  · exact (chosenClockData_powers X C (le_refl 4)).1
  · exact (chosenClockData_powers X C (le_refl 4)).2
  intro a ha hdeform hsymbol hloc
  have hpa : (chosenClockData X C).fiberPower ≤ 4 * a := by
    have := (chosenClockData_powers X C ha).1
    omega
  have hpc : (chosenClockData X C).fiberPower ≤ (chosenClockData X C).dampingPower := by
    norm_num [chosenClockData]
  have hc : 0 < (chosenClockData X C).dampingPower := by norm_num [chosenClockData]
  have ha3 : 3 ≤ 4 * a := by omega
  exact ⟨fejerEstimates_of_symbolBounds hdb ha hsymbol,
    frequencySelection _,
    negativePartEstimates_of_original_inputs hdb ha hloc hsymbol hdeform,
    centerMajorants_of_symbolBounds hdb ha hloc hsymbol hdeform,
    spectralFactorEstimates_of_symbolBounds hdb ha hsymbol,
    clockEstimates_of_original_inputs hdb hk hFiberB hBaseB ha3 hpa hpc hc hloc,
    Filter.Eventually.of_forall (fun j => backwardClockRealization_of_cutoffs hdb hk j a),
    PositiveReplacementAux.positiveReplacement hdb hk ha hsymbol,
    SymplecticSubmeanAux.symplecticSubmean_of_original_inputs hdb hk a⟩

theorem v04 : Yau.Blueprint.V04 := fun _ X => v04Contract X

end Yau.Blueprint.V04Proof
