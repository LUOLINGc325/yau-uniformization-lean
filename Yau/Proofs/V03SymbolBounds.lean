import Yau.Proofs.V03SymbolTraceBound
import Yau.Proofs.V03EnergyTraceBounds
import Yau.Proofs.V03SymbolOpNorm

/-! The FULL original SymbolBounds clause. One constant precedes every
admissible disc and normalized frame and controls the actual computed
energy, including its logarithmic wall summand. -/

open scoped Topology ContDiff

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

theorem symbolBounds {n q : ℕ} {X : KahlerManifold n} {d : VariationData X q}
    (hd : VariationSetup d) (a : ℕ) (ha : 4 ≤ a) : SymbolBounds d a := by
  intro j
  obtain ⟨M, hM, hOp⟩ := boundarySymbol_uniform_opNorm hd j a ha
  obtain ⟨C, hC, hTr⟩ := boundarySymbol_uniform_trace_bound hd j a ha
  let N : ℝ := C * (3 * (2 * Real.pi)⁻¹)
  have hN : 0 ≤ N := by dsimp only [N]; positivity
  refine ⟨M + N, add_nonneg hM hN, fun F E hF hE => ⟨?_, ?_⟩⟩
  · intro θ
    obtain ⟨hHerm, hNorm⟩ := hOp F E hF hE θ
    exact ⟨hHerm, hNorm.trans (le_add_of_nonneg_right hN)⟩
  calc
    _ ≤ ENNReal.ofReal C *
        (matrixDSq (fun θ => ambientFrame d.G F.f E (circlePoint θ)) +
          boundaryDSq (fun θ b => d.G (F.f (circlePoint θ)) b) +
            boundaryDSq (fun θ (_ : Unit) => F.w (circlePoint θ))) := hTr F E hF hE
    _ ≤ ENNReal.ofReal C * (ENNReal.ofReal (3 * (2 * Real.pi)⁻¹) * variationEnergy d j F) := by
      gcongr
      exact admissible_three_traces_le_energy hd j hF hE
    _ = ENNReal.ofReal N * variationEnergy d j F := by
      rw [ENNReal.ofReal_mul hC]
      exact (mul_assoc _ _ _).symm
    _ ≤ ENNReal.ofReal (M + N) * (1 + variationEnergy d j F) := by
      gcongr
      · exact le_add_of_nonneg_left hM
      · exact le_add_of_nonneg_left zero_le_one

end Yau.Blueprint.V03Proof
