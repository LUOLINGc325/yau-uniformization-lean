import Yau.Proofs.F03DirichletEulerConvergence

/-! Contractive restriction from the actual complex L2 operators to real data. -/
noncomputable section
open MeasureTheory
open scoped Topology InnerProductSpace
namespace Yau.Proofs.F03Aux
open Yau LeafProofs.L19Aux
set_option maxHeartbeats 1000000

theorem heatLpRe_norm_le {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (f : Lp ℂ 2 μ) : ‖heatLpRe μ f‖ ≤ ‖f‖ := by
  have hsplit := heatLp_norm_sq μ f
  nlinarith only [hsplit,sq_nonneg ‖heatLpIm μ f‖,norm_nonneg (heatLpRe μ f),norm_nonneg f]

theorem heatRealRestrictionCLM_norm_le {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (A : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) : ‖heatRealRestrictionCLM μ A‖ ≤ ‖A‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg A)
  intro f
  change ‖heatLpRe μ (A (heatLpOfReal μ f))‖ ≤ ‖A‖*‖f‖
  exact (heatLpRe_norm_le μ _).trans ((A.le_opNorm _).trans_eq (by rw [heatLpOfReal_norm]))

end Yau.Proofs.F03Aux
