import Yau.Blueprint.VariationContracts

/-! The coefficient chosen before radius enlargement controls the same
local wall problem for every new radius. No coefficient is reselected. -/

open scoped Topology
noncomputable section
namespace Yau.Blueprint.V04Proof
open Yau Yau.Blueprint

variable {n q : ℕ} {X : KahlerManifold n}

theorem baseWallError_update_B {d : VariationData X q} {k : ClockData X}
    (h : BaseWallError d k) (B : ℕ → ℝ) : BaseWallError {d with B := B} k := by
  obtain ⟨C, hC, hbound⟩ := h
  refine ⟨C, hC, fun j x t ht hx => ?_⟩
  change |laplacian (d.h t) (wallBase d j) x| ≤
    C * Real.exp (d.rho x t) * (deltaBase d j x ^ 3)⁻¹ *
      (if clockBaseCutoff d k j x = 1 then 1 else 0)
  exact hbound j x t ht hx

theorem fiberWallError_update_B {d : VariationData X q} {k : ClockData X}
    (h : FiberWallError d k) (B : ℕ → ℝ) : FiberWallError {d with B := B} k := by
  intro j b hb
  dsimp only
  intro y hy t ht s hs
  have hy' : y ∈ boundaryRegion {d with B := Function.update d.B j b} j := by
    simpa only [boundaryRegion, Function.update_self] using hy
  have hbound := h j b hb y hy' t ht s hs
  simpa only [spatialBoundaryHessianAt, wallCost, baseCost, wallFiber, deltaFiber,
    wallBase, deltaBase, wallProduct, clockFiberCutoff, Function.update_self] using hbound

end Yau.Blueprint.V04Proof
