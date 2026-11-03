import Yau.Proofs.F01ShiftedNativePotential
import Yau.Proofs.F01NormalizedPotentialSup

/-! The original scalar time equation and metric comparison give the
actual positive-time potential supremum. Its fixed-horizon budget does
not use derivatives inferred from qualitative smoothness. -/
noncomputable section
open Set Metric
open scoped Matrix ComplexOrder
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic Yau.LeafProofs.L17Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem potential_sup_from_metric_sandwich
    (g : HermitianField M) (h : ℝ → HermitianField M) (U : M.Carrier → ℝ → ℝ)
    {T C : ℝ} (hT : 0 ≤ T) (hC : 1 ≤ C) (hU0 : ∀ x, U x 0 = 0)
    (hJet : ∀ x s, s ∈ Icc 0 T → HasDerivWithinAt (U x)
      (flowLogDetRatio g h x s) (Icc 0 T) s)
    (hflow : ∀ x s, s ∈ Icc 0 T →
      (gMat (h s) x - ((C⁻¹ : ℝ) : ℂ) • gMat g x).PosSemidef ∧
      ((C : ℂ) • gMat g x - gMat (h s) x).PosSemidef) :
    ∀ x t, t ∈ Icc 0 T → |U x t| ≤ ((n : ℝ) * Real.log C) * t := by
  intro x
  apply closed_potential_abs_bound_of_time_value hT (hU0 x) (hJet x)
  intro t ht
  exact logdet_ratio_abs_bound_of_sandwich
    (Yau.LeafProofs.L12Aux.hMat_posDef g x (chartPt x x) (mem_extChartAt_target x))
    (Yau.LeafProofs.L12Aux.hMat_posDef (h t) x (chartPt x x) (mem_extChartAt_target x))
    hC (hflow x t ht).1 (hflow x t ht).2

theorem shifted_native_potential_sup
    (g : HermitianField M) (A : BoundedChartFamily g)
    (h : ℝ → HermitianField M) (U : M.Carrier → ℝ → ℝ) {T Tcap C ρ τ : ℝ}
    (hC : 1 ≤ C) (hLower : ρ ^ 2 ≤ τ) (hUpper : τ + ρ ^ 2 ≤ T) (hCap : T ≤ Tcap)
    (hU0 : ∀ x, U x 0 = 0)
    (hJet : ∀ x s, s ∈ Icc 0 T → HasDerivWithinAt (U x)
      (flowLogDetRatio g h x s) (Icc 0 T) s)
    (hflow : ∀ x s, s ∈ Icc 0 T →
      (gMat (h s) x - ((C⁻¹ : ℝ) : ℂ) • gMat g x).PosSemidef ∧
      ((C : ℂ) • gMat g x - gMat (h s) x).PosSemidef) (a : M.Carrier) :
    ∀ p ∈ cylinder (ball 0 1) (-1) 1,
      |shiftedNativePotential A U a ρ τ p| ≤ (ρ ^ 2)⁻¹ * (((n : ℝ) * Real.log C) * Tcap) := by
  have hT : 0 ≤ T := by nlinarith [sq_nonneg ρ]
  have hA : 0 ≤ (n : ℝ) * Real.log C := mul_nonneg (Nat.cast_nonneg n) (Real.log_nonneg hC)
  intro p hp
  have ht := shifted_clock_maps hLower hUpper hp.2
  have hu := potential_sup_from_metric_sandwich g h U hT hC hU0 hJet hflow
    (A.chart a (affineParabolicPoint ρ 0 τ p).1) (affineParabolicPoint ρ 0 τ p).2 ht
  have hBound := hu.trans (mul_le_mul_of_nonneg_left (ht.2.trans hCap) hA)
  dsimp only [shiftedNativePotential, affineParabolicPotential, affineParabolicPullback]
  rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr (sq_nonneg ρ))]
  exact mul_le_mul_of_nonneg_left hBound (inv_nonneg.mpr (sq_nonneg ρ))

end Yau.NodeProofs.F01Aux
