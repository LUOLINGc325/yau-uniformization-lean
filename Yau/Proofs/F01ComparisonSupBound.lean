import Yau.Proofs.F01LogDetOrder
import Yau.Proofs.F01MetricRayleighPositive
import Yau.Proofs.F01LargestRayleighOrder
import Yau.Proofs.F01NativeLogDetEvolution
import Yau.Proofs.F01ComparisonTime
import Yau.Proofs.F01ClosedTimeBounds

/-! A bound for the actual logarithmic largest eigenvalue controls the
actual logdet, its time-integrated potential, and the same explicit Q.
This retains the small coefficient used to absorb a preliminary supremum. -/
noncomputable section
open Set
open scoped Matrix ComplexOrder
namespace Yau.NodeProofs.F01Aux
open Yau
variable {n : ℕ} {M : ComplexManifold n}

theorem flowLogDetRatio_le_log_largest (α : HermitianField M)
    (h : ℝ → HermitianField M) (x : M.Carrier) (t : ℝ) :
    flowLogDetRatio α h x t ≤ (n : ℝ) * Real.log (metricLargestRayleigh α (h t) x) := by
  have hα := Yau.LeafProofs.L12Aux.hMat_posDef α x (chartPt x x) (mem_extChartAt_target x)
  have hk := Yau.LeafProofs.L12Aux.hMat_posDef (h t) x (chartPt x x) (mem_extChartAt_target x)
  exact logdet_ratio_upper_of_order hα hk (metricLargestRayleigh_pos α (h t) x)
    (order_of_largestMatrixRayleigh_le hα hk le_rfl)

theorem comparisonFunction_bound_of_log_largest
    (α : HermitianField M) (h : ℝ → HermitianField M) (U : M.Carrier → ℝ → ℝ)
    (φ : M.Carrier → ℝ) {T D B Mφ : ℝ} (hT : 0 ≤ T) (hTD : T ≤ D)
    (hU0 : ∀ x, U x 0 = 0)
    (hpde : ∀ x s, s ∈ Icc 0 T →
      HasDerivWithinAt (U x) (flowLogDetRatio α h x s) (Icc 0 T) s)
    (hlog : ∀ x s, s ∈ Icc 0 T → Real.log (metricLargestRayleigh α (h s) x) ≤ B)
    (hφ : ∀ x, -Mφ ≤ φ x) (x : M.Carrier) {t : ℝ} (ht : t ∈ Icc 0 T) :
    comparisonFunction D n U (flowLogDetRatio α h) φ x t ≤
      (n : ℝ) * D * B + D * Mφ + (n : ℝ) * T := by
  have hP (y : M.Carrier) (s : ℝ) (hs : s ∈ Icc 0 T) :
      flowLogDetRatio α h y s ≤ (n : ℝ) * B :=
    (flowLogDetRatio_le_log_largest α h y s).trans
      (mul_le_mul_of_nonneg_left (hlog y s hs) (Nat.cast_nonneg n))
  have hUcap := linear_upper_of_closed_derivative_cap hT (hpde x) (hP x) t ht
  rw [hU0 x, zero_add] at hUcap
  have hD : 0 ≤ D := hT.trans hTD
  have hprod := mul_le_mul_of_nonneg_left (hP x t ht) (sub_nonneg.mpr (ht.2.trans hTD))
  have hweight := mul_le_mul_of_nonneg_left (hφ x) hD
  have htime := mul_le_mul_of_nonneg_left ht.2 (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  unfold comparisonFunction
  nlinarith

end Yau.NodeProofs.F01Aux
