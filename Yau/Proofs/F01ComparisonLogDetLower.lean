import Yau.Proofs.F01ComparisonSupBound
import Yau.Proofs.F01MetricComparisonScalarBounds

/-! The actual nonnegative comparison Q and the actual metric upper
order give two-sided scalar bounds on a half-size time slab. -/
noncomputable section
open Set
open scoped Matrix ComplexOrder
namespace Yau.NodeProofs.F01Aux
open Yau
variable {n : ℕ} {M : ComplexManifold n}

theorem logdet_lower_of_nonnegative_comparison
    (α : HermitianField M) (h : ℝ → HermitianField M) (U : M.Carrier → ℝ → ℝ)
    (φ : M.Carrier → ℝ) {T D B Mφ : ℝ}
    (hT : 0 ≤ T) (hD : 0 < D) (hhalf : 2 * T ≤ D)
    (hB : 0 ≤ B) (hMφ : 0 ≤ Mφ)
    (hU0 : ∀ x, U x 0 = 0)
    (hpde : ∀ x s, s ∈ Icc 0 T →
      HasDerivWithinAt (U x) (flowLogDetRatio α h x s) (Icc 0 T) s)
    (horder : ∀ x s, s ∈ Icc 0 T →
      ((Real.exp B : ℂ) • gMat α x - gMat (h s) x).PosSemidef)
    (hφ : ∀ x, -Mφ ≤ φ x)
    (hQ : ∀ x s, s ∈ Icc 0 T →
      0 ≤ comparisonFunction D n U (flowLogDetRatio α h) φ x s) :
    ∀ x t, t ∈ Icc 0 T →
      -(2 * Mφ + (n : ℝ) * B + n) ≤ flowLogDetRatio α h x t := by
  have hPcap (x : M.Carrier) (s : ℝ) (hs : s ∈ Icc 0 T) :
      flowLogDetRatio α h x s ≤ (n : ℝ) * B :=
    logdet_ratio_upper_of_exp_order
      (Yau.LeafProofs.L12Aux.hMat_posDef α x (chartPt x x) (mem_extChartAt_target x))
      (Yau.LeafProofs.L12Aux.hMat_posDef (h s) x (chartPt x x) (mem_extChartAt_target x))
      (horder x s hs)
  intro x t ht
  have hUcap := linear_upper_of_closed_derivative_cap hT (hpde x) (hPcap x) t ht
  rw [hU0 x, zero_add] at hUcap
  have hgap : 0 ≤ D - 2 * t := by linarith [ht.2]
  have hdt : 0 < D - t := by linarith
  have hweight := mul_le_mul_of_nonneg_left (hφ x) hD.le
  have hnonneg := hQ x t ht
  unfold comparisonFunction at hnonneg
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hnB : 0 ≤ (n : ℝ) * B := mul_nonneg hn hB
  have hnum : (n : ℝ) * B * t + D * Mφ + n * t ≤
      (2 * Mφ + (n : ℝ) * B + n) * (D - t) := by
    nlinarith [mul_nonneg hMφ hgap, mul_nonneg hnB hgap, mul_nonneg hn hgap]
  have hprod : 0 ≤ (D - t) *
      (flowLogDetRatio α h x t + (2 * Mφ + (n : ℝ) * B + n)) := by
    nlinarith
  have hsum := nonneg_of_mul_nonneg_right hprod hdt
  linarith

theorem scalar_abs_bounds_of_nonnegative_comparison
    (α : HermitianField M) (h : ℝ → HermitianField M) (U : M.Carrier → ℝ → ℝ)
    (φ : M.Carrier → ℝ) {T D B Mφ : ℝ}
    (hT : 0 ≤ T) (hD : 0 < D) (hhalf : 2 * T ≤ D)
    (hB : 0 ≤ B) (hMφ : 0 ≤ Mφ)
    (hU0 : ∀ x, U x 0 = 0)
    (hpde : ∀ x s, s ∈ Icc 0 T →
      HasDerivWithinAt (U x) (flowLogDetRatio α h x s) (Icc 0 T) s)
    (horder : ∀ x s, s ∈ Icc 0 T →
      ((Real.exp B : ℂ) • gMat α x - gMat (h s) x).PosSemidef)
    (hφ : ∀ x, -Mφ ≤ φ x)
    (hQ : ∀ x s, s ∈ Icc 0 T →
      0 ≤ comparisonFunction D n U (flowLogDetRatio α h) φ x s) :
    ∀ x t, t ∈ Icc 0 T →
      |flowLogDetRatio α h x t| ≤ 2 * Mφ + (n : ℝ) * B + n ∧
      |U x t| ≤ (2 * Mφ + (n : ℝ) * B + n) * t := by
  have hlo := logdet_lower_of_nonnegative_comparison α h U φ hT hD hhalf hB hMφ
    hU0 hpde horder hφ hQ
  have habs (x : M.Carrier) (s : ℝ) (hs : s ∈ Icc 0 T) :
      |flowLogDetRatio α h x s| ≤ 2 * Mφ + (n : ℝ) * B + n := by
    apply abs_le.mpr
    refine ⟨hlo x s hs, ?_⟩
    have hhi := logdet_ratio_upper_of_exp_order
      (Yau.LeafProofs.L12Aux.hMat_posDef α x (chartPt x x) (mem_extChartAt_target x))
      (Yau.LeafProofs.L12Aux.hMat_posDef (h s) x (chartPt x x) (mem_extChartAt_target x))
      (horder x s hs)
    change flowLogDetRatio α h x s ≤ (n : ℝ) * B at hhi
    linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  intro x t ht
  exact ⟨habs x t ht,
    closed_potential_abs_bound_of_time_value hT (hU0 x) (hpde x) (habs x) t ht⟩

end Yau.NodeProofs.F01Aux
