import Yau.Proofs.V04WallErrorBaseHessian
import Yau.Proofs.V04WallErrorFlowTrace
import Yau.Proofs.V04WallErrorPlateau

/-! The original base-wall estimate with a single constant for all wall
indices, and with the indicator supplied by the actual cutoff plateau. -/

open scoped Manifold Topology ContDiff Matrix ComplexOrder
noncomputable section
namespace Yau.Blueprint.V04Proof.WallErrorAux
open Yau Yau.Blueprint V03Proof
open Yau.Proofs.F02Aux

variable {n q : ℕ} {X : KahlerManifold n}

theorem baseWallError_chosenClockData {d : VariationData X q} (hd : VariationSetup d)
    (Ccoeff : ℕ → ℝ) : BaseWallError d (chosenClockData X Ccoeff) := by
  obtain ⟨C, hC, hEx⟩ := hd.2.2.2.1.2.2.2
  obtain ⟨M, hM, hDer⟩ := profile_two_derivatives_bound (setup_wallProfiles hd).1
  let K := M * C + (2 * M ^ 2 + M) * (2 * C ^ 2)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨K * n, by positivity, fun j x t ht hx => ?_⟩
  by_cases hcut : clockBaseCutoff d (chosenClockData X Ccoeff) j x = 1
  · rw [if_pos hcut, mul_one]
    have hux : 1 ≤ d.u x := hd.2.2.2.1.2.2.1 x
    have hA : 0 < d.A j := zero_lt_one.trans_le (hux.trans hx.le)
    have hδ : 0 < deltaBase d j x :=
      ((setup_wallProfiles hd).2.2.1 (d.u x / d.A j)).2.2.1.mpr ((div_lt_one hA).2 hx)
    have hw : 0 ≤ (deltaBase d j x ^ 3)⁻¹ := by positivity
    have hG := gMat_posDef X.metric.form x
    have hH := gMat_posDef (d.h t) x
    have hround : chartInv x (chartPt x x) = x :=
      (extChartAt (ComplexModel n) x).left_inv (mem_extChartAt_source x)
    have hDelta : ContDiffAt ℝ ∞ (inChart x (deltaBase d j)) (chartPt x x) :=
      (((setup_wallProfiles hd).1.comp_contDiffOn ((hd.2.2.2.1.1 x).div_const (d.A j))).contDiffAt
        ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds
          (mem_extChartAt_target x)))
    have hDeltaNe : inChart x (deltaBase d j) (chartPt x x) ≠ 0 := by
      simpa only [inChart, hround] using hδ.ne'
    have hWall : ContDiffAt ℝ 2 (inChart x (wallBase d j)) (chartPt x x) :=
      ((hDelta.inv hDeltaNe).sub contDiffAt_const).of_le (by simp)
    have hWH : (levi (wallBase d j) x).IsHermitian := leviMatrix_isHermitian hWall stdVec
    have hBound := baseWall_direction_abs_bound hd hC hEx hM hDer j x hx
    have hHigh : HermLE (levi (wallBase d j) x)
        (((K * (deltaBase d j x ^ 3)⁻¹ : ℝ) : ℂ) • gMat X.metric.form x) := by
      apply hermLE_of_direction_le hWH (hG.isHermitian.smul (by simp [IsSelfAdjoint]))
      intro v
      rw [leviDirection_real_smul]
      exact (le_abs_self _).trans (hBound v)
    have hLow : HermLE (((-(K * (deltaBase d j x ^ 3)⁻¹) : ℝ) : ℂ) • gMat X.metric.form x)
        (levi (wallBase d j) x) := by
      apply hermLE_of_direction_le (hG.isHermitian.smul (by simp [IsSelfAdjoint])) hWH
      intro v
      rw [leviDirection_real_smul]
      have hb := (abs_le.mp (hBound v)).1
      simpa only [neg_mul] using hb
    have hlo := traceWith_mono _ _ _ hH.posSemidef hLow
    have hhi := traceWith_mono _ _ _ hH.posSemidef hHigh
    rw [traceWith_real_smul] at hlo hhi
    have hAbs : |laplacian (d.h t) (wallBase d j) x| ≤
        K * (deltaBase d j x ^ 3)⁻¹ * traceWith (gMat (d.h t) x) (gMat X.metric.form x) := by
      apply abs_le.mpr
      constructor
      · simpa only [laplacian, neg_mul] using hlo
      · exact hhi
    calc
      |laplacian (d.h t) (wallBase d j) x| ≤
          K * (deltaBase d j x ^ 3)⁻¹ * traceWith (gMat (d.h t) x) (gMat X.metric.form x) := hAbs
      _ ≤ K * (deltaBase d j x ^ 3)⁻¹ * (n * Real.exp (d.rho x t)) :=
        mul_le_mul_of_nonneg_left (initialMetric_traceWith_le_exp_rho hd x ht.1)
          (mul_nonneg hK hw)
      _ = _ := by ring
  · rw [baseWall_laplacian_eq_zero_of_cutoff_ne_one hd Ccoeff j x (d.h t) hcut,
      abs_zero, if_neg hcut, mul_zero]

end Yau.Blueprint.V04Proof.WallErrorAux
