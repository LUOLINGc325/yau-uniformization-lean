import Yau.LeafProofs.L05PucciHarnackTransport

open Filter MeasureTheory Set
open scoped Topology ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05Aux
open Yau.Parabolic

theorem harnack_tracePair_smul_left {n : ℕ} (A H : Sym n) (q : ℝ) :
    tracePair (q • A) H=q*tracePair A H := by
  simp only [tracePair,selfAdjoint.val_smul,Matrix.smul_mul,Matrix.trace_smul,smul_eq_mul]

theorem harnack_slope_smul_mem {n : ℕ} {ell L q : ℝ} (hq : 0 ≤ q)
    {A : Sym n} (hA : A ∈ slopeSet n ell L) : q • A ∈ slopeSet n (q*ell) (q*L) := by
  constructor
  · have h := hA.1.smul hq
    simpa only [selfAdjoint.val_smul,smul_sub,smul_smul] using h
  · have h := hA.2.smul hq
    simpa only [selfAdjoint.val_smul,smul_sub,smul_smul] using h

theorem harnack_slope_inv_mem {n : ℕ} {ell L q : ℝ} (hq : 0 < q)
    {A : Sym n} (hA : A ∈ slopeSet n (q*ell) (q*L)) : q⁻¹ • A ∈ slopeSet n ell L := by
  have h := harnack_slope_smul_mem (inv_nonneg.mpr hq.le) hA
  simpa only [← mul_assoc,inv_mul_cancel₀ hq.ne',one_mul] using h

theorem harnack_plus_scale_constants_le {n : ℕ} {ell L q : ℝ}
    (hell : 0 ≤ ell) (hL : ell ≤ L) (hq : 0 < q) (H : Sym n) :
    pucciPlus (q*ell) (q*L) H ≤ q*pucciPlus ell L H := by
  apply pucciPlus_le (mul_le_mul_of_nonneg_left hL hq.le)
  intro A hA
  have hInv := harnack_slope_inv_mem hq hA
  have hBound := tracePair_le_pucciPlus hell hInv H
  rw [harnack_tracePair_smul_left] at hBound
  have hMul := mul_le_mul_of_nonneg_left hBound hq.le
  simpa only [← mul_assoc,mul_inv_cancel₀ hq.ne',one_mul] using hMul

theorem harnack_plus_scale_constants {n : ℕ} {ell L q : ℝ}
    (hell : 0 ≤ ell) (hL : ell ≤ L) (hq : 0 < q) (H : Sym n) :
    pucciPlus (q*ell) (q*L) H=q*pucciPlus ell L H := by
  have hInv := harnack_plus_scale_constants_le (mul_nonneg hq.le hell)
    (mul_le_mul_of_nonneg_left hL hq.le) (inv_pos.mpr hq) H
  simp only [← mul_assoc,inv_mul_cancel₀ hq.ne',one_mul] at hInv
  have hMul := mul_le_mul_of_nonneg_left hInv hq.le
  rw [← mul_assoc,mul_inv_cancel₀ hq.ne',one_mul] at hMul
  exact le_antisymm (harnack_plus_scale_constants_le hell hL hq H) hMul

theorem harnack_minus_scale_constants {n : ℕ} {ell L q : ℝ}
    (hell : 0 ≤ ell) (hL : ell ≤ L) (hq : 0 < q) (H : Sym n) :
    harnackPucciMinus (q*ell) (q*L) H=q*harnackPucciMinus ell L H := by
  unfold harnackPucciMinus
  rw [harnack_plus_scale_constants hell hL hq]
  ring

end Yau.LeafProofs.L05Aux
