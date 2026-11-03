import Yau.Proofs.Y06VolumeInverse
import Yau.Proofs.Y06SizeAlgebra
import Yau.Proofs.Y01ChangeBounds

/-! Fixed realization and finite triangular inversion preserve a uniform
exponential bound in the square-root clock. No continuity of choices is needed. -/

noncomputable section

namespace Yau.Proofs.Y06Aux

open Yau.Blueprint Yau.Blueprint.Alignment Yau.Proofs.Y02Aux
open Yau.Blueprint.Alignment.Y03Proof

variable {n d : ℕ}

theorem constant_exp_bound {K x : ℝ} (hK : 0 ≤ K) (hx : 1 ≤ x) : K ≤ Real.exp (K * x) := by
  have h := Real.add_one_le_exp K
  exact (by linarith : K ≤ Real.exp K).trans
    (Real.exp_le_exp.mpr (le_mul_of_one_le_right hK hx))

theorem realization_inverse_envelope {H I : PolyMap n} {C E x : ℝ}
    (hE : 0 ≤ E) (hx : 1 ≤ x) (hH : H.linearPart = 1)
    (hsize : polySize H ≤ Real.exp (E * x))
    (hI : I.coeffNorm ≤ C * (1 + H.coeffNorm + matOpNorm H.linearPart⁻¹) ^ C) :
    I.coeffNorm ≤ Real.exp ((|C| + |C| * (E + 1)) * x) := by
  let B := 1 + H.coeffNorm + matOpNorm H.linearPart⁻¹
  have hB1 : 1 ≤ B := by
    dsimp [B]
    linarith [coeffNorm_nonneg H, (show 0 ≤ matOpNorm H.linearPart⁻¹ from norm_nonneg _)]
  have hB : B ≤ Real.exp ((E + 1) * x) := by
    have hunit : matOpNorm H.linearPart⁻¹ ≤ 1 := by rw [hH, inv_one]; exact matOpNorm_one_le
    have hble : B ≤ 1 + polySize H := by dsimp [B, polySize]; linarith
    exact hble.trans ((add_le_add (le_refl 1) hsize).trans
      (by simpa only [max_eq_right hE] using one_add_exp_enlarge (A := E) hx))
  have hpower : B ^ C ≤ Real.exp ((|C| * (E + 1)) * x) := by
    apply (Real.rpow_le_rpow_of_exponent_le hB1 (le_abs_self C)).trans
    have h := Real.rpow_le_rpow (by linarith : 0 ≤ B) hB (abs_nonneg C)
    rw [← Real.exp_mul] at h
    convert h using 1 <;> congr 1 <;> ring
  have hC := constant_exp_bound (abs_nonneg C) hx
  apply hI.trans
  calc
    _ ≤ |C| * B ^ C := mul_le_mul_of_nonneg_right (le_abs_self C) (Real.rpow_nonneg (by linarith : 0 ≤ B) C)
    _ ≤ Real.exp (|C| * x) * Real.exp ((|C| * (E + 1)) * x) :=
      mul_le_mul hC hpower (Real.rpow_nonneg (by linarith : 0 ≤ B) C) (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem triangular_inverse_envelope (P : PolyMap n) (a : Fin n → ℂ) (hd : 1 ≤ d)
    (hdegree : P.degree ≤ d) {E A x : ℝ} (hx : 1 ≤ x)
    (hP : polySize P ≤ Real.exp (E * x))
    (hI : polySize (linearPolynomial (Matrix.diagonal (fun i => (a i)⁻¹))) ≤ Real.exp (A * x)) :
    (triangularInverseApprox P a n).coeffNorm ≤
      Real.exp (((triangularInverseExponent d n : ℝ) * ((n + 2 : ℝ) + 2 * E + A)) * x) := by
  let U := polySize P
  let V := polySize (linearPolynomial (Matrix.diagonal (fun i => (a i)⁻¹)))
  let T := (n + 2 : ℝ) * U ^ 2 * V
  have hU : 1 ≤ U := polySize_one_le P
  have hV : 1 ≤ V := polySize_one_le _
  have hn : (2 : ℝ) ≤ n + 2 := by have := Nat.cast_nonneg (α := ℝ) n; linarith
  have hUU : 1 ≤ U ^ 2 := one_le_pow₀ hU
  have hTU : 2 * U ≤ T := by
    have hUsq : U ≤ U ^ 2 := by nlinarith
    calc
      _ ≤ (n + 2 : ℝ) * U ^ 2 := mul_le_mul hn hUsq (by linarith) (by positivity)
      _ ≤ _ := le_mul_of_one_le_right (by positivity) hV
  have hTV : V ≤ T := by
    have hco : 1 ≤ (n + 2 : ℝ) * U ^ 2 := one_le_mul_of_one_le_of_one_le (by linarith) hUU
    exact le_mul_of_one_le_left (by linarith) hco
  have hTN : (n : ℝ) ≤ T := by
    have hco : (n + 2 : ℝ) ≤ T :=
      (le_mul_of_one_le_right (by positivity : 0 ≤ (n + 2 : ℝ)) hUU).trans
        (le_mul_of_one_le_right (by positivity) hV)
    linarith
  have hN : (nonlinearPart P).coeffNorm ≤ T := by
    have hlin := linearPoly_linearPart_coeffNorm_le P
    change (linearPolynomial P.linearPart).coeffNorm ≤ P.coeffNorm at hlin
    have hnorm := coeffNorm_sub_le P (linearPolynomial P.linearPart)
    have : (nonlinearPart P).coeffNorm ≤ 2 * U := by
      dsimp [nonlinearPart, U, polySize] at *
      linarith
    exact this.trans hTU
  have hT : 2 ≤ T := (by nlinarith : (2 : ℝ) ≤ 2 * U).trans hTU
  have hInv : (linearPolynomial (Matrix.diagonal (fun i => (a i)⁻¹))).coeffNorm ≤ T := by
    have : (linearPolynomial (Matrix.diagonal (fun i => (a i)⁻¹))).coeffNorm ≤ V := by
      dsimp [V, polySize]; linarith
    exact this.trans hTV
  have hTbound : T ≤ Real.exp (((n + 2 : ℝ) + 2 * E + A) * x) := by
    have hconstant := constant_exp_bound (by positivity : (0 : ℝ) ≤ n + 2) hx
    have hpow := pow_le_pow_left₀ (by linarith : 0 ≤ U) hP 2
    have hproduct := mul_le_mul (mul_le_mul hconstant hpow (by positivity) (Real.exp_pos _).le)
      hI (by linarith : 0 ≤ V) (by positivity)
    convert hproduct using 1 <;> rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add] <;> congr 1 <;> ring
  have hraw := triangularInverseApprox_coeffNorm P a hdegree hd hT hTN hN hInv n
  apply hraw.trans
  have hpow := pow_le_pow_left₀ (by linarith : 0 ≤ T) hTbound (triangularInverseExponent d n)
  rw [← Real.exp_nat_mul] at hpow
  convert hpow using 1 <;> congr 1 <;> ring

end Yau.Proofs.Y06Aux
