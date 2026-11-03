import Yau.Proofs.Y01SequenceEnvelopes
import Yau.Proofs.Y01VolumeBounds

/-! The original coherent-volume output has uniform sqrt-clock bounds,
including V itself, whose bound is derived from its actual transition germ. -/

noncomputable section

namespace Yau.Proofs.Y01Aux

open Yau.Blueprint Yau.Blueprint.Alignment Yau.Proofs.Y02Aux
open scoped ContDiff

variable {n d : ℕ}

theorem coherent_volume_sqrt_bounds
    {F : ℝ → ℝ → ComplexVector n → ComplexVector n} {tk s : ℕ → ℝ}
    {r hm BF : ℝ} {last : Fin n} {logs : ℕ → ComplexVector n → ℂ}
    {B : ℕ → ℕ → MvPolynomial (Fin n) ℂ} {ell E : ℕ → MvPolynomial (Fin n) ℂ}
    {A Ainv V : ℕ → PolyMap n}
    (hVol : CoherentVolume F tk s d r last logs B ell E A Ainv V)
    (hs : ∀ k, 1 ≤ s k)
    (hstep : ∀ k, s (k + 1) - s k ≤ (Real.exp hm - 1) * s k)
    (hBF : 0 ≤ BF)
    (hF : ∀ k, ContDiffAt ℂ d (F (tk k) (tk (k + 1))) 0)
    (hF0 : ∀ k, F (tk k) (tk (k + 1)) 0 = 0)
    (hFnorm : ∀ k, jetNorm (F (tk k) (tk (k + 1))) d ≤ BF) :
    ∃ Cv : ℝ, 0 ≤ Cv ∧ ∀ k,
      (A k).coeffNorm ≤ Real.exp (Cv * Real.sqrt (s k)) ∧
      (Ainv k).coeffNorm ≤ Real.exp (Cv * Real.sqrt (s k)) ∧
      (V k).coeffNorm ≤ Real.exp (Cv * Real.sqrt (s k)) := by
  obtain ⟨C, hC, hbound⟩ := hVol.2.2.2.2
  have hA k : (A k).coeffNorm ≤ (1 + s k) ^ C := by
    have hell : 0 ≤ ∑ β ∈ (ell k).support, ‖(ell k).coeff β‖ :=
      Finset.sum_nonneg (fun β hβ => norm_nonneg _)
    have hb := hbound k
    rw [abs_of_nonneg (by linarith [hs k] : 0 ≤ s k)] at hb
    linarith [coeffNorm_nonneg (Ainv k)]
  have hI k : (Ainv k).coeffNorm ≤ (1 + s k) ^ C := by
    have hell : 0 ≤ ∑ β ∈ (ell k).support, ‖(ell k).coeff β‖ :=
      Finset.sum_nonneg (fun β hβ => norm_nonneg _)
    have hb := hbound k
    rw [abs_of_nonneg (by linarith [hs k] : 0 ≤ s k)] at hb
    linarith [coeffNorm_nonneg (A k)]
  let CA := 4 * |C|
  have hCA : 0 ≤ CA := by dsimp [CA]; positivity
  have hAexp k : (A k).coeffNorm ≤ Real.exp (CA * Real.sqrt (s k)) :=
    (hA k).trans (polynomial_le_sqrt_envelope (hs k))
  have hIexp k : (Ainv k).coeffNorm ≤ Real.exp (CA * Real.sqrt (s k)) :=
    (hI k).trans (polynomial_le_sqrt_envelope (hs k))
  have hNext : ∃ Cn : ℝ, 0 ≤ Cn ∧ ∀ k,
      (A (k + 1)).coeffNorm ≤ Real.exp (Cn * Real.sqrt (s k)) := by
    refine ⟨CA * Real.sqrt (Real.exp hm), by positivity, ?_⟩
    intro k
    exact next_sqrt_envelope hCA (by linarith [hs k]) (hstep k) (hAexp (k + 1))
  let cj := cauchyJetConstant d
  let pj := partitionJetConstant d
  let ej := (n : ℝ) * ((boundedMonomials n d).card : ℝ)
  have hcj : 0 ≤ cj := cauchyJetConstant_nonneg d
  have hpj : 0 ≤ pj := partitionJetConstant_nonneg d
  have hej : 0 ≤ ej := by dsimp [ej]; positivity
  have hConst (K : ℝ) : ∃ Ck : ℝ, 0 ≤ Ck ∧ ∀ k,
      K ≤ Real.exp (Ck * Real.sqrt (s k)) :=
    exists_constant_sqrt_envelope hs (fun _ => le_rfl)
  have hCI : ∃ Ck : ℝ, 0 ≤ Ck ∧ ∀ k,
      cj * (Ainv k).coeffNorm ≤ Real.exp (Ck * Real.sqrt (s k)) :=
    exists_mul_sqrt_envelope (fun _ => hcj) (fun k => coeffNorm_nonneg (Ainv k))
      (hConst cj) ⟨CA, hCA, hIexp⟩
  have hOneCI := exists_sum_sqrt_envelope hs (hConst 1) hCI
  have hOneCI0 k : 0 ≤ 1 + cj * (Ainv k).coeffNorm :=
    add_nonneg zero_le_one (mul_nonneg hcj (coeffNorm_nonneg _))
  have hPowCI0 k : 0 ≤ (1 + cj * (Ainv k).coeffNorm) ^ d := pow_nonneg (hOneCI0 k) d
  have hOneInner0 k : 0 ≤ 1 + pj * BF * (1 + cj * (Ainv k).coeffNorm) ^ d :=
    add_nonneg zero_le_one (mul_nonneg (mul_nonneg hpj hBF) (hPowCI0 k))
  have hPowInner0 k : 0 ≤ (1 + pj * BF * (1 + cj * (Ainv k).coeffNorm) ^ d) ^ d :=
    pow_nonneg (hOneInner0 k) d
  have hCN0 k : 0 ≤ cj * (A (k + 1)).coeffNorm := mul_nonneg hcj (coeffNorm_nonneg _)
  have hPowCI := exists_pow_sqrt_envelope
    hOneCI0 hOneCI d
  have hInner := exists_mul_sqrt_envelope (fun _ => mul_nonneg hpj hBF)
    hPowCI0
    (hConst (pj * BF)) hPowCI
  have hOneInner := exists_sum_sqrt_envelope hs (hConst 1) hInner
  have hPowInner := exists_pow_sqrt_envelope
    hOneInner0
    hOneInner d
  have hCN := exists_mul_sqrt_envelope (fun _ => hcj)
    (fun k => coeffNorm_nonneg (A (k + 1))) (hConst cj) hNext
  have hProduct := exists_mul_sqrt_envelope
    (fun k => mul_nonneg hcj (coeffNorm_nonneg _))
    hPowInner0
    hCN hPowInner
  obtain ⟨CV, hCV, hVexp⟩ := exists_mul_sqrt_envelope (fun _ => mul_nonneg hej hpj)
    (fun k => mul_nonneg (hCN0 k) (hPowInner0 k))
    (hConst (ej * pj)) hProduct
  let Cv := max CA CV
  have hCv : 0 ≤ Cv := hCA.trans (le_max_left _ _)
  refine ⟨Cv, hCv, ?_⟩
  intro k
  have heA := Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right (le_max_left CA CV) (Real.sqrt_nonneg (s k)))
  have heV := Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right (le_max_right CA CV) (Real.sqrt_nonneg (s k)))
  refine ⟨(hAexp k).trans heA, (hIexp k).trans heA, ?_⟩
  obtain ⟨hellDegree, hellZero, hellSum, hellJet, hEDegree, hEJet, hAdef, hAzero, hAizero,
    hAlinear, hADegree, hAiDegree, hAleft, hAright, hVDegree, hVconst, hVjet⟩ := hVol.2.2.2.1 k
  have hraw := volume_transition_coeffNorm_bound (hF k) (hF0 k) hAizero (hFnorm k) hVDegree hVjet
  have hraw' : (V k).coeffNorm ≤ (ej * pj) * ((cj * (A (k + 1)).coeffNorm) *
      (1 + pj * BF * (1 + cj * (Ainv k).coeffNorm) ^ d) ^ d) := by
    convert hraw using 1 <;> dsimp [ej, pj, cj] <;> ring
  exact hraw'.trans ((hVexp k).trans heV)

end Yau.Proofs.Y01Aux
