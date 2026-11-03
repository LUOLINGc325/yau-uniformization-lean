import Yau.Proofs.Y01CoherentBounds

/-! A finite polynomial transition jet has a sqrt-clock coefficient bound
from its actual germ identity and the two endpoint polynomial bounds. -/

noncomputable section

namespace Yau.Proofs.Y01Aux

open Yau.Blueprint Yau.Proofs.Y02Aux
open scoped ContDiff

variable {n d : ℕ}

theorem transitionJet_coeffNorm_sqrt_bounds
    {s : ℕ → ℝ} {hm BF : ℝ} {F : ℕ → ComplexVector n → ComplexVector n}
    {Outer Inner Jet : ℕ → PolyMap n}
    (hs : ∀ k, 1 ≤ s k)
    (hstep : ∀ k, s (k + 1) - s k ≤ (Real.exp hm - 1) * s k)
    (hBF : 0 ≤ BF) (hF : ∀ k, ContDiffAt ℂ d (F k) 0) (hF0 : ∀ k, F k 0 = 0)
    (hFnorm : ∀ k, jetNorm (F k) d ≤ BF)
    (hOuterEnv : ∃ C : ℝ, 0 ≤ C ∧ ∀ k, (Outer k).coeffNorm ≤ Real.exp (C * Real.sqrt (s k)))
    (hInnerEnv : ∃ C : ℝ, 0 ≤ C ∧ ∀ k, (Inner k).coeffNorm ≤ Real.exp (C * Real.sqrt (s k)))
    (hIzero : ∀ k, (Inner k).FixesZero) (hDegree : ∀ k, (Jet k).degree ≤ d)
    (hJet : ∀ k, GermJetEq ((Outer (k + 1)).eval ∘ F k ∘ (Inner k).eval) (Jet k).eval d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k, (Jet k).coeffNorm ≤ Real.exp (C * Real.sqrt (s k)) := by
  obtain ⟨Co, hCo, hOuterNorm⟩ := hOuterEnv
  obtain ⟨Ci, hCi, hInnerNorm⟩ := hInnerEnv
  have hNext : ∃ Cn : ℝ, 0 ≤ Cn ∧ ∀ k,
      (Outer (k + 1)).coeffNorm ≤ Real.exp (Cn * Real.sqrt (s k)) := by
    refine ⟨Co * Real.sqrt (Real.exp hm), by positivity, ?_⟩
    intro k
    exact next_sqrt_envelope hCo (by linarith [hs k]) (hstep k) (hOuterNorm (k + 1))
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
      cj * (Inner k).coeffNorm ≤ Real.exp (Ck * Real.sqrt (s k)) :=
    exists_mul_sqrt_envelope (fun _ => hcj) (fun k => coeffNorm_nonneg (Inner k))
      (hConst cj) ⟨Ci, hCi, hInnerNorm⟩
  have hOneCI := exists_sum_sqrt_envelope hs (hConst 1) hCI
  have hOneCI0 k : 0 ≤ 1 + cj * (Inner k).coeffNorm :=
    add_nonneg zero_le_one (mul_nonneg hcj (coeffNorm_nonneg _))
  have hPowCI0 k : 0 ≤ (1 + cj * (Inner k).coeffNorm) ^ d := pow_nonneg (hOneCI0 k) d
  have hOneInner0 k : 0 ≤ 1 + pj * BF * (1 + cj * (Inner k).coeffNorm) ^ d :=
    add_nonneg zero_le_one (mul_nonneg (mul_nonneg hpj hBF) (hPowCI0 k))
  have hPowInner0 k : 0 ≤ (1 + pj * BF * (1 + cj * (Inner k).coeffNorm) ^ d) ^ d :=
    pow_nonneg (hOneInner0 k) d
  have hCN0 k : 0 ≤ cj * (Outer (k + 1)).coeffNorm := mul_nonneg hcj (coeffNorm_nonneg _)
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
    (fun k => coeffNorm_nonneg (Outer (k + 1))) (hConst cj) hNext
  have hProduct := exists_mul_sqrt_envelope
    (fun k => mul_nonneg hcj (coeffNorm_nonneg _))
    hPowInner0
    hCN hPowInner
  obtain ⟨CV, hCV, hVexp⟩ := exists_mul_sqrt_envelope (fun _ => mul_nonneg hej hpj)
    (fun k => mul_nonneg (hCN0 k) (hPowInner0 k))
    (hConst (ej * pj)) hProduct
  refine ⟨CV, hCV, ?_⟩
  intro k
  have hraw := volume_transition_coeffNorm_bound (hF k) (hF0 k) (hIzero k)
    (hFnorm k) (hDegree k) (hJet k)
  have hraw' : (Jet k).coeffNorm ≤ (ej * pj) * ((cj * (Outer (k + 1)).coeffNorm) *
      (1 + pj * BF * (1 + cj * (Inner k).coeffNorm) ^ d) ^ d) := by
    convert hraw using 1 <;> dsimp [ej, pj, cj] <;> ring
  exact hraw'.trans (hVexp k)

end Yau.Proofs.Y01Aux
