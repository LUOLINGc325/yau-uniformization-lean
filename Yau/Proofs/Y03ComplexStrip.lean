import Yau.Proofs.Y03Strip
import Yau.Proofs.Y03Laplacian

/-! The bounded-strip theorem with the contract's literal complex Levi derivative. -/

open scoped Topology
open Set

noncomputable section

namespace Yau.Blueprint.Alignment.Y03Proof

open Yau

theorem bounded_complex_strip_maximum {u : ℂ → ℝ} {T B C : ℝ} (hT : 0 < T)
    (hc : ContinuousOn u {z | 0 ≤ z.re ∧ z.re ≤ T})
    (hf : ∀ z : ℂ, 0 < z.re → z.re < T → ContDiffAt ℝ 2 u z)
    (hlevi : ∀ z : ℂ, 0 < z.re → z.re < T →
      0 ≤ (wirt (fun w => wirtBar (fun q => (u q : ℂ)) w 1) z 1).re)
    (hbounded : ∀ z : ℂ, 0 ≤ z.re → z.re ≤ T → u z ≤ C)
    (hleft : ∀ y : ℝ, u ((y : ℂ) * Complex.I) ≤ B)
    (hright : ∀ y : ℝ, u ((T : ℂ) + (y : ℂ) * Complex.I) ≤ B) :
    ∀ z : ℂ, 0 ≤ z.re → z.re ≤ T → u z ≤ B := by
  have hmap : MapsTo Complex.equivRealProdCLM.symm (Icc 0 T ×ˢ univ)
      {z : ℂ | 0 ≤ z.re ∧ z.re ≤ T} := by
    intro p hp
    simpa only [mem_ofPred_eq, mem_Icc, Complex.equivRealProdCLM_symm_apply,
      Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero] using hp.1
  have hrect : ∀ p ∈ Icc 0 T ×ˢ univ, (u ∘ Complex.equivRealProdCLM.symm) p ≤ B := by
    apply bounded_strip_maximum hT
    · exact hc.comp Complex.equivRealProdCLM.symm.continuous.continuousOn hmap
    · intro p hp
      apply (hf (Complex.equivRealProdCLM.symm p) (by simpa using hp.1.1) (by simpa using hp.1.2)).comp
        p Complex.equivRealProdCLM.symm.contDiff.contDiffAt
    · intro p hp
      rw [axisLaplacian_eq_four_re_levi (hf (Complex.equivRealProdCLM.symm p)
        (by simpa using hp.1.1) (by simpa using hp.1.2))]
      exact mul_nonneg (by norm_num) (hlevi _ (by simpa using hp.1.1) (by simpa using hp.1.2))
    · intro p hp
      exact hbounded _ (hmap hp).1 (hmap hp).2
    · intro y
      simpa only [Function.comp_apply, Complex.equivRealProdCLM_symm_apply,
        Complex.ofReal_zero, zero_add] using hleft y
    · intro y
      simpa only [Function.comp_apply, Complex.equivRealProdCLM_symm_apply] using hright y
  intro z hz₀ hzT
  have hp : Complex.equivRealProdCLM z ∈ Icc 0 T ×ˢ univ := by
    exact ⟨⟨hz₀, hzT⟩, mem_univ _⟩
  simpa only [Function.comp_apply, ContinuousLinearEquiv.symm_apply_apply] using hrect _ hp

end Yau.Blueprint.Alignment.Y03Proof
