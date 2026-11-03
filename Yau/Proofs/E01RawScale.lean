import Yau.Proofs.E01DualScale
import Yau.Proofs.E01ERealScale

/-! Exact positive real homogeneity of the original infimum over genuine cotangent discs. -/

noncomputable section
open scoped Manifold Topology ContDiff Matrix

namespace Yau.NodeProofs.E01Aux
open Yau Yau.Blueprint

variable {n : ℕ} {M : ComplexManifold n}

theorem envelopeRaw_positive_real_smul_le (h : ℝ → HermitianField M) (T : ℝ)
    (y : M.Carrier) (ξ : Covector n) (s r : ℝ) (hr : 0 < r) :
    envelopeRaw h T y ((r : ℂ) • ξ) s ≤
      ((r ^ 2 : ℝ) : EReal) * envelopeRaw h T y ξ s := by
  unfold envelopeRaw
  simp only [erealPositiveScale_iInf (r ^ 2) (sq_pos_of_pos hr)]
  refine le_iInf fun f => le_iInf fun ξd => le_iInf fun w => le_iInf fun had => ?_
  rcases had with ⟨hs, hsT, hd, hw, hf, hξ, hw0, ht⟩
  have hscaled : 0 < s ∧ s < T ∧ IsCotangentDisc f (fun ζ => (r : ℂ) • ξd ζ) ∧
      ContDiffOn ℂ ∞ w (Metric.closedBall 0 1) ∧ f 0 = y ∧
      (fun ζ => (r : ℂ) • ξd ζ) 0 = (r : ℂ) • ξ ∧ w 0 = 0 ∧
      ∀ ζ ∈ Metric.closedBall (0 : ℂ) 1, s * Real.exp (2 * (w ζ).re) < T :=
    ⟨hs, hsT, original_cotangentDisc_const_smul hd (r : ℂ), hw, hf,
      congrArg (fun ν : Covector n => (r : ℂ) • ν) hξ, hw0, ht⟩
  refine iInf_le_of_le f (iInf_le_of_le (fun ζ => (r : ℂ) • ξd ζ)
    (iInf_le_of_le w (iInf_le_of_le hscaled ?_)))
  have hnr : ‖(r : ℂ)‖ ^ 2 = r ^ 2 := by simp [Complex.norm_real, Real.norm_eq_abs]
  simp only [dualNorm_complex_smul, hnr, original_circleAverage_const_mul, EReal.coe_mul, le_refl]

theorem envelopeRaw_positive_real_smul (h : ℝ → HermitianField M) (T : ℝ)
    (y : M.Carrier) (ξ : Covector n) (s r : ℝ) (hr : 0 < r) :
    envelopeRaw h T y ((r : ℂ) • ξ) s =
      ((r ^ 2 : ℝ) : EReal) * envelopeRaw h T y ξ s := by
  apply le_antisymm (envelopeRaw_positive_real_smul_le h T y ξ s r hr)
  have hrev := envelopeRaw_positive_real_smul_le h T y ((r : ℂ) • ξ) s r⁻¹ (inv_pos.mpr hr)
  have hinv : ((r⁻¹ : ℝ) : ℂ) • ((r : ℂ) • ξ) = ξ := by
    rw [smul_smul, ← Complex.ofReal_mul, inv_mul_cancel₀ hr.ne', Complex.ofReal_one, one_smul]
  rw [hinv] at hrev
  have hh := mul_le_mul_of_nonneg_left hrev (EReal.coe_nonneg.mpr (sq_nonneg r))
  have hcoef : r ^ 2 * r⁻¹ ^ 2 = 1 := by rw [← mul_pow, mul_inv_cancel₀ hr.ne', one_pow]
  simpa only [← mul_assoc, ← EReal.coe_mul, hcoef, EReal.coe_one, one_mul] using hh

end Yau.NodeProofs.E01Aux
