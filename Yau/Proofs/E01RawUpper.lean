import spec.CHAIN.CONTRACTS

/-! The actual constant-disc competitor bounds the original raw envelope. -/

noncomputable section
open scoped Manifold Topology ContDiff Matrix
open MeasureTheory

namespace Yau.NodeProofs.E01Aux
open Yau Yau.Blueprint

variable {n : ℕ} {M : ComplexManifold n}

theorem original_cotangentDisc_const (y : M.Carrier) (ξ : Covector n) :
    IsCotangentDisc (fun _ : ℂ => y) (fun _ => ξ) :=
  ⟨contMDiffOn_const, fun _ _ => contDiffWithinAt_const⟩

theorem original_circleAverage_const (c : ℝ) : circleAverage (fun _ => c) = c := by
  unfold circleAverage
  rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul]
  have hp : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  rw [← mul_assoc, inv_mul_cancel₀ hp, one_mul]

theorem envelopeRaw_le_actual_dualNorm
    (h : ℝ → HermitianField M) (T : ℝ) (y : M.Carrier) (ξ : Covector n)
    (s : ℝ) (hs : 0 < s) (hsT : s < T) :
    envelopeRaw h T y ξ s ≤ (dualNorm (h s) y ξ : EReal) := by
  unfold envelopeRaw
  refine iInf_le_of_le (fun _ : ℂ => y) (iInf_le_of_le (fun _ : ℂ => ξ)
    (iInf_le_of_le (fun _ : ℂ => (0 : ℂ)) ?_))
  have had : 0 < s ∧ s < T ∧ IsCotangentDisc (fun _ : ℂ => y) (fun _ => ξ) ∧
      ContDiffOn ℂ ∞ (fun _ : ℂ => (0 : ℂ)) (Metric.closedBall 0 1) ∧
      (fun _ : ℂ => y) 0 = y ∧ (fun _ : ℂ => ξ) 0 = ξ ∧
      (fun _ : ℂ => (0 : ℂ)) 0 = 0 ∧
      ∀ ζ ∈ Metric.closedBall (0 : ℂ) 1, s * Real.exp (2 * (0 : ℂ).re) < T :=
    ⟨hs, hsT, original_cotangentDisc_const y ξ, contDiffOn_const,
      rfl, rfl, rfl, fun _ _ => by simpa using hsT⟩
  refine iInf_le_of_le had ?_
  simp only [Complex.zero_re, mul_zero, Real.exp_zero, mul_one, original_circleAverage_const,
    le_refl]

end Yau.NodeProofs.E01Aux
