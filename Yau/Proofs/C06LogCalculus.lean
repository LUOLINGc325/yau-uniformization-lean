import Yau.Proofs.P07DistanceLeviCalculus

noncomputable section
open Filter
open scoped Topology ContDiff

namespace Yau.Proofs.C06Aux

open Yau Yau.Blueprint Yau.NodeProofs.P07DistanceLevi

variable {n : ℕ}

/-- The actual radial first variation cancels the flat part of the index form. -/
theorem log_levi_neg {f : ComplexVector n → ℝ} {z v : ComplexVector n}
    (hf : ContDiffAt ℝ 2 f z) (hp : 0 < f z)
    (hLevi : leviDirection (leviC f z) v < f z)
    (hfirst : fderiv ℝ f z v = 2 * f z) :
    leviDirection (leviC (Real.log ∘ f) z) v < 0 := by
  rw [leviDirection_scalar_comp hf (Real.contDiffAt_log.mpr hp.ne')]
  rw [Real.deriv_log, Real.deriv_log']
  have hsecond : deriv (fun x : ℝ => x⁻¹) (f z) = -(f z ^ 2)⁻¹ := by
    simpa only [one_div] using (hasDerivAt_inv hp.ne').deriv
  rw [hsecond]
  have hRank : f z ^ 2 ≤ directionalRankOne f z v := by
    unfold directionalRankOne
    rw [hfirst]
    nlinarith [sq_nonneg (fderiv ℝ f z (Complex.I • v))]
  have h₁ : (f z)⁻¹ * leviDirection (leviC f z) v < 1 := by
    have H := mul_lt_mul_of_pos_left hLevi (inv_pos.mpr hp)
    simpa only [inv_mul_cancel₀ hp.ne'] using H
  have h₂ : 1 ≤ (f z ^ 2)⁻¹ * directionalRankOne f z v := by
    have H := mul_le_mul_of_nonneg_left hRank (inv_nonneg.mpr (sq_nonneg (f z)))
    simpa only [inv_mul_cancel₀ (pow_ne_zero 2 hp.ne')] using H
  nlinarith

end Yau.Proofs.C06Aux
