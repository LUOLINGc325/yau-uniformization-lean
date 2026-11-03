import Yau.Proofs.F01DiagonalHeat
import Yau.Proofs.F01PenaltyContactJet
import Yau.Proofs.F01PenaltyContactOperator

/-! A genuine space-time maximum contradicts the actual heat inequalities
once the paper's contact coefficient is negative. All jets come from the
actual penalized scalar; no contact or realization oracle is assumed. -/
noncomputable section
open scoped ContDiff Matrix
namespace Yau.NodeProofs.F01Aux
open Yau
variable {n : ℕ}

theorem penalized_contact_contradiction
    (values : Fin n → ℝ) (hv : ∀ i, 0 < values i)
    (U Q : ComplexVector n × ℝ → ℝ) (f : ComplexVector n → ℝ)
    {z : ComplexVector n} {t T a δ τ C c B G : ℝ}
    (ht : 0 < t) (htT : t ≤ T) (ha : 0 < a) (hδ : 0 ≤ δ)
    (hτ : 0 < τ) (hc : 0 ≤ c) (hQnonneg : 0 ≤ Q (z, t))
    (hlarge : rayleighPenalty a (Q (z, t)) ≤ U (z, t))
    (hUnique : UniqueDiffWithinAt ℝ (Set.Icc 0 T) t)
    (hUtime : DifferentiableWithinAt ℝ (fun s => U (z, s)) (Set.Icc 0 T) t)
    (hQtime : DifferentiableWithinAt ℝ (fun s => Q (z, s)) (Set.Icc 0 T) t)
    (hUspace : ContDiffAt ℝ 2 (fun w => U (w, t)) z)
    (hQspace : ContDiffAt ℝ 2 (fun w => Q (w, t)) z)
    (hf : ContDiffAt ℝ 2 f z)
    (hmaxSpace : IsLocalMax (fun w => U (w, t) - rayleighPenalty a (Q (w, t)) - δ * f w) z)
    (hmaxTime : IsMaxOn (fun s => U (z, s) - rayleighPenalty a (Q (z, s)) - δ * f z)
      (Set.Icc 0 T) t)
    (hUdrift : diagonalHeatWithin values U (Set.Icc 0 T) z t ≤ C * τ +
      2 * (Real.exp (U (z, t)))⁻¹ * Real.sqrt (diagonalGradientNorm values f z) *
        Real.sqrt (diagonalGradientNorm values (fun w => U (w, t)) z))
    (hQheat : c * τ ≤ diagonalHeatWithin values Q (Set.Icc 0 T) z t)
    (hLf : traceWith (Matrix.diagonal (fun i => (values i : ℂ))) (leviC f z) ≤ B * τ)
    (hgrad : diagonalGradientNorm values f z ≤ G * τ)
    (hnegative : C - c * a + 8 * G + δ * (B + 2 * G) < 0) : False := by
  let P := fun p : ComplexVector n × ℝ => U p - rayleighPenalty a (Q p) - δ * f p.1
  have hden : 1 + a * Q (z, t) ≠ 0 := by positivity
  have hJ : ContDiffAt ℝ 2 (rayleighPenalty a) (Q (z, t)) :=
    (rayleighPenalty_contDiffAt a (Q (z, t)) hden).of_le (by simp)
  have hPspace : ContDiffAt ℝ 2 (fun w => P (w, t)) z :=
    (hUspace.sub (hJ.comp z hQspace)).sub (contDiffAt_const.mul hf)
  have hJtime := (hJ.differentiableAt (by norm_num)).hasDerivAt.comp_hasDerivWithinAt t
    hQtime.hasDerivWithinAt
  have hPtime : DifferentiableWithinAt ℝ (fun s => P (z, s)) (Set.Icc 0 T) t :=
    ((hUtime.hasDerivWithinAt.sub hJtime).sub
      (hasDerivWithinAt_const t (Set.Icc 0 T) (δ * f z))).differentiableWithinAt
  have hnonneg := diagonalHeatWithin_nonneg_at_max values hv P ht htT
    hPspace hmaxSpace hPtime hmaxTime
  have hjet : diagonalCovectorJet (fun w => U (w, t)) z = fun i =>
      ((deriv (rayleighPenalty a) (Q (z, t)) : ℝ) : ℂ) *
        diagonalCovectorJet (fun w => Q (w, t)) z i + (δ : ℂ) * diagonalCovectorJet f z i := by
    funext i
    exact penalty_contact_wirtinger_jet (fun w => U (w, t)) (fun w => Q (w, t)) f
      (hUspace.differentiableAt (by norm_num)) (hQspace.differentiableAt (by norm_num))
      (hf.differentiableAt (by norm_num)) a δ hden hmaxSpace (stdVec i)
  have hne (i : Fin n) : values i ≠ 0 := (hv i).ne'
  have hnorm (g : ComplexVector n → ℝ) := diagonalGradientNorm_eq_weighted values hne g z
  have hUw : diagonalHeatWithin values U (Set.Icc 0 T) z t ≤ C * τ +
      2 * (Real.exp (U (z, t)))⁻¹ *
        Real.sqrt (weightedCovectorSquare (fun i => (values i)⁻¹) (diagonalCovectorJet f z)) *
        Real.sqrt (weightedCovectorSquare (fun i => (values i)⁻¹)
          (diagonalCovectorJet (fun w => U (w, t)) z)) := by
    simpa only [hnorm] using hUdrift
  have hgw : weightedCovectorSquare (fun i => (values i)⁻¹) (diagonalCovectorJet f z) ≤ G * τ := by
    simpa only [hnorm] using hgrad
  have hb := penalty_contact_operator_bound (fun i => (values i)⁻¹)
    (fun i => inv_nonneg.mpr (hv i).le) (diagonalCovectorJet f z)
    (diagonalCovectorJet (fun w => Q (w, t)) z) (diagonalCovectorJet (fun w => U (w, t)) z)
    ha hQnonneg (Real.exp_le_exp.mpr hlarge) hδ hτ.le hc hjet hUw hQheat hLf hgw
  have hchain := diagonalHeatWithin_penalty_chain values hne U Q f (rayleighPenalty a)
    hUnique hUtime hQtime hUspace hQspace hf hJ (δ := δ)
  rw [hnorm] at hchain
  have htest : diagonalHeatWithin values P (Set.Icc 0 T) z t ≤
      (C - c * a + 8 * G + δ * (B + 2 * G)) * τ := by
    rw [hchain]
    exact hb
  have hlt := mul_neg_of_neg_of_pos hnegative hτ
  linarith

end Yau.NodeProofs.F01Aux
