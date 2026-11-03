import Yau.Proofs.C07CauchyIterated
import Yau.Blueprint.Stages

open scoped ContDiff

noncomputable section

namespace Yau.Proofs.C07Aux

open Yau

variable {n : ℕ}

def cauchyJetConstant (d : ℕ) (R : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (d + 1), cauchyFactor k / R ^ k

/-- Summing the actual iterated Fréchet derivatives gives a bound for the
frozen `jetNorm`, with exactly its zeroth-order summand. -/
theorem jetNorm_cauchy_bound {f : ComplexVector n → ComplexVector n} {R B : ℝ}
    (hR : 0 < R) (hf : ContDiffOn ℂ ∞ f (Metric.ball 0 R))
    (hbound : ∀ z ∈ Metric.ball (0 : ComplexVector n) R, ‖f z‖ ≤ B) (d : ℕ) :
    jetNorm f d ≤ cauchyJetConstant d R * B := by
  unfold jetNorm cauchyJetConstant
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro k _
  have hk := iterated_cauchy_bound hR hf hbound k 0
    (Metric.mem_ball_self (by positivity : 0 < R / 2 ^ k))
  exact hk.trans_eq (by ring)

/-- Cauchy on the exponentially small inner ball gives the paper's
`exp(d C₀ s - σ u)` factor, with a constant independent of both clocks. -/
theorem jetNorm_inner_bound {f : ComplexVector n → ComplexVector n}
    {C₀ s σ u : ℝ} (hC : 0 ≤ C₀) (hs : 0 ≤ s)
    (hf : ContDiffOn ℂ ∞ f (Metric.ball 0 (Real.exp (-C₀ * s))))
    (hbound : ∀ z ∈ Metric.ball (0 : ComplexVector n) (Real.exp (-C₀ * s)),
      ‖f z‖ ≤ Real.exp (-σ * u)) (d : ℕ) :
    jetNorm f d ≤ (∑ k ∈ Finset.range (d + 1), cauchyFactor k) *
      Real.exp ((d : ℝ) * C₀ * s - σ * u) := by
  unfold jetNorm
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro k hk
  have hkd : (k : ℝ) ≤ d := by exact_mod_cast (by
    have hh := Finset.mem_range.mp hk
    omega : k ≤ d)
  have h := iterated_cauchy_bound (Real.exp_pos _) hf hbound k 0
    (Metric.mem_ball_self (by positivity))
  calc
    ‖iteratedFDeriv ℂ k f 0‖ ≤
        cauchyFactor k * Real.exp (-σ * u) / Real.exp (-C₀ * s) ^ k := h
    _ = cauchyFactor k * Real.exp ((k : ℝ) * C₀ * s - σ * u) := by
      rw [← Real.exp_nat_mul, mul_div_assoc, ← Real.exp_sub]
      congr 2
      ring
    _ ≤ cauchyFactor k * Real.exp ((d : ℝ) * C₀ * s - σ * u) := by
      apply mul_le_mul_of_nonneg_left _ (cauchyFactor_pos k).le
      apply Real.exp_le_exp.mpr
      nlinarith [mul_nonneg (sub_nonneg.mpr hkd) (mul_nonneg hC hs)]

end Yau.Proofs.C07Aux
