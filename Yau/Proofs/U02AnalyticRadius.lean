import Yau.Proofs.U02AnalyticBounds
import Mathlib.Analysis.Analytic.ConvergenceRadius
import Mathlib.Analysis.Complex.Exponential

open scoped ContDiff Topology
open Set Metric ENNReal NNReal

namespace U02AnalyticAux

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

noncomputable def complexTaylorSeries (f : E → F) (x : E) :
    FormalMultilinearSeries ℂ E F :=
  fun k ↦ (k.factorial : ℂ)⁻¹ • iteratedFDeriv ℂ k f x

theorem norm_complexTaylorSeries (f : E → F) (x : E) (k : ℕ) :
    ‖complexTaylorSeries f x k‖ = ‖iteratedFDeriv ℂ k f x‖ / (k.factorial : ℝ) := by
  simp [complexTaylorSeries, norm_smul, norm_inv, Complex.norm_natCast, div_eq_mul_inv,
    mul_comm]

theorem coefficient_geometric_bound {R C A : ℝ} (hR : 0 < R) (hC : 0 ≤ C)
    (k : ℕ) (hA : A ≤ C * (2 * ((k : ℝ) + 1) / R)^k) :
    A / (k.factorial : ℝ) * (R / (2 * Real.exp 1))^k ≤ C * Real.exp 1 := by
  have hfac : 0 < (k.factorial : ℝ) := by positivity
  have hexp : 0 < Real.exp 1 := Real.exp_pos 1
  have hp : 0 < (Real.exp 1)^k := pow_pos hexp k
  have hpow := Real.pow_div_factorial_le_exp (x := (k : ℝ) + 1) (by positivity) k
  have hexpeq : Real.exp ((k : ℝ) + 1) = Real.exp 1 * (Real.exp 1)^k := by
    rw [Real.exp_add, show (k : ℝ) = (k : ℝ) * 1 by ring, Real.exp_nat_mul]
    ring
  rw [hexpeq] at hpow
  calc
    A / (k.factorial : ℝ) * (R / (2 * Real.exp 1))^k ≤
        (C * (2 * ((k : ℝ) + 1) / R)^k) / (k.factorial : ℝ) *
          (R / (2 * Real.exp 1))^k := by gcongr
    _ = C * (((k : ℝ) + 1)^k / (k.factorial : ℝ)) / (Real.exp 1)^k := by
      rw [div_pow, mul_pow, div_pow, mul_pow]
      field_simp
      <;> ring
    _ ≤ C * (Real.exp 1 * (Real.exp 1)^k) / (Real.exp 1)^k := by gcongr
    _ = C * Real.exp 1 := by field_simp

theorem complexTaylorSeries_radius_bound
    {f : E → F} {x : E} {R C : ℝ}
    (hR : 0 < R) (hC : 0 ≤ C)
    (hf : ContDiffOn ℂ ∞ f (ball x R))
    (hb : ∀ y ∈ ball x R, ‖f y‖ ≤ C) :
    (ENNReal.ofReal (R / (2 * Real.exp 1))) ≤
      (complexTaylorSeries f x).radius := by
  change (↑(Real.toNNReal (R / (2 * Real.exp 1))) : ENNReal) ≤ _
  apply (complexTaylorSeries f x).le_radius_of_bound (C * Real.exp 1)
  intro k
  rw [Real.coe_toNNReal _ (by positivity), norm_complexTaylorSeries]
  exact coefficient_geometric_bound hR hC k (norm_iteratedFDeriv_center_le hR hC hf hb k)

end U02AnalyticAux
