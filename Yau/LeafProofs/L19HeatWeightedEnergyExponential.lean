import Yau.LeafProofs.L19HeatWeightedEnergy

/-! Exponential weights, with every multiplier bound derived internally. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology InnerProductSpace
namespace Yau.LeafProofs.L19Aux
open L18Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

theorem smoothFn_exp {ψ : M.Carrier → ℝ} (hψ : SmoothFn ψ) :
    SmoothFn (fun x => Real.exp (ψ x)) :=
  smoothFn_scalar_comp hψ Real.exp Real.contDiff_exp

theorem scalarExp_bound (ψ : M.Carrier → ℝ) (b : ℝ) (hb : ∀ x, ψ x ≤ b) :
    ∀ x, |Real.exp (ψ x)| ≤ Real.exp b := by
  intro x
  rw [abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_exp.mpr (hb x)

/-- The actual exponential weight on scalar L². An upper bound suffices
for this bounded operator. -/
def scalarExpMultiplierL2 (μ : Measure M.Carrier) (ψ : M.Carrier → ℝ)
    (hψ : SmoothFn ψ) (b : ℝ) (hb : ∀ x, ψ x ≤ b) : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  scalarMultiplierL2 μ (fun x => Real.exp (ψ x))
    (continuous_of_smoothFn (smoothFn_exp hψ)).aestronglyMeasurable
    (Real.exp b) (scalarExp_bound ψ b hb)

theorem scalarExpMultiplierL2_coe (μ : Measure M.Carrier) (ψ : M.Carrier → ℝ)
    (hψ : SmoothFn ψ) (b : ℝ) (hb : ∀ x, ψ x ≤ b) (f : Lp ℝ 2 μ) :
    scalarExpMultiplierL2 μ ψ hψ b hb f =ᵐ[μ] (fun x => Real.exp (ψ x) * f x) :=
  scalarMultiplierL2_coe μ _ _ _ _ f

theorem scalarGradientPair_exp_self (g : SmoothMetric M) {ψ : M.Carrier → ℝ}
    (hψ : SmoothFn ψ) (x : M.Carrier) :
    scalarGradientPair g.form (fun x => Real.exp (ψ x)) (fun x => Real.exp (ψ x)) x =
      Real.exp (ψ x) ^ 2 * scalarGradientPair g.form ψ ψ x := by
  rw [scalarGradientPair_scalar_comp_self g.form hψ Real.exp x
    (Real.hasDerivAt_exp (ψ x)).differentiableAt, Real.deriv_exp]

/-- Davies' weighted L² estimate for the actual CFC heat flow, with the
project's half-physical-Laplacian normalization. No regularity or weighted
estimate is supplied by the caller. -/
theorem scalarHeatFamily_weighted_L2 (g : SmoothMetric M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (ψ : M.Carrier → ℝ) (hψ : SmoothFn ψ) (b : ℝ) (hb : ∀ x, ψ x ≤ b)
    (ell : ℝ) (hgrad : ∀ x, scalarGradientPair g.form ψ ψ x ≤ ell ^ 2)
    (t : ℝ) (ht : 0 ≤ t) (f : Lp ℝ 2 μ) :
    ‖scalarExpMultiplierL2 μ ψ hψ b hb (scalarHeatFamily g μ hμ t f)‖ ≤
      Real.exp (ell ^ 2 * t / 2) * ‖scalarExpMultiplierL2 μ ψ hψ b hb f‖ := by
  have hrel (x : M.Carrier) :
      scalarGradientPair g.form (fun x => Real.exp (ψ x)) (fun x => Real.exp (ψ x)) x ≤
        ell ^ 2 * Real.exp (ψ x) ^ 2 := by
    rw [scalarGradientPair_exp_self g hψ]
    nlinarith [mul_le_mul_of_nonneg_left (hgrad x) (sq_nonneg (Real.exp (ψ x)))]
  have hC (x : M.Carrier) :
      scalarGradientPair g.form (fun x => Real.exp (ψ x)) (fun x => Real.exp (ψ x)) x ≤
        (Real.exp b * ell) ^ 2 := by
    have he : Real.exp (ψ x) ^ 2 ≤ Real.exp b ^ 2 :=
      (sq_le_sq₀ (Real.exp_pos _).le (Real.exp_pos _).le).2 (Real.exp_le_exp.mpr (hb x))
    calc
      _ ≤ ell ^ 2 * Real.exp (ψ x) ^ 2 := hrel x
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left he (sq_nonneg ell)]
  exact scalarHeatFamily_multiplier_norm_le g μ hμ _ (smoothFn_exp hψ)
    (Real.exp b) (Real.exp b * ell) (scalarExp_bound ψ b hb) hC ell hrel t ht f

end Yau.LeafProofs.L19Aux
