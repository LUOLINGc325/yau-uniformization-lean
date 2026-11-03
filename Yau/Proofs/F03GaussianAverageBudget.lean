import Yau.Proofs.F03BallMeanDensityGrowth
import Yau.Proofs.F03GaussianPolynomialSeries

/-! Actual normalized ball averages imply a Gaussian integral budget with one constant before every volume. -/
noncomputable section
open MeasureTheory Set
open scoped ComplexOrder ENNReal
namespace Yau.Proofs.F03Aux
open Yau LeafProofs.L12Aux LeafProofs.L18Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem exists_gaussian_average_budget
    (g : SmoothMetric M) (hcomplete : IsComplete g) (hK : IsKahler g)
    (hRic : ∀ z,(ricci g.form z).PosSemidef) {c : ℝ} (hc : 0 < c) :
    ∃ C : ℝ,0 < C ∧ ∀ (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
      (o : M.Carrier) (f : M.Carrier → ℝ),Measurable f →
      ∀ A : ℝ,0 ≤ A → (∀ L : ℝ,1 ≤ L → BallIntegralLE g.form μ o f L (A/L)) →
      ∀ R : ℝ,1 ≤ R →
      (∫⁻ y,ENNReal.ofReal (Real.exp (-c*(inducedDistance g.form o y/R)^2)*f y) ∂μ) ≤
        ENNReal.ofReal (C*A/R*(μ (distBall g.form o R)).toReal) := by
  obtain ⟨C,hC,hBudget⟩ := exists_gaussian_polynomial_mass_budget (α := M.Carrier) (2*n) hc
  refine ⟨C,hC,fun μ hμ o f hf A hA hMean R hR => ?_⟩
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  let radius : M.Carrier → ℝ := fun y => inducedDistance g.form o y/R
  let ν := μ.withDensity (fun y => ENNReal.ofReal (f y))
  let B := (A/R)*(μ (distBall g.form o R)).toReal
  have hRadius : Measurable radius := ((continuous_distFrom g o).div_const R).measurable
  have hRadius0 : ∀ y,0 ≤ radius y := fun y => div_nonneg (g.induced_distance_nonneg o y) hR0.le
  have hB : 0 ≤ B := mul_nonneg (div_nonneg hA hR0.le) ENNReal.toReal_nonneg
  have hGrowth (j : ℕ) : ν {y | radius y<(j : ℝ)+1} ≤ ENNReal.ofReal (B*((j : ℝ)+1)^(2*n)) :=
    ball_mean_density_polynomial_growth g hcomplete hK hRic μ hμ o f hA hR hMean j
  have hActual := hBudget ν radius hRadius hRadius0 B hB hGrowth
  have hDensity : Measurable (fun y => ENNReal.ofReal (f y)) := ENNReal.measurable_ofReal.comp hf
  have hGaussian : Measurable (fun y => ENNReal.ofReal (Real.exp (-c*(radius y)^2))) :=
    ENNReal.measurable_ofReal.comp (Real.continuous_exp.measurable.comp
      (measurable_const.mul (hRadius.pow_const 2)))
  dsimp only [ν] at hActual
  rw [lintegral_withDensity_eq_lintegral_mul μ hDensity hGaussian] at hActual
  simp only [Pi.mul_apply] at hActual
  have hProduct : (∫⁻ y,ENNReal.ofReal (Real.exp (-c*(radius y)^2)*f y) ∂μ)=
      ∫⁻ y,ENNReal.ofReal (f y)*ENNReal.ofReal (Real.exp (-c*(radius y)^2)) ∂μ := by
    apply lintegral_congr
    intro y
    rw [ENNReal.ofReal_mul (Real.exp_pos _).le,mul_comm]
  rw [← hProduct] at hActual
  calc
    _ ≤ ENNReal.ofReal (C*B) := hActual
    _ = _ := by dsimp [B];congr 1;ring

end Yau.Proofs.F03Aux
