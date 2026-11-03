import Yau.Proofs.F03BallLinearDensityGrowth
import Yau.Proofs.F03GaussianPolynomialSeries

/-! Linear ball means give genuine Gaussian integrability of the actual unbounded density. -/
noncomputable section
open MeasureTheory Set
open scoped ComplexOrder ENNReal
namespace Yau.Proofs.F03Aux
open Yau LeafProofs.L12Aux LeafProofs.L18Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem exists_gaussian_linear_mean_budget
    (g : SmoothMetric M) (hcomplete : IsComplete g) (hK : IsKahler g)
    (hRic : ∀ z,(ricci g.form z).PosSemidef) {c : ℝ} (hc : 0 < c) :
    ∃ C : ℝ,0 < C ∧ ∀ (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
      (o : M.Carrier) (f : M.Carrier → ℝ),Measurable f →
      ∀ A : ℝ,0 ≤ A → (∀ L : ℝ,1 ≤ L → BallIntegralLE g.form μ o f L (A*L)) →
      ∀ R : ℝ,1 ≤ R →
      (∫⁻ y,ENNReal.ofReal (Real.exp (-c*(inducedDistance g.form o y/R)^2)*f y) ∂μ) ≤
        ENNReal.ofReal (C*A*R*(μ (distBall g.form o R)).toReal) := by
  obtain ⟨C,hC,hBudget⟩ := exists_gaussian_polynomial_mass_budget (α := M.Carrier) (2*n+1) hc
  refine ⟨C,hC,fun μ hμ o f hf A hA hMean R hR => ?_⟩
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  let radius : M.Carrier → ℝ := fun y => inducedDistance g.form o y/R
  let ν := μ.withDensity (fun y => ENNReal.ofReal (f y))
  let B := (A*R)*(μ (distBall g.form o R)).toReal
  have hRadius : Measurable radius := ((continuous_distFrom g o).div_const R).measurable
  have hRadius0 : ∀ y,0 ≤ radius y := fun y => div_nonneg (g.induced_distance_nonneg o y) hR0.le
  have hB : 0 ≤ B := by dsimp [B];positivity
  have hGrowth (j : ℕ) : ν {y | radius y<(j:ℝ)+1} ≤ ENNReal.ofReal (B*((j:ℝ)+1)^(2*n+1)) :=
    ball_linear_mean_density_polynomial_growth g hcomplete hK hRic μ hμ o f hA hR hMean j
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

theorem gaussian_linear_mean_integrable
    (g : SmoothMetric M) (hcomplete : IsComplete g) (hK : IsKahler g)
    (hRic : ∀ z,(ricci g.form z).PosSemidef)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (o : M.Carrier) (f : M.Carrier → ℝ) (hf : Measurable f) (hf0 : ∀ y,0 ≤ f y)
    {A : ℝ} (hA : 0 ≤ A) (hMean : ∀ L : ℝ,1 ≤ L → BallIntegralLE g.form μ o f L (A*L))
    {c R : ℝ} (hc : 0 < c) (hR : 1 ≤ R) :
    Integrable (fun y => Real.exp (-c*(inducedDistance g.form o y/R)^2)*f y) μ := by
  obtain ⟨C,_hC,hBudget⟩ := exists_gaussian_linear_mean_budget g hcomplete hK hRic hc
  have hGauss : Measurable (fun y => Real.exp (-c*(inducedDistance g.form o y/R)^2)) :=
    Real.continuous_exp.measurable.comp (measurable_const.mul
      (((continuous_distFrom g o).div_const R).measurable.pow_const 2))
  refine ⟨(hGauss.mul hf).aestronglyMeasurable,?_⟩
  apply (hasFiniteIntegral_iff_ofReal (ae_of_all μ (fun y => mul_nonneg (Real.exp_pos _).le (hf0 y)))).mpr
  exact (hBudget μ hμ o f hf A hA hMean R hR).trans_lt ENNReal.ofReal_lt_top

end Yau.Proofs.F03Aux
