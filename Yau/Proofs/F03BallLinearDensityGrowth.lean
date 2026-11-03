import Yau.Proofs.F03BallMeanDensityGrowth

/-! The original linear ball means yield actual polynomial masses for the density measure. -/
noncomputable section
open MeasureTheory Set
open scoped ComplexOrder
namespace Yau.Proofs.F03Aux
open Yau LeafProofs.L12Aux LeafProofs.L18Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem ball_linear_mean_density_polynomial_growth
    (g : SmoothMetric M) (hcomplete : IsComplete g) (hK : IsKahler g)
    (hRic : ∀ z,(ricci g.form z).PosSemidef)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (o : M.Carrier) (f : M.Carrier → ℝ) {A R : ℝ} (hA : 0 ≤ A) (hR : 1 ≤ R)
    (hMean : ∀ L : ℝ,1 ≤ L → BallIntegralLE g.form μ o f L (A*L)) (j : ℕ) :
    (μ.withDensity (fun y => ENNReal.ofReal (f y)))
      {y | inducedDistance g.form o y/R<(j:ℝ)+1} ≤
      ENNReal.ofReal ((A*R)*(μ (distBall g.form o R)).toReal*((j:ℝ)+1)^(2*n+1)) := by
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  let q : ℝ := (j:ℝ)+1
  have hq : 1 ≤ q := by dsimp [q];linarith [Nat.cast_nonneg (α := ℝ) j]
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hqR : 1 ≤ q*R := by nlinarith
  have hRqR : R ≤ q*R := by nlinarith
  have hqR0 : 0 < q*R := mul_pos hq0 hR0
  have hE : {y | inducedDistance g.form o y/R<(j:ℝ)+1}=distBall g.form o (q*R) := by
    ext y
    rw [mem_distBall_iff g o y hqR0]
    exact div_lt_iff₀ hR0
  have hBG := bishopGromov n M g hcomplete hK hRic μ hμ o R (q*R) hR0 hRqR
  rw [mul_div_cancel_right₀ q hR0.ne'] at hBG
  have hCoeff : 0 ≤ A*(q*R) := by positivity
  rw [hE,withDensity_apply _ (measurableSet_distBall g o (q*R))]
  calc
    _ ≤ ENNReal.ofReal (A*(q*R))*μ (distBall g.form o (q*R)) := hMean (q*R) hqR
    _ ≤ ENNReal.ofReal (A*(q*R))*(ENNReal.ofReal (q^(2*n))*μ (distBall g.form o R)) :=
      mul_le_mul_of_nonneg_left hBG (by positivity)
    _ = ENNReal.ofReal ((A*(q*R))*(q^(2*n)*(μ (distBall g.form o R)).toReal)) := by
      rw [ENNReal.ofReal_mul hCoeff,ENNReal.ofReal_mul (pow_nonneg hq0.le _),
        ENNReal.ofReal_toReal (riemannianVolume_distBall_lt_top g μ hμ o hR0).ne]
    _ = _ := by
      dsimp [q]
      rw [pow_succ]
      congr 1
      ring

end Yau.Proofs.F03Aux
