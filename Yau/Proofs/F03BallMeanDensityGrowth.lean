import Yau.LeafProofs.L24Complete

/-! The actual normalized ball averages give polynomial radial masses for the genuine density measure. -/
noncomputable section
open MeasureTheory Set
open scoped ComplexOrder
namespace Yau.Proofs.F03Aux
open Yau LeafProofs.L12Aux LeafProofs.L18Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem ball_mean_density_polynomial_growth
    (g : SmoothMetric M) (hcomplete : IsComplete g) (hK : IsKahler g)
    (hRic : ∀ z,(ricci g.form z).PosSemidef)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (o : M.Carrier) (f : M.Carrier → ℝ) {A R : ℝ} (hA : 0 ≤ A) (hR : 1 ≤ R)
    (hMean : ∀ L : ℝ,1 ≤ L → BallIntegralLE g.form μ o f L (A/L)) (j : ℕ) :
    (μ.withDensity (fun y => ENNReal.ofReal (f y)))
      {y | inducedDistance g.form o y/R<(j : ℝ)+1} ≤
      ENNReal.ofReal ((A/R)*(μ (distBall g.form o R)).toReal*((j : ℝ)+1)^(2*n)) := by
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  let q : ℝ := (j : ℝ)+1
  have hq : 1 ≤ q := by
    dsimp [q]
    have hj : 0 ≤ (j : ℝ) := Nat.cast_nonneg j
    linarith
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hqR : 1 ≤ q*R := by nlinarith
  have hRqR : R ≤ q*R := by nlinarith
  have hqR0 : 0 < q*R := mul_pos hq0 hR0
  have hE : {y | inducedDistance g.form o y/R<(j : ℝ)+1}=distBall g.form o (q*R) := by
    ext y
    rw [mem_distBall_iff g o y hqR0]
    exact div_lt_iff₀ hR0
  have hBG := bishopGromov n M g hcomplete hK hRic μ hμ o R (q*R) hR0 hRqR
  have hRatio : q*R/R=q := mul_div_cancel_right₀ q hR0.ne'
  rw [hRatio] at hBG
  have hCoeff : ENNReal.ofReal (A/(q*R)) ≤ ENNReal.ofReal (A/R) :=
    ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_left hA hR0 hRqR)
  have hDiv : 0 ≤ A/R := div_nonneg hA hR0.le
  rw [hE,withDensity_apply _ (measurableSet_distBall g o (q*R))]
  calc
    _ ≤ ENNReal.ofReal (A/(q*R))*μ (distBall g.form o (q*R)) := hMean (q*R) hqR
    _ ≤ ENNReal.ofReal (A/R)*(ENNReal.ofReal (q^(2*n))*μ (distBall g.form o R)) :=
      mul_le_mul hCoeff hBG (by positivity) (by positivity)
    _ = _ := by
      rw [ENNReal.ofReal_mul (mul_nonneg hDiv ENNReal.toReal_nonneg),ENNReal.ofReal_mul hDiv,
        ENNReal.ofReal_toReal (riemannianVolume_distBall_lt_top g μ hμ o hR0).ne]
      dsimp [q]
      ac_rfl

end Yau.Proofs.F03Aux
