import Yau.LeafProofs.L24Complete

/-! The actual symmetric Gaussian volume denominator reduces to one center through Bishop--Gromov. -/
noncomputable section
open MeasureTheory Set
open scoped ComplexOrder
namespace Yau.Proofs.F03Aux
open Yau LeafProofs.L12Aux LeafProofs.L18Aux LeafProofs.L24Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000

theorem gaussian_inverse_volume_denominator
    (g : SmoothMetric M) (hcomplete : IsComplete g) (hK : IsKahler g)
    (hRic : ∀ z,(ricci g.form z).PosSemidef)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (x y : M.Carrier) {r : ℝ} (hr : 0 < r) :
    1/Real.sqrt ((μ (distBall g.form x r)).toReal*(μ (distBall g.form y r)).toReal) ≤
      (1+inducedDistance g.form x y/r)^n/(μ (distBall g.form x r)).toReal := by
  let k := 1+inducedDistance g.form x y/r
  have hd : 0 ≤ inducedDistance g.form x y := g.induced_distance_nonneg x y
  have hk : 1 ≤ k := by
    dsimp [k]
    have hh : 0 ≤ inducedDistance g.form x y/r := div_nonneg hd hr.le
    linarith
  have hk0 : 0 ≤ k := zero_le_one.trans hk
  have hkr : 0 < k*r := mul_pos (zero_lt_one.trans_le hk) hr
  have hsub : distBall g.form x r ⊆ distBall g.form y (k*r) := by
    intro z hz
    have hz' := (mem_distBall_iff g x z hr).mp hz
    apply (mem_distBall_iff g y z hkr).mpr
    have htri := g.induced_distance_triangle y x z
    rw [g.induced_distance_symm y x] at htri
    have he : k*r=r+inducedDistance g.form x y := by dsimp [k];field_simp [hr.ne']
    rw [he]
    linarith
  have hBG := ball_volume_le_of_subset_dilate g hcomplete hK hRic μ hμ x y hr hk hsub
  let V := (μ (distBall g.form x r)).toReal
  let W := (μ (distBall g.form y r)).toReal
  have hV : 0 < V := ENNReal.toReal_pos
    (riemannianVolume_distBall_pos g μ hμ x hr).ne'
    (riemannianVolume_distBall_lt_top g μ hμ x hr).ne
  have hW : 0 ≤ W := ENNReal.toReal_nonneg
  have hD : 0 < Real.sqrt (V*W) := sqrt_ball_volume_product_pos g μ hμ x y hr
  have hSquare : V^2 ≤ (k^n*Real.sqrt (V*W))^2 := by
    have hh := mul_le_mul_of_nonneg_left hBG hV.le
    have he : k^(2*n)=(k^n)^2 := by rw [← pow_mul];congr 1;omega
    rw [mul_pow,Real.sq_sqrt (mul_nonneg hV.le hW)]
    rw [he] at hh
    nlinarith
  have hRoot : V ≤ k^n*Real.sqrt (V*W) :=
    (sq_le_sq₀ hV.le (mul_nonneg (pow_nonneg hk0 _) (Real.sqrt_nonneg _))).mp hSquare
  apply (div_le_div_iff₀ hD hV).mpr
  simpa only [one_mul] using hRoot

end Yau.Proofs.F03Aux
