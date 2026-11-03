import Yau.Proofs.F03GaussianDenominator

/-! Actual volume at a nearby small ball controls the reference large ball. -/
noncomputable section
open MeasureTheory Set
open scoped ComplexOrder
namespace Yau.Proofs.F03Aux
open Yau LeafProofs.L12Aux LeafProofs.L18Aux LeafProofs.L24Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem ball_inverse_volume_center_transfer
    (g : SmoothMetric M) (hcomplete : IsComplete g) (hK : IsKahler g)
    (hRic : ∀ z,(ricci g.form z).PosSemidef)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (o x : M.Carrier) {r R : ℝ} (hr : 0 < r) (hrR : r ≤ R)
    (hNear : inducedDistance g.form o x ≤ R) :
    1/(μ (distBall g.form x r)).toReal ≤ ((2*R)/r)^(2*n)/(μ (distBall g.form o R)).toReal := by
  have hR : 0 < R := hr.trans_le hrR
  let k := (2*R)/r
  have hk : 1 ≤ k := (le_div_iff₀ hr).mpr (by linarith)
  have hkr : k*r=2*R := by dsimp [k];field_simp [hr.ne']
  have hsub : distBall g.form o R ⊆ distBall g.form x (k*r) := by
    intro y hy
    have hy' := (mem_distBall_iff g o y hR).mp hy
    rw [hkr]
    apply (mem_distBall_iff g x y (by positivity : 0 < 2*R)).mpr
    have htri := g.induced_distance_triangle x o y
    rw [g.induced_distance_symm x o] at htri
    linarith
  have hBG := ball_volume_le_of_subset_dilate g hcomplete hK hRic μ hμ o x hr hk hsub
  have hVx : 0 < (μ (distBall g.form x r)).toReal := ENNReal.toReal_pos
    (riemannianVolume_distBall_pos g μ hμ x hr).ne'
    (riemannianVolume_distBall_lt_top g μ hμ x hr).ne
  have hVo : 0 < (μ (distBall g.form o R)).toReal := ENNReal.toReal_pos
    (riemannianVolume_distBall_pos g μ hμ o hR).ne'
    (riemannianVolume_distBall_lt_top g μ hμ o hR).ne
  apply (div_le_div_iff₀ hVx hVo).mpr
  simpa only [one_mul] using hBG

end Yau.Proofs.F03Aux
