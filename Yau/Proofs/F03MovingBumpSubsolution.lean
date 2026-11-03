import Yau.Proofs.F03MovingBumpPrincipal
import Yau.Proofs.F03MovingBumpRate

/-! Genuine differential inequality of the moving cubic in computed elliptic charts. -/
noncomputable section
open Filter Set
open scoped Topology InnerProductSpace
namespace Yau.Proofs.F03Aux
open Yau Parabolic LeafProofs.L16Aux
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

theorem movingBallBump_residual_le {n : ℕ} {Q : Set (Point n)}
    {a : Point n → Mat n} {lam upper R V : ℝ}
    (hEll : Elliptic Q a lam upper) (hR : 0 < R)
    {c : ℝ → Space n} {c' : Space n} (p : Point n) (hp : p ∈ Q)
    (hc : HasDerivAt c c' p.2) (hV : ‖c'‖ ≤ V) :
    deriv (fun s => movingBallBump R c (p.1,s)) p.2 -
      (∑ i, ∑ j, a p i j*spatialDD (movingBallBump R c) p (realVec i) (realVec j)) ≤
      movingCubicRate R lam (2*R*V+2*(Fintype.card (RIdx n) : ℝ)*upper)*movingBallBump R c p := by
  let d := p.1-c p.2
  let q := R^2-‖d‖^2
  let P := 2*R*V+2*(Fintype.card (RIdx n) : ℝ)*upper
  have hV0 : 0 ≤ V := (norm_nonneg c').trans hV
  have hU0 : 0 < upper := hEll.1.trans_le hEll.2.1
  have hP : 0 ≤ P := by dsimp only [P]; positivity
  rw [(movingBallBump_time_hasDerivAt R p.1 hc).deriv,movingBallBump_principal]
  change 6*positivePower 2 q*inner ℝ d c' -
    (24*positivePower 1 q*(∑ i, ∑ j, a p i j*realCoord d i*realCoord d j) -
      6*positivePower 2 q*(∑ i, a p i i)) ≤
    movingCubicRate R lam P*positivePower 3 q
  by_cases hq : 0 < q
  · have hdn : ‖d‖ < R := by
      have hd2 : ‖d‖^2 < R^2 := sub_pos.mp hq
      nlinarith only [hd2,hR,norm_nonneg d]
    have hinner : inner ℝ d c' ≤ R*V :=
      (real_inner_le_norm d c').trans (mul_le_mul hdn.le hV (norm_nonneg c') hR.le)
    have hquad : lam*‖d‖^2 ≤ ∑ i, ∑ j, a p i j*realCoord d i*realCoord d j := by
      simpa only [sum_realCoord_sq] using ((hEll.2.2 p hp).2 (realCoord d)).1
    have htrace := elliptic_trace_upper hEll hp
    have ht := mul_le_mul_of_nonneg_left hinner
      (show 0 ≤ 6*positivePower 2 q by unfold positivePower; positivity)
    have hq' := mul_le_mul_of_nonneg_left hquad
      (show 0 ≤ 24*positivePower 1 q by unfold positivePower; positivity)
    have htr := mul_le_mul_of_nonneg_left htrace
      (show 0 ≤ 6*positivePower 2 q by unfold positivePower; positivity)
    have hrate := moving_cubic_polynomial_bound R lam P ‖d‖ hR hEll.1 hP
    change 3*P*positivePower 2 q-24*lam*‖d‖^2*positivePower 1 q ≤
      movingCubicRate R lam P*positivePower 3 q at hrate
    dsimp only [P] at hrate ⊢
    nlinarith only [ht,hq',htr,hrate]
  · have hq0 : q ≤ 0 := le_of_not_gt hq
    simp only [positivePower,max_eq_left hq0,zero_pow (by decide : 2 ≠ 0),
      zero_pow (by decide : 1 ≠ 0),zero_pow (by decide : 3 ≠ 0),mul_zero,zero_mul,
      sub_self,le_refl]

end Yau.Proofs.F03Aux
