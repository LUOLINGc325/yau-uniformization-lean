import Yau.LeafProofs.L05PerronBarrierBounds
import Yau.LeafProofs.L05PerturbationShapePowers

open Filter MeasureTheory Set Metric
open scoped Topology ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05Aux
open Yau.Parabolic

def perturbInitialSpeed (n : ℕ) (L : ℝ) : ℝ := 2+2*(Fintype.card (Yau.RIdx n) : ℝ)*L
def perturbLateralCoefficient (n : ℕ) (ell : ℝ) : ℝ := 3/((Fintype.card (Yau.RIdx n) : ℝ)*ell)
def perturbShapeMax (n : ℕ) (ell L : ℝ) : ℝ :=
  max (4+perturbInitialSpeed n L) (3+perturbLateralCoefficient n ell)

theorem perturb_initial_speed_ge_two (n : ℕ) {L : ℝ} (hL : 0 ≤ L) :
    2 ≤ perturbInitialSpeed n L := by
  unfold perturbInitialSpeed
  have hh : 0 ≤ 2*(Fintype.card (Yau.RIdx n) : ℝ)*L := by positivity
  linarith

theorem perturb_lateral_coefficient_pos {n : ℕ} (hn : 0 < n) {ell : ℝ} (hell : 0 < ell) :
    0 < perturbLateralCoefficient n ell := by
  have hd : 0 < (Fintype.card (Yau.RIdx n) : ℝ) := by
    simp only [Yau.RIdx,Fintype.card_prod,Fintype.card_fin,Nat.cast_mul,Nat.cast_ofNat]
    positivity
  exact div_pos (by norm_num) (mul_pos hd hell)

theorem perturb_shapeMax_ge_one (n : ℕ) (ell : ℝ) {L : ℝ} (hL : 0 ≤ L) :
    1 ≤ perturbShapeMax n ell L := by
  have hh := le_max_left (4+perturbInitialSpeed n L) (3+perturbLateralCoefficient n ell)
  have hA := perturb_initial_speed_ge_two n hL
  change 1 ≤ max (4+perturbInitialSpeed n L) (3+perturbLateralCoefficient n ell)
  linarith

theorem perturb_initial_shape_bounds {n : ℕ} {ell L : ℝ} (hL : 0 ≤ L)
    {p q : Point n} (hp : p∈unitClosed n) (hpt : p.2=(-1 : ℝ)) (hq : q∈unitClosed n) :
    0 ≤ perronInitialShape p (perturbInitialSpeed n L) q ∧
      perronInitialShape p (perturbInitialSpeed n L) q ≤ perturbShapeMax n ell L ∧
      ‖q.1-p.1‖^2 ≤ 2*perronInitialShape p (perturbInitialSpeed n L) q ∧
      |q.2-p.2|^2 ≤ perronInitialShape p (perturbInitialSpeed n L) q := by
  have hpX : ‖p.1‖ ≤ 1 := by simpa only [mem_closedBall,dist_zero_right] using hp.1
  have hqX : ‖q.1‖ ≤ 1 := by simpa only [mem_closedBall,dist_zero_right] using hq.1
  have hX : ‖q.1-p.1‖ ≤ 2 := (norm_sub_le _ _).trans (by linarith)
  have hX2 : ‖q.1-p.1‖^2 ≤ 4 := by nlinarith only [hX,norm_nonneg (q.1-p.1)]
  have hT0 : 0 ≤ q.2-p.2 := by rw [hpt]; linarith [hq.2.1]
  have hT1 : q.2-p.2 ≤ 1 := by rw [hpt]; linarith [hq.2.2]
  have hA := perturb_initial_speed_ge_two n hL
  have hA0 : 0 ≤ perturbInitialSpeed n L := by linarith
  have hAt0 := mul_nonneg hA0 hT0
  have hAt1 := mul_le_mul_of_nonneg_left hT1 hA0
  have hAt2 := mul_nonneg (sub_nonneg.mpr hA) hT0
  have hMax : 4+perturbInitialSpeed n L ≤ perturbShapeMax n ell L := le_max_left _ _
  simp only [perronInitialShape_apply,sq_abs]
  constructor
  · exact add_nonneg (sq_nonneg _) hAt0
  constructor
  · nlinarith only [hX2,hAt1,hMax]
  constructor
  · nlinarith only [hAt0,sq_nonneg ‖q.1-p.1‖]
  · nlinarith only [hT0,hT1,hAt2,sq_nonneg ‖q.1-p.1‖]

theorem perturb_lateral_shape_bounds {n : ℕ} {ell L : ℝ}
    (hK : 0 ≤ perturbLateralCoefficient n ell)
    {p q : Point n} (hp : p∈unitClosed n) (hpn : ‖p.1‖=1) (hq : q∈unitClosed n) :
    0 ≤ perronLateralShape p (perturbLateralCoefficient n ell) q ∧
      perronLateralShape p (perturbLateralCoefficient n ell) q ≤ perturbShapeMax n ell L ∧
      ‖q.1-p.1‖^2 ≤ 2*perronLateralShape p (perturbLateralCoefficient n ell) q ∧
      |q.2-p.2|^2 ≤ perronLateralShape p (perturbLateralCoefficient n ell) q := by
  have hqX : ‖q.1‖ ≤ 1 := by simpa only [mem_closedBall,dist_zero_right] using hq.1
  have hqX2 : ‖q.1‖^2 ≤ 1 := by nlinarith only [hqX,norm_nonneg q.1]
  have hInner : |inner ℝ q.1 p.1| ≤ 1 := by
    have hh := abs_real_inner_le_norm q.1 p.1
    rw [hpn,mul_one] at hh
    exact hh.trans hqX
  have hILo := (abs_le.mp hInner).1
  have hIHi := (abs_le.mp hInner).2
  have hK0 := mul_nonneg hK (sub_nonneg.mpr hqX2)
  have hK1 := mul_le_mul_of_nonneg_left (show 1-‖q.1‖^2 ≤ 1 by nlinarith [sq_nonneg ‖q.1‖]) hK
  have hTLo : -1 ≤ q.2-p.2 := by linarith [hq.2.1,hp.2.2]
  have hTHi : q.2-p.2 ≤ 1 := by linarith [hq.2.2,hp.2.1]
  have hT2 : (q.2-p.2)^2 ≤ 1 := by nlinarith only [hTLo,hTHi]
  have hNorm := norm_sub_sq_real q.1 p.1
  rw [hpn,one_pow] at hNorm
  have hMax : 3+perturbLateralCoefficient n ell ≤ perturbShapeMax n ell L := le_max_right _ _
  simp only [perronLateralShape_apply hpn,sq_abs]
  constructor
  · nlinarith only [hIHi,hK0,sq_nonneg (q.2-p.2)]
  constructor
  · nlinarith only [hILo,hK1,hT2,hMax]
  constructor
  · nlinarith only [hNorm,hqX2,hK0,sq_nonneg (q.2-p.2)]
  · nlinarith only [hIHi,hK0]

end Yau.LeafProofs.L05Aux
