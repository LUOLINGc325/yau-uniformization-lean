import Yau.Proofs.F03CoarseKernelBound

/-! An actual single-center Gaussian bound transfers to one reference Gaussian with explicit volume loss. -/
noncomputable section
open MeasureTheory Set
open scoped ComplexOrder
namespace Yau.Proofs.F03Aux
open Yau Blueprint LeafProofs.L24Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem single_center_gaussian_to_reference
    (g : SmoothMetric M) (hcomplete : IsComplete g) (hK : IsKahler g)
    (hRic : ∀ z,(ricci g.form z).PosSemidef)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ) (o x y : M.Carrier)
    {C₀ K c L b v : ℝ} (hC₀ : 0 ≤ C₀) (hK0 : 0 ≤ K) (hc : 0 < c)
    (hL : 1 ≤ L) (hb : 0 < b) (hbL : b ≤ L^2)
    (hx : inducedDistance g.form o x ≤ C₀*L)
    (hv : v ≤ K*Real.exp (-c*inducedDistance g.form x y^2/b)/
      (μ (distBall g.form x (Real.sqrt b))).toReal) :
    v ≤ (K*Real.exp c*(2*(C₀+1))^(2*n))*(L/Real.sqrt b)^(2*n)*
      Real.exp (-(c/2)*(inducedDistance g.form o y/((C₀+1)*L))^2)/
      (μ (distBall g.form o ((C₀+1)*L))).toReal := by
  let D := C₀+1
  let R := D*L
  let r := Real.sqrt b
  have hD : 1 ≤ D := by dsimp [D];linarith
  have hD0 : 0 < D := zero_lt_one.trans_le hD
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hR : 0 < R := mul_pos hD0 hL0
  have hr : 0 < r := Real.sqrt_pos.mpr hb
  have hrL : r ≤ L := Real.sqrt_le_iff.mpr ⟨hL0.le,hbL⟩
  have hLR : L ≤ R := by dsimp [R];nlinarith
  have hNear : inducedDistance g.form o x ≤ R := by dsimp [R,D];nlinarith
  have hbR : b ≤ R^2 := hbL.trans (pow_le_pow_left₀ hL0.le hLR 2)
  have hInv := ball_inverse_volume_center_transfer g hcomplete hK hRic μ hμ o x hr (hrL.trans hLR) hNear
  have hExponent := nearby_gaussian_exponent (c := c)
    (d := inducedDistance g.form x y) (D := inducedDistance g.form o y)
    (t := R^2) (s := b) (r := R) hc.le (sq_pos_of_pos hR) hb hbR hR.le rfl
    (g.induced_distance_nonneg x y) (g.induced_distance_nonneg o y)
    (by linarith [g.induced_distance_triangle o x y])
  have hExp : Real.exp (-c*inducedDistance g.form x y^2/b) ≤
      Real.exp c*Real.exp (-(c/2)*(inducedDistance g.form o y/R)^2) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    convert hExponent using 1 <;> rw [div_pow] <;> ring
  calc
    v ≤ K*Real.exp (-c*inducedDistance g.form x y^2/b)*
        (1/(μ (distBall g.form x r)).toReal) := by simpa only [div_eq_mul_inv,one_mul,r] using hv
    _ ≤ K*(Real.exp c*Real.exp (-(c/2)*(inducedDistance g.form o y/R)^2))*
        (((2*R)/r)^(2*n)/(μ (distBall g.form o R)).toReal) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hExp hK0) hInv (by positivity) (by positivity)
    _ = _ := by
      have hRatio : (2*R)/r=(2*D)*(L/r) := by dsimp [R];ring
      rw [hRatio,mul_pow]
      dsimp [R,D,r]
      ring

end Yau.Proofs.F03Aux
