import Mathlib

/-! The actual singular weight on the unit ball and its real derivatives. -/

open scoped ContDiff InnerProductSpace Topology
noncomputable section
namespace Yau.LeafProofs.L21Aux

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def rho (x : E) : ℝ := 1 - ‖x‖ ^ 2

def boundaryWeight (K : ℝ) (x : E) : ℝ := K / rho x

theorem rho_pos {x : E} (hx : x ∈ Metric.ball (0 : E) 1) : 0 < rho x := by
  have hh : ‖x‖ < 1 := by simpa only [Metric.mem_ball, dist_zero_right] using hx
  dsimp [rho]
  nlinarith [norm_nonneg x]

theorem rho_le_one (x : E) : rho x ≤ 1 := by dsimp [rho]; nlinarith [sq_nonneg ‖x‖]

theorem contDiff_rho : ContDiff ℝ ∞ (rho : E → ℝ) :=
  contDiff_const.sub (contDiff_norm_sq ℝ)

theorem hasFDerivAt_rho (x : E) :
    HasFDerivAt (rho : E → ℝ) (-(2 • innerSL ℝ x)) x := by
  exact (hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_sub 1

theorem fderiv_rho (x v : E) : fderiv ℝ (rho : E → ℝ) x v = -2 * inner ℝ x v := by
  rw [(hasFDerivAt_rho x).fderiv]
  simp

theorem contDiffOn_boundaryWeight (K : ℝ) :
    ContDiffOn ℝ ∞ (boundaryWeight K : E → ℝ) (Metric.ball 0 1) := by
  exact contDiffOn_const.div contDiff_rho.contDiffOn (fun x hx => (rho_pos hx).ne')

theorem fderiv_boundaryWeight (K : ℝ) {x : E}
    (hx : x ∈ Metric.ball (0 : E) 1) (v : E) :
    fderiv ℝ (boundaryWeight K : E → ℝ) x v =
      2 * K * (rho x)⁻¹ ^ 2 * inner ℝ x v := by
  have hd := ((hasFDerivAt_inv (rho_pos hx).ne').comp x (hasFDerivAt_rho x)).const_mul K
  have he := congrArg (fun L : E →L[ℝ] ℝ => L v) hd.fderiv
  change fderiv ℝ (fun y : E => K * (rho y)⁻¹) x v = _ at he
  change fderiv ℝ (fun y : E => K / rho y) x v = _
  simp only [div_eq_mul_inv]
  rw [he]
  simp only [ContinuousLinearMap.comp_apply, _root_.smul_apply, _root_.neg_apply,
    ContinuousLinearMap.toSpanSingleton_apply, innerSL_apply_apply, smul_eq_mul]
  simp only [inv_pow]
  ring

theorem second_fderiv_boundaryWeight (K : ℝ) {x : E}
    (hx : x ∈ Metric.ball (0 : E) 1) (v w : E) :
    fderiv ℝ (fun y => fderiv ℝ (boundaryWeight K : E → ℝ) y v) x w =
      2 * K * (rho x)⁻¹ ^ 2 * inner ℝ v w +
        8 * K * (rho x)⁻¹ ^ 3 * inner ℝ x v * inner ℝ x w := by
  have heq : (fun y => fderiv ℝ (boundaryWeight K : E → ℝ) y v) =ᶠ[𝓝 x]
      (fun y => 2 * K * (rho y)⁻¹ ^ 2 * inner ℝ y v) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hx] with y hy
    exact fderiv_boundaryWeight K hy v
  rw [heq.fderiv_eq]
  have hri := (hasFDerivAt_inv (rho_pos hx).ne').comp x (hasFDerivAt_rho x)
  have hlin : HasFDerivAt (fun y : E => inner ℝ y v) (innerSL ℝ v) x := by
    simpa only [coe_innerSL_apply, real_inner_comm] using (innerSL ℝ v).hasFDerivAt (x := x)
  have hd := ((hri.pow 2).const_mul (2 * K)).mul hlin
  have he := congrArg (fun L : E →L[ℝ] ℝ => L w) hd.fderiv
  change fderiv ℝ (fun y : E => 2 * K * (rho y)⁻¹ ^ 2 * inner ℝ y v) x w = _ at he
  rw [he]
  simp only [ContinuousLinearMap.comp_apply, _root_.smul_apply, _root_.neg_apply,
    _root_.add_apply, ContinuousLinearMap.toSpanSingleton_apply, innerSL_apply_apply,
    smul_eq_mul, inv_pow, Function.comp_apply, Nat.cast_ofNat, pow_one]
  ring

theorem boundaryWeight_hessian_lower_bound (K : ℝ) (hK : 0 ≤ K) {x : E}
    (hx : x ∈ Metric.ball (0 : E) 1) (v : E) :
    2 * K * (rho x)⁻¹ ^ 2 * ‖v‖ ^ 2 ≤
      fderiv ℝ (fun y => fderiv ℝ (boundaryWeight K : E → ℝ) y v) x v := by
  rw [second_fderiv_boundaryWeight K hx, real_inner_self_eq_norm_sq]
  have hr := rho_pos hx
  have hh : 0 ≤ 8 * K * (rho x)⁻¹ ^ 3 * inner ℝ x v ^ 2 := by positivity
  nlinarith

theorem norm_fderiv_rho_le_two {x : E} (hx : x ∈ Metric.ball (0 : E) 1) :
    ‖fderiv ℝ (rho : E → ℝ) x‖ ≤ 2 := by
  rw [(hasFDerivAt_rho x).fderiv, norm_neg]
  have hh : ‖x‖ < 1 := by simpa only [Metric.mem_ball, dist_zero_right] using hx
  calc
    _ ≤ (2 : ℝ) * ‖innerSL ℝ x‖ := norm_nsmul_le
    _ ≤ 2 := by rw [innerSL_apply_norm]; linarith

theorem norm_fderiv_boundaryWeight_le (K : ℝ) (hK : 0 ≤ K) {x : E}
    (hx : x ∈ Metric.ball (0 : E) 1) :
    ‖fderiv ℝ (boundaryWeight K : E → ℝ) x‖ ≤ 2 * K * (rho x)⁻¹ ^ 2 := by
  have he : fderiv ℝ (boundaryWeight K : E → ℝ) x =
      (2 * K * (rho x)⁻¹ ^ 2) • innerSL ℝ x := by
    ext v
    exact fderiv_boundaryWeight K hx v
  rw [he, norm_smul, innerSL_apply_norm, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hh0 : ‖x‖ < 1 := by simpa only [Metric.mem_ball, dist_zero_right] using hx
  have hh : ‖x‖ ≤ 1 := hh0.le
  exact mul_le_of_le_one_right (by positivity) hh

end Yau.LeafProofs.L21Aux
