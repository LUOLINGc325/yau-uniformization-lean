import Yau.Proofs.F03MovingBumpWeight

/-! Actual straight moving centres and their compact chart-tube margins. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace Yau.Proofs.F03Aux
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def straightMovingCenter (x y : E) (T : ℝ) (t : ℝ) : E := x+(t/T) • (y-x)

theorem straightMovingCenter_smooth (x y : E) (T : ℝ) :
    ContDiff ℝ ∞ (straightMovingCenter x y T) := by
  unfold straightMovingCenter
  fun_prop

theorem straightMovingCenter_zero (x y : E) (T : ℝ) : straightMovingCenter x y T 0=x := by
  simp only [straightMovingCenter,zero_div,zero_smul,add_zero]

theorem straightMovingCenter_terminal (x y : E) {T : ℝ} (hT : T ≠ 0) :
    straightMovingCenter x y T T=y := by
  simp only [straightMovingCenter,div_self hT,one_smul,add_sub_cancel]

theorem straightMovingCenter_hasDerivAt (x y : E) (T t : ℝ) :
    HasDerivAt (straightMovingCenter x y T) (T⁻¹ • (y-x)) t := by
  change HasDerivAt (fun τ : ℝ => x+(τ/T) • (y-x)) (T⁻¹ • (y-x)) t
  simpa only [one_div,id_eq] using
    (((hasDerivAt_id t).div_const T).smul_const (y-x)).const_add x

theorem straightMovingCenter_mem_closedBall (x y o : E) {r T t : ℝ} (hT : 0 < T)
    (hx : x ∈ Metric.closedBall o r) (hy : y ∈ Metric.closedBall o r) (ht : t ∈ Icc (0 : ℝ) T) :
    straightMovingCenter x y T t ∈ Metric.closedBall o r := by
  have hθ0 : 0 ≤ t/T := div_nonneg ht.1 hT.le
  have hθ1 : t/T ≤ 1 := (div_le_one hT).mpr ht.2
  exact (convex_closedBall o r).add_smul_sub_mem hx hy ⟨hθ0,hθ1⟩

theorem straightMovingCenter_tube_margin (x y o : E) {r R T t : ℝ} (hT : 0 < T)
    (hx : x ∈ Metric.closedBall o (r/2)) (hy : y ∈ Metric.closedBall o (r/2))
    (hR : R ≤ r/2) (ht : t ∈ Icc (0 : ℝ) T) {z : E} (hz : z ∉ Metric.ball o r) :
    R ≤ ‖z-straightMovingCenter x y T t‖ := by
  have hc := straightMovingCenter_mem_closedBall x y o hT hx hy ht
  rw [Metric.mem_closedBall,dist_eq_norm] at hc
  have hz' : r ≤ ‖z-o‖ := by simpa only [Metric.mem_ball,dist_eq_norm,not_lt] using hz
  have htri := norm_add_le (z-straightMovingCenter x y T t) (straightMovingCenter x y T t-o)
  rw [sub_add_sub_cancel] at htri
  linarith only [hc,hz',htri,hR]

theorem exists_movingBump_amplitude {m : ℝ} (hm : 0 < m) (R : ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ ε*R^6 ≤ m := by
  have hden : 0 < R^6+1 := by positivity
  refine ⟨m/(R^6+1),div_pos hm hden,?_⟩
  rw [div_mul_eq_mul_div,div_le_iff₀ hden]
  nlinarith only [hm]

end Yau.Proofs.F03Aux
