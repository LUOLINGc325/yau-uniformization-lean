import Yau.LeafProofs.L01Proximal
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Group.Bounded

open Set Filter Asymptotics
open scoped Topology InnerProductSpace

namespace Yau.LeafProofs.L01Aux

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The finite scalar envelope of the actual compact proximal minimizer. -/
noncomputable def envelope (f : E → ℝ) (P : E → E) (y : E) : ℝ :=
  ⟪y, P y⟫_ℝ - f (P y) - (1 / 2) * ‖P y‖ ^ 2

theorem primal_eq_of_envelope (f : E → ℝ) (P : E → E) (y : E) :
    f (P y) = ⟪y, P y⟫_ℝ - envelope f P y - (1 / 2) * ‖P y‖ ^ 2 := by
  unfold envelope
  ring

/-- Minimality identifies the envelope as an upper bound for every primal competitor. -/
theorem le_envelope {K : Set E} {f : E → ℝ} {P : E → E}
    (hmin : ∀ y z, z ∈ K → proxCost f y (P y) ≤ proxCost f y z)
    (y : E) {z : E} (hz : z ∈ K) :
    ⟪y, z⟫_ℝ - f z - (1 / 2) * ‖z‖ ^ 2 ≤ envelope f P y := by
  have h := hmin y z hz
  dsimp [proxCost, envelope] at *
  linarith

/-- The envelope has a quadratic first-order error, without differentiating `f`. -/
theorem envelope_remainder_bounds {K : Set E} {f : E → ℝ} {P : E → E}
    (hmem : ∀ y, P y ∈ K)
    (hmin : ∀ y z, z ∈ K → proxCost f y (P y) ≤ proxCost f y z)
    (hLip : LipschitzWith 1 P) (y w : E) :
    0 ≤ envelope f P w - envelope f P y - ⟪P y, w - y⟫_ℝ ∧
    envelope f P w - envelope f P y - ⟪P y, w - y⟫_ℝ ≤ ‖w - y‖ ^ 2 := by
  have h₁ := le_envelope hmin w (hmem y)
  have h₂ := le_envelope hmin y (hmem w)
  have hl : ‖P w - P y‖ ≤ ‖w - y‖ := by
    simpa only [dist_eq_norm, NNReal.coe_one, one_mul] using hLip.dist_le_mul w y
  have hi := (real_inner_le_norm (P w - P y) (w - y)).trans
    (mul_le_mul_of_nonneg_right hl (norm_nonneg (w - y)))
  simp only [inner_sub_left, inner_sub_right] at hi ⊢
  dsimp [envelope] at h₁ h₂ ⊢
  constructor <;>
    nlinarith only [h₁, h₂, hi, real_inner_comm (P y) w, real_inner_comm (P y) y,
      real_inner_comm (P w) w, real_inner_comm (P w) y]

theorem envelope_hasFDerivAt {K : Set E} {f : E → ℝ} {P : E → E}
    (hmem : ∀ y, P y ∈ K)
    (hmin : ∀ y z, z ∈ K → proxCost f y (P y) ≤ proxCost f y z)
    (hLip : LipschitzWith 1 P) (y : E) :
    HasFDerivAt (envelope f P) (innerSL ℝ (P y)) y := by
  apply hasFDerivAt_iff_isLittleO.2
  have hb : (fun w => envelope f P w - envelope f P y - (innerSL ℝ (P y)) (w - y))
      =O[𝓝 y] (fun w => ‖w - y‖ ^ 2) := by
    apply IsBigO.of_bound' (Eventually.of_forall fun w => ?_)
    obtain ⟨h₀, h₁⟩ := envelope_remainder_bounds hmem hmin hLip y w
    simpa only [innerSL_apply_apply, Real.norm_eq_abs, abs_of_nonneg h₀,
      abs_of_nonneg (sq_nonneg ‖w - y‖)] using h₁
  exact hb.trans_isLittleO (isLittleO_pow_sub_sub y (show 1 < 2 by norm_num))

/-- A buffered primal ball gives a radial lower bound for the dual envelope. -/
theorem envelope_sub_inner_lower_bound {K : Set E} {f : E → ℝ} {P : E → E}
    (hmin : ∀ y z, z ∈ K → proxCost f y (P y) ≤ proxCost f y z)
    {z : E} {r M : ℝ} (hr : 0 < r) (hball : Metric.closedBall z r ⊆ K)
    (hbound : ∀ w ∈ K, f w + (1 / 2) * ‖w‖ ^ 2 ≤ M) (y : E) :
    r * ‖y‖ - M ≤ envelope f P y - ⟪z, y⟫_ℝ := by
  by_cases hy : y = 0
  · subst y
    have hz : z ∈ K := hball (Metric.mem_closedBall_self hr.le)
    have h := le_envelope hmin (0 : E) hz
    have hb := hbound z hz
    simp only [inner_zero_left, inner_zero_right, norm_zero, mul_zero, sub_zero] at *
    linarith
  · have hn : 0 < ‖y‖ := norm_pos_iff.mpr hy
    let w := z + (r / ‖y‖) • y
    have hnorm : ‖(r / ‖y‖) • y‖ = r := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos hr hn), div_mul_cancel₀ _ hn.ne']
    have hw : w ∈ K := hball (by
      change dist (z + (r / ‖y‖) • y) z ≤ r
      simpa only [dist_eq_norm, add_sub_cancel_left, hnorm] using le_refl r)
    have hi : ⟪y, w⟫_ℝ = ⟪z, y⟫_ℝ + r * ‖y‖ := by
      dsimp [w]
      rw [inner_add_right, inner_smul_right, real_inner_self_eq_norm_sq, real_inner_comm y z]
      congr 1
      field_simp
    have h := le_envelope hmin y hw
    have hb := hbound w hw
    rw [hi] at h
    linarith

/-- Every interior primal point has a proximal preimage, by finite dual minimization. -/
theorem interior_subset_range_prox [FiniteDimensional ℝ E]
    (K : Set E) (f : E → ℝ) (P : E → E)
    (hK : IsCompact K) (hcont : ContinuousOn f K)
    (hmem : ∀ y, P y ∈ K)
    (hmin : ∀ y z, z ∈ K → proxCost f y (P y) ≤ proxCost f y z)
    (hLip : LipschitzWith 1 P) :
    interior K ⊆ Set.range P := by
  intro z hz
  obtain ⟨r₀, hr₀, hball₀⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hz)
  let r := r₀ / 2
  have hr : 0 < r := half_pos hr₀
  have hball : Metric.closedBall z r ⊆ K :=
    (Metric.closedBall_subset_ball (half_lt_self hr₀)).trans hball₀
  have hg : ContinuousOn (fun w => f w + (1 / 2) * ‖w‖ ^ 2) K :=
    hcont.add (continuousOn_const.mul (continuous_norm.continuousOn.pow 2))
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hg
  let M := |C| + 1
  have hM : 0 < M := by dsimp [M]; positivity
  have hbound (w : E) (hw : w ∈ K) : |f w + (1 / 2) * ‖w‖ ^ 2| ≤ M := by
    have h := hC w hw
    rw [Real.norm_eq_abs] at h
    exact h.trans (by dsimp [M]; linarith [le_abs_self C])
  let J : E → ℝ := fun y => envelope f P y - ⟪z, y⟫_ℝ
  have hJ (y : E) : HasFDerivAt J (innerSL ℝ (P y) - innerSL ℝ z) y :=
    (envelope_hasFDerivAt hmem hmin hLip y).sub (innerSL ℝ z).hasFDerivAt
  have hJcont : Continuous J := continuous_iff_continuousAt.mpr fun y => (hJ y).continuousAt
  have hlo (y : E) : r * ‖y‖ - M ≤ J y :=
    envelope_sub_inner_lower_bound hmin hr hball
      (fun w hw => (le_abs_self _).trans (hbound w hw)) y
  have hzero : J 0 ≤ M := by
    have hb := neg_le_of_abs_le (hbound (P 0) (hmem 0))
    dsimp [J, envelope]
    simp only [inner_zero_left, inner_zero_right, sub_zero]
    linarith
  let R := (2 * M + 1) / r
  have hR : 0 < R := div_pos (by linarith) hr
  have hrR : r * R = 2 * M + 1 := by dsimp [R]; field_simp
  obtain ⟨q, hq, hqmin⟩ := (isCompact_closedBall (0 : E) R).exists_isMinOn
    ⟨0, Metric.mem_closedBall_self hR.le⟩ hJcont.continuousOn
  have hqzero : J q ≤ J 0 := hqmin (Metric.mem_closedBall_self hR.le)
  have hqin : q ∈ Metric.ball (0 : E) R := by
    rw [Metric.mem_ball, dist_zero_right]
    by_contra h
    have hnorm : R ≤ ‖q‖ := le_of_not_gt h
    have hmul := mul_le_mul_of_nonneg_left hnorm hr.le
    have hlow := hlo q
    nlinarith
  have hlocal : IsLocalMin J q := hqmin.isLocalMin
    (mem_of_superset (Metric.isOpen_ball.mem_nhds hqin) Metric.ball_subset_closedBall)
  have hderivzero := hlocal.hasFDerivAt_eq_zero (hJ q)
  have heval := congrArg (fun L : E →L[ℝ] ℝ => L (P q - z)) hderivzero
  have hinner : ⟪P q - z, P q - z⟫_ℝ = 0 := by
    simpa only [sub_apply, innerSL_apply_apply,
      zero_apply, inner_sub_left] using heval
  exact ⟨q, sub_eq_zero.mp (inner_self_eq_zero.mp hinner)⟩

end Yau.LeafProofs.L01Aux
