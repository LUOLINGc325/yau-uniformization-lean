import Mathlib.Analysis.Convex.Strong
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FunProp

open Set Filter
open scoped Topology InnerProductSpace

namespace Yau.LeafProofs.L01Aux

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The compact proximal cost; only values of `f` on the compact domain enter. -/
noncomputable def proxCost (f : E → ℝ) (y z : E) : ℝ :=
  f z + (1 / 2) * ‖z‖ ^ 2 - ⟪y, z⟫_ℝ

/-- Strong convexity upgrades an attained minimum to a quadratic lower bound. -/
theorem strong_minimum_lower_bound {K : Set E} {F : E → ℝ}
    (hc : StrongConvexOn K 1 F) {p : E} (hp : p ∈ K)
    (hmin : IsMinOn F K p) {z : E} (hz : z ∈ K) :
    F p + (1 / 2) * ‖z - p‖ ^ 2 ≤ F z := by
  have happrox (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
      F p + (1 - t) / 2 * ‖z - p‖ ^ 2 ≤ F z := by
    have hmem : (1 - t) • p + t • z ∈ K :=
      hc.1 hp hz (by linarith [ht.2]) ht.1.le (by ring)
    have hsc := hc.2 hp hz (show 0 ≤ 1 - t by linarith [ht.2]) ht.1.le
      (show 1 - t + t = 1 by ring)
    have hm : F p ≤ F ((1 - t) • p + t • z) := hmin hmem
    simp only [smul_eq_mul] at hsc
    rw [norm_sub_rev p z] at hsc
    apply (mul_le_mul_iff_right₀ ht.1).mp
    nlinarith [hsc, hm]
  have hlim : Tendsto (fun t : ℝ => F p + (1 - t) / 2 * ‖z - p‖ ^ 2)
      (𝓝[>] 0) (𝓝 (F p + (1 / 2) * ‖z - p‖ ^ 2)) := by
    have h : Continuous (fun t : ℝ => F p + (1 - t) / 2 * ‖z - p‖ ^ 2) := by
      fun_prop
    simpa using (h.continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds
  apply le_of_tendsto hlim
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t ht
  exact happrox t ht

theorem proxCost_strongConvexOn {K : Set E} {f : E → ℝ}
    (hc : ConvexOn ℝ K f) (y : E) : StrongConvexOn K 1 (proxCost f y) := by
  apply strongConvexOn_iff_convex.2
  convert hc.sub ((innerSL ℝ y).toLinearMap.concaveOn hc.1) using 1
  ext z
  simp only [proxCost, Pi.sub_apply, ContinuousLinearMap.coe_coe, innerSL_apply_apply]
  ring

/-- The two quadratic minimum inequalities give firm nonexpansiveness. -/
theorem firm_of_proximal_minimum {K : Set E} {f : E → ℝ} {P : E → E}
    (hmem : ∀ y, P y ∈ K)
    (hstrong : ∀ y z, z ∈ K →
      proxCost f y (P y) + (1 / 2) * ‖z - P y‖ ^ 2 ≤ proxCost f y z) :
    ∀ y w, ‖P y - P w‖ ^ 2 ≤ ⟪P y - P w, y - w⟫_ℝ := by
  intro y w
  have hy := hstrong y (P w) (hmem w)
  have hw := hstrong w (P y) (hmem y)
  rw [norm_sub_rev (P w) (P y)] at hy
  simp only [proxCost] at hy hw
  simp only [inner_sub_left, inner_sub_right]
  nlinarith only [hy, hw, real_inner_comm y (P y), real_inner_comm y (P w),
    real_inner_comm w (P y), real_inner_comm w (P w)]

/-- A firm self-map is globally nonexpansive. -/
theorem lipschitzWith_one_of_firm {P : E → E}
    (hfirm : ∀ y w, ‖P y - P w‖ ^ 2 ≤ ⟪P y - P w, y - w⟫_ℝ) :
    LipschitzWith 1 P := by
  refine LipschitzWith.of_dist_le_mul fun y w => ?_
  simp only [dist_eq_norm, NNReal.coe_one, one_mul]
  have h := (hfirm y w).trans (real_inner_le_norm (P y - P w) (y - w))
  nlinarith [norm_nonneg (P y - P w), norm_nonneg (y - w)]

/-- Compact minimization constructs a proximal map with its quantitative estimates. -/
theorem exists_proximal
    (K : Set E) (f : E → ℝ)
    (hK : IsCompact K) (hne : K.Nonempty)
    (hc : ConvexOn ℝ K f) (hcont : ContinuousOn f K) :
    ∃ P : E → E,
      (∀ y, P y ∈ K) ∧
      (∀ y z, z ∈ K →
        proxCost f y (P y) + (1 / 2) * ‖z - P y‖ ^ 2 ≤ proxCost f y z) ∧
      (∀ y w, ‖P y - P w‖ ^ 2 ≤ ⟪P y - P w, y - w⟫_ℝ) ∧
      LipschitzWith 1 P := by
  classical
  have hcost (y : E) : ContinuousOn (proxCost f y) K := by
    unfold proxCost
    exact (hcont.add (continuousOn_const.mul (continuous_norm.continuousOn.pow 2))).sub
      (continuous_const.inner continuous_id).continuousOn
  choose P hmem hmin using fun y => hK.exists_isMinOn hne (hcost y)
  have hstrong : ∀ y z, z ∈ K →
      proxCost f y (P y) + (1 / 2) * ‖z - P y‖ ^ 2 ≤ proxCost f y z := by
    intro y z hz
    exact strong_minimum_lower_bound (proxCost_strongConvexOn hc y) (hmem y) (hmin y) hz
  have hfirm := firm_of_proximal_minimum hmem hstrong
  exact ⟨P, hmem, hstrong, hfirm, lipschitzWith_one_of_firm hfirm⟩

end Yau.LeafProofs.L01Aux
