import Yau.Proofs.P07DyadicValues
import Yau.Proofs.P07LocalCalculus
import Yau.Proofs.P07MatrixOrder

/-! Smoothness and all quantitative estimates of the actual dyadic sum. -/
noncomputable section
open Filter Set
open scoped Topology ContDiff ComplexOrder
namespace Yau.NodeProofs.P07Aux
open Yau Yau.Blueprint Yau.LeafProofs.L12Aux Yau.LeafProofs.L18Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem dyadic_smooth {g : SmoothMetric M} {o : M.Carrier}
    {v : ℝ → M.Carrier → ℝ} {D1 D2 : ℝ} (hv : ScaledCutoffFamily g o v D1 D2) :
    SmoothFn (dyadicExhaustion v) := by
  apply smoothFn_of_locally_smooth
  intro x
  obtain ⟨k, _, _, heq⟩ := dyadic_exists_local_formula hv x
  refine ⟨(fun y => (2 : ℝ) ^ k * (1 + v ((2 : ℝ) ^ k) y)), ?_, heq⟩
  intro a
  exact contDiffOn_const.mul (contDiffOn_const.add ((hv _ (by positivity)).1 a))

theorem dyadic_growth {g : SmoothMetric M} {o : M.Carrier}
    {v : ℝ → M.Carrier → ℝ} {D1 D2 : ℝ} (hv : ScaledCutoffFamily g o v D1 D2)
    (x : M.Carrier) : 1 ≤ dyadicExhaustion v x ∧
      (1 + distFrom g.form o x) / 3 ≤ dyadicExhaustion v x ∧
      dyadicExhaustion v x ≤ 2 * (1 + distFrom g.form o x) := by
  obtain ⟨k, hlo, hhi, heq⟩ := dyadic_exists_local_formula hv x
  have he := heq.eq_of_nhds
  have hrange := ((hv ((2 : ℝ) ^ k) (by positivity)).2 x).1
  have hL : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
  have hsmall : (2 : ℝ) ^ k ≤ dyadicExhaustion v x := by
    rw [he]
    nlinarith [hrange.1]
  have hlarge : dyadicExhaustion v x ≤ 2 * (2 : ℝ) ^ k := by
    rw [he]
    nlinarith [hrange.2]
  have hd : 0 ≤ distFrom g.form o x := g.induced_distance_nonneg o x
  refine ⟨hL.trans hsmall, by linarith, ?_⟩
  rcases hlo with hk | hk
  · subst k
    norm_num at hlarge
    linarith
  · linarith

theorem dyadic_gradient_bound {g : SmoothMetric M} {o : M.Carrier}
    {v : ℝ → M.Carrier → ℝ} {D1 D2 : ℝ} (hv : ScaledCutoffFamily g o v D1 D2)
    (x : M.Carrier) : gradNormSq g.form (dyadicExhaustion v) x ≤ D1 ^ 2 := by
  obtain ⟨k, _, _, heq⟩ := dyadic_exists_local_formula hv x
  have hL : 0 < (2 : ℝ) ^ k := by positivity
  have haff : dyadicExhaustion v =ᶠ[𝓝 x] fun y => (2 : ℝ) ^ k * v ((2 : ℝ) ^ k) y + (2 : ℝ) ^ k := by
    filter_upwards [heq] with y hy
    rw [hy]
    ring
  rw [gradNormSq_congr_of_eventuallyEq g.form haff,
    gradNormSq_affine g.form (hv _ hL).1]
  have hb := mul_le_mul_of_nonneg_left (((hv _ hL).2 x).2.2.2.1) (sq_nonneg ((2 : ℝ) ^ k))
  have he : ((2 : ℝ) ^ k) ^ 2 * (D1 / (2 : ℝ) ^ k) ^ 2 = D1 ^ 2 := by field_simp
  exact hb.trans_eq he

theorem dyadic_directional_bound {g : SmoothMetric M} {o : M.Carrier}
    {v : ℝ → M.Carrier → ℝ} {D1 D2 : ℝ} (hv : ScaledCutoffFamily g o v D1 D2)
    (hD2 : 0 ≤ D2) (x : M.Carrier) (w : ComplexVector n) :
    |leviDirection (levi (dyadicExhaustion v) x) w| ≤
      (2 * D2 / dyadicExhaustion v x) * leviDirection (gMat g.form x) w := by
  obtain ⟨k, _, _, heq⟩ := dyadic_exists_local_formula hv x
  have hL : 0 < (2 : ℝ) ^ k := by positivity
  have haff : dyadicExhaustion v =ᶠ[𝓝 x] fun y => (2 : ℝ) ^ k * v ((2 : ℝ) ^ k) y + (2 : ℝ) ^ k := by
    filter_upwards [heq] with y hy
    rw [hy]
    ring
  rw [Yau.LeafProofs.L22Aux.levi_congr_of_eventuallyEq haff,
    leviDirection_affine (hv _ hL).1, abs_mul, abs_of_pos hL]
  have hb := mul_le_mul_of_nonneg_left (((hv _ hL).2 x).2.2.2.2 w) hL.le
  have hc : (2 : ℝ) ^ k * (D2 / ((2 : ℝ) ^ k) ^ 2) = D2 / (2 : ℝ) ^ k := by field_simp
  rw [← mul_assoc, hc] at hb
  apply hb.trans
  have hu : 0 < dyadicExhaustion v x := lt_of_lt_of_le zero_lt_one (dyadic_growth hv x).1
  have hval := heq.eq_of_nhds
  have hrange := ((hv _ hL).2 x).1
  have hub : dyadicExhaustion v x ≤ 2 * (2 : ℝ) ^ k := by rw [hval]; nlinarith [hrange.2]
  have hratio : D2 / (2 : ℝ) ^ k ≤ 2 * D2 / dyadicExhaustion v x := by
    apply (div_le_div_iff₀ hL hu).mpr
    nlinarith
  exact mul_le_mul_of_nonneg_right hratio
    ((Complex.nonneg_iff.mp ((Yau.LeafProofs.L12Aux.hMat_posDef g.form x (chartPt x x)
      (mem_extChartAt_target x)).posSemidef.dotProduct_mulVec_nonneg (WithLp.ofLp w))).1)

end Yau.NodeProofs.P07Aux
