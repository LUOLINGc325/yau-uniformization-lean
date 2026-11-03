import Yau.Proofs.P07DyadicEstimates
import Yau.Proofs.G04LeviForms
import Yau.Blueprint.Analytic

/-! The original controlled exhaustion follows from the produced scaled
cutoff family, with one common constant chosen before all points. -/
noncomputable section
open Set
open scoped Topology ComplexOrder
namespace Yau.NodeProofs.P07Aux
open Yau Yau.Blueprint Yau.LeafProofs.L12Aux Yau.LeafProofs.L18Aux
variable {n : ℕ}

theorem dyadic_sublevels_compact (X : KahlerManifold n) (o : Pt X)
    {v : ℝ → Pt X → ℝ} {D1 D2 : ℝ} (hv : ScaledCutoffFamily X.metric o v D1 D2)
    (c : ℝ) : IsCompact {x | dyadicExhaustion v x ≤ c} := by
  have hu := continuous_of_smoothFn (dyadic_smooth hv)
  apply (isCompact_inducedDistance_sublevel X.metric o (3 * c)).of_isClosed_subset
    (isClosed_le hu continuous_const)
  intro x hx
  have hg := (dyadic_growth hv x).2.1
  change dyadicExhaustion v x ≤ c at hx
  change distFrom X.metric.form o x ≤ 3 * c
  linarith

theorem controlledExhaustion_of_scaledCutoffs (X : KahlerManifold n) (o : Pt X)
    {v : ℝ → Pt X → ℝ} {D1 D2 : ℝ} (hD1 : 0 ≤ D1) (hD2 : 0 ≤ D2)
    (hv : ScaledCutoffFamily X.metric o v D1 D2) :
    ∃ u, ControlledExhaustion X o u := by
  let u := dyadicExhaustion v
  have hu : SmoothFn u := dyadic_smooth hv
  let C := 4 + D1 + 2 * D2
  have hC : 0 < C := by dsimp only [C]; positivity
  have hC3 : 3 ≤ C := by dsimp only [C]; linarith
  have hC2 : 2 ≤ C := by linarith
  have hCD1 : D1 ≤ C := by dsimp only [C]; linarith
  have hCD2 : 2 * D2 ≤ C := by dsimp only [C]; linarith
  refine ⟨u, hu, dyadic_sublevels_compact X o hv, fun x => (dyadic_growth hv x).1, C, hC, ?_⟩
  intro x
  have hg := dyadic_growth hv x
  have hupos : 0 < u x := lt_of_lt_of_le zero_lt_one hg.1
  have hspos : 0 ≤ 1 + distFrom X.metric.form o x := by linarith [X.metric.induced_distance_nonneg o x]
  have hbound : ∀ w : ComplexVector n, |leviDirection (levi u x) w| ≤
      (C / u x) * leviDirection (gMat X.metric.form x) w := by
    intro w
    apply (dyadic_directional_bound hv hD2 x w).trans
    apply mul_le_mul_of_nonneg_right ((div_le_div_iff_of_pos_right hupos).mpr hCD2)
    exact (Complex.nonneg_iff.mp ((Yau.LeafProofs.L12Aux.hMat_posDef X.metric.form x (chartPt x x)
      (mem_extChartAt_target x)).posSemidef.dotProduct_mulVec_nonneg (WithLp.ofLp w))).1
  have hherm := (hermitian_bounds_iff_abs_directional (gMat X.metric.form x) (levi u x)
    (Yau.LeafProofs.L12Aux.hMat_isHermitian X.metric.form x (chartPt x x))
    (G04Aux.levi_hermitian u hu x) (C / u x)).mpr hbound
  refine ⟨?_, ?_, ?_, ?_, hherm.2⟩
  · rw [← div_eq_inv_mul]
    apply (div_le_iff₀ hC).mpr
    nlinarith [hg.1, hg.2.1]
  · exact hg.2.2.trans (mul_le_mul_of_nonneg_right hC2 hspos)
  · exact (dyadic_gradient_bound hv x).trans (by nlinarith)
  · simpa only [Complex.ofReal_div, Complex.ofReal_neg] using hherm.1

end Yau.NodeProofs.P07Aux
