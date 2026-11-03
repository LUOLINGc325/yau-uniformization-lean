import Yau.Proofs.F04SubcaloricUniqueness
import Yau.Proofs.F04SmoothPositiveLimit
import Yau.Proofs.F04LaplacianLinear

open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold

noncomputable section

namespace Yau.F04Proof

open Yau.Blueprint Yau.LeafProofs.L18Aux

variable {n : ℕ} {M : ComplexManifold n}

theorem smoothSpaceTime_timeSlice_contDiffOn
    {I : Set ℝ} {w : M.Carrier → ℝ → ℝ} (hw : SmoothSpaceTime w I) (x : M.Carrier) :
    ContDiffOn ℝ ∞ (w x) I := by
  have h := (hw x).comp ((contDiffOn_const (c := chartPt x x)).prodMk contDiffOn_id)
    (fun _ ht => ⟨mem_extChartAt_target x, ht⟩)
  have hinv : chartInv x (chartPt x x) = x :=
    Yau.LeafProofs.chartInv_chartPt_of_mem x x (mem_chart_source _ _)
  simpa only [Function.comp_def, hinv, id_eq] using h

theorem smoothPositive_second_deriv_nonneg {δ : ℝ} (hδ : 0 < δ) (s : ℝ) :
    0 ≤ deriv (deriv (smoothPositive δ)) s := by
  have hm : Monotone (fun q : ℝ => Real.smoothTransition (q / δ)) :=
    Real.smoothTransition.monotone.comp (fun _ _ h => div_le_div_of_nonneg_right h hδ.le)
  have he : deriv (smoothPositive δ) = (fun q => Real.smoothTransition (q / δ)) :=
    funext (smoothPositive_deriv δ)
  rw [he]
  exact hm.deriv_nonneg

theorem heatOp_sub_smooth {X : KahlerManifold n} (h : Flow X)
    {T : ℝ} (hT : 0 < T) {u v : STF X}
    (hu : SmoothSpaceTime u (Icc 0 T)) (hv : SmoothSpaceTime v (Icc 0 T))
    (x : Pt X) {t : ℝ} (ht : t ∈ Icc 0 T) :
    heatOp h (Icc 0 T) (fun y s => u y s - v y s) x t =
      heatOp h (Icc 0 T) u x t - heatOp h (Icc 0 T) v x t := by
  have hud := ((smoothSpaceTime_timeSlice_contDiffOn hu x).differentiableOn (by simp) t ht).hasDerivWithinAt
  have hvd := ((smoothSpaceTime_timeSlice_contDiffOn hv x).differentiableOn (by simp) t ht).hasDerivWithinAt
  have he := (hud.sub hvd).derivWithin (uniqueDiffOn_Icc hT t ht)
  unfold heatOp
  change derivWithin (u x - v x) (Icc 0 T) t -
    laplacian (h t) (fun y => u y t - v y t) x = _
  rw [he, laplacian_sub_smooth (h t) ((smoothSpaceTime_c1 hu).1 t ht)
    ((smoothSpaceTime_c1 hv).1 t ht)]
  ring

/-- Convex smooth positive parts preserve the actual subcaloric inequality,
 including within derivatives at both original time faces. -/
theorem smoothPositive_subcaloric {X : KahlerManifold n} (h : Flow X)
    {T : ℝ} (hT : 0 < T) {w : STF X} (hw : SmoothSpaceTime w (Icc 0 T))
    {δ : ℝ} (hδ : 0 < δ)
    (hcal : ∀ x t, t ∈ Icc 0 T → heatOp h (Icc 0 T) w x t ≤ 0) :
    ∀ x t, t ∈ Icc 0 T →
      heatOp h (Icc 0 T) (fun y s => smoothPositive δ (w y s)) x t ≤ 0 := by
  intro x t ht
  have hwd := ((smoothSpaceTime_timeSlice_contDiffOn hw x).differentiableOn (by simp) t ht).hasDerivWithinAt
  have hd := ((smoothPositive_hasDerivAt δ (w x t)).comp_hasDerivWithinAt t hwd).derivWithin
    (uniqueDiffOn_Icc hT t ht)
  rw [← smoothPositive_deriv δ (w x t)] at hd
  have hp := mul_nonpos_of_nonneg_of_nonpos (smoothPositive_deriv_bounds δ (w x t)).1 (hcal x t ht)
  have hq := mul_nonneg (smoothPositive_second_deriv_nonneg hδ (w x t))
    (scalarGradientPair_self_nonneg (h t) (fun y => w y t) x)
  unfold heatOp at hp ⊢
  change derivWithin (smoothPositive δ ∘ w x) (Icc 0 T) t -
    laplacian (h t) (fun y => smoothPositive δ (w y t)) x ≤ 0
  rw [hd, laplacian_scalar_comp (h t) ((smoothSpaceTime_c1 hw).1 t ht)
    (smoothPositive δ) x ((smoothPositive_contDiff δ).contDiffAt.of_le (by simp))]
  nlinarith only [hp, hq]

end Yau.F04Proof
