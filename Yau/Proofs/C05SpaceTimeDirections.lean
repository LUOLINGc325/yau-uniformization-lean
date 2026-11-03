import Yau.Proofs.C05MixedDirections

/-! Restrict the true joint derivatives to a fixed spatial chart and a physical
time line. The chart is kept fixed throughout. -/

noncomputable section
open scoped ContDiff Topology
namespace Yau.Proofs.C05Aux
open Filter
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem left_directionalDerivative {f : E × ℝ → F} {z : E} {t : ℝ}
    (hf : DifferentiableAt ℝ f (z, t)) (v : E) :
    directionalDerivative v (fun y => f (y, t)) z =
      directionalDerivative (v, 0) f (z, t) := by
  have hline : HasFDerivAt (fun y : E => (y, t))
      ((ContinuousLinearMap.id ℝ E).prod (0 : E →L[ℝ] ℝ)) z :=
    (hasFDerivAt_id z).prodMk (hasFDerivAt_const t z)
  have hc := hf.hasFDerivAt.comp z hline
  exact congrArg (fun A => A v) hc.fderiv

theorem right_hasDerivAt {f : E × ℝ → F} {z : E} {t : ℝ}
    (hf : DifferentiableAt ℝ f (z, t)) :
    HasDerivAt (fun s => f (z, s)) (directionalDerivative (0, 1) f (z, t)) t := by
  exact hf.hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_const t z).prodMk (hasDerivAt_id t))

theorem second_left_directionalDerivative {f : E × ℝ → F} {z : E} {t : ℝ}
    (hf : ContDiffAt ℝ 2 f (z, t)) (v w : E) :
    fderiv ℝ (fderiv ℝ (fun y => f (y, t))) z v w =
      directionalDerivative (v, 0) (directionalDerivative (w, 0) f) (z, t) := by
  have hleft : ContDiffAt ℝ 2 (fun y => f (y, t)) z :=
    hf.comp z (contDiffAt_id.prodMk contDiffAt_const)
  rw [← directionalDerivative_directionalDerivative hleft w v]
  have he : directionalDerivative w (fun y => f (y, t)) =ᶠ[𝓝 z]
      (fun y => directionalDerivative (w, 0) f (y, t)) := by
    have hh : ∀ᶠ y in 𝓝 z, ContDiffAt ℝ 2 f (y, t) :=
      (show ContinuousAt (fun y : E => (y, t)) z from
        continuousAt_id.prodMk continuousAt_const).eventually (hf.eventually (by norm_num))
    filter_upwards [hh] with y hy
    exact left_directionalDerivative (hy.differentiableAt (by norm_num)) w
  change fderiv ℝ (directionalDerivative w (fun y => f (y, t))) z v = _
  rw [he.fderiv_eq]
  exact left_directionalDerivative
    ((contDiffAt_directionalDerivative hf (m := 1) (by norm_num) (w, 0)).differentiableAt
      one_ne_zero) v

theorem hasDerivAt_second_spatial_derivative {f : E × ℝ → F} {z : E} {t : ℝ}
    (hf : ContDiffAt ℝ 3 f (z, t)) (v w : E) :
    HasDerivAt (fun s => fderiv ℝ (fderiv ℝ (fun y => f (y, s))) z v w)
      (directionalDerivative (v, 0)
        (directionalDerivative (w, 0) (directionalDerivative (0, 1) f)) (z, t)) t := by
  have hdw : ContDiffAt ℝ 2 (directionalDerivative (w, 0) f) (z, t) :=
    contDiffAt_directionalDerivative hf (by norm_num) (w, 0)
  have hdv : ContDiffAt ℝ 1
      (directionalDerivative (v, 0) (directionalDerivative (w, 0) f)) (z, t) :=
    contDiffAt_directionalDerivative hdw (by norm_num) (v, 0)
  have hd := right_hasDerivAt (hdv.differentiableAt one_ne_zero)
  rw [directionalDerivative_third_rotate hf] at hd
  apply hd.congr_of_eventuallyEq
  have hh : ∀ᶠ s in 𝓝 t, ContDiffAt ℝ 3 f (z, s) :=
    (show ContinuousAt (fun s : ℝ => (z, s)) t from
      continuousAt_const.prodMk continuousAt_id).eventually (hf.eventually (by norm_num))
  filter_upwards [hh] with s hs
  exact second_left_directionalDerivative (hs.of_le (by norm_num)) v w

end Yau.Proofs.C05Aux
