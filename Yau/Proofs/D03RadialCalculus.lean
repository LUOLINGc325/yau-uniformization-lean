import Yau.Proofs.D03Radial

open scoped Manifold Topology ContDiff ENNReal
open MeasureTheory Set Filter

noncomputable section

namespace Yau.Proofs.D03Aux
open Yau Yau.Blueprint Yau.Blueprint.BundlePresentation

private def normSqRealDerivative (z : ℂ) : ℂ →L[ℝ] ℝ :=
  (2 * z.re) • Complex.reCLM + (2 * z.im) • Complex.imCLM

private theorem normSq_hasFDerivAt (z : ℂ) :
    HasFDerivAt (fun w : ℂ => ‖w‖ ^ 2) (normSqRealDerivative z) z := by
  convert (Complex.reCLM.hasFDerivAt (x := z)).pow 2 |>.add
    ((Complex.imCLM.hasFDerivAt (x := z)).pow 2) using 1
  · ext w
    change ‖w‖ ^ 2 = w.re ^ 2 + w.im ^ 2
    rw [Complex.sq_norm]
    simp [Complex.normSq_apply, pow_two]
  · simp [normSqRealDerivative]

/-- Radial first derivative, computed from the real Fréchet definition. -/
theorem wirtBar_normSq_comp (H : ℝ → ℝ) {z : ℂ} {d : ℝ}
    (hH : HasDerivAt H d (‖z‖ ^ 2)) :
    wirtBar (fun w : ℂ => (H (‖w‖ ^ 2) : ℂ)) z 1 = (d : ℂ) * z := by
  have hd := Complex.ofRealCLM.hasFDerivAt.comp z
    (hH.comp_hasFDerivAt z (normSq_hasFDerivAt z))
  change HasFDerivAt (fun w : ℂ => (H (‖w‖ ^ 2) : ℂ)) _ z at hd
  unfold wirtBar
  rw [hd.fderiv]
  apply Complex.ext <;> simp [normSqRealDerivative, Complex.real_smul] <;> ring

/-- Radial complex derivative, with the same real differentiability hypothesis. -/
theorem wirt_normSq_comp (H : ℝ → ℝ) {z : ℂ} {d : ℝ}
    (hH : HasDerivAt H d (‖z‖ ^ 2)) :
    wirt (fun w : ℂ => (H (‖w‖ ^ 2) : ℂ)) z 1 = (d : ℂ) * star z := by
  have hd := Complex.ofRealCLM.hasFDerivAt.comp z
    (hH.comp_hasFDerivAt z (normSq_hasFDerivAt z))
  change HasFDerivAt (fun w : ℂ => (H (‖w‖ ^ 2) : ℂ)) _ z at hd
  unfold wirt
  rw [hd.fderiv]
  apply Complex.ext <;> simp [normSqRealDerivative, Complex.real_smul] <;> ring

theorem wirt_eventuallyEq {f g : ℂ → ℂ} {z : ℂ} (h : f =ᶠ[𝓝 z] g) :
    wirt f z 1 = wirt g z 1 := by
  unfold wirt
  rw [h.fderiv_eq]

theorem wirtBar_eventuallyEq {f g : ℂ → ℂ} {z : ℂ} (h : f =ᶠ[𝓝 z] g) :
    wirtBar f z 1 = wirtBar g z 1 := by
  unfold wirtBar
  rw [h.fderiv_eq]

/-- The genuine complex Hessian of a radial function away from zero. -/
theorem levi_normSq_comp (H H' : ℝ → ℝ) {z : ℂ} (hz : z ≠ 0) {d : ℝ}
    (hH : ∀ u : ℝ, 0 < u → HasDerivAt H (H' u) u)
    (hH' : HasDerivAt H' d (‖z‖ ^ 2)) :
    wirt (fun w : ℂ => wirtBar (fun v : ℂ => (H (‖v‖ ^ 2) : ℂ)) w 1) z 1 =
      ((d * ‖z‖ ^ 2 + H' (‖z‖ ^ 2) : ℝ) : ℂ) := by
  have he : (fun w : ℂ => wirtBar (fun v : ℂ => (H (‖v‖ ^ 2) : ℂ)) w 1) =ᶠ[𝓝 z]
      (fun w : ℂ => (H' (‖w‖ ^ 2) : ℂ) * w) := by
    filter_upwards [eventually_ne_nhds hz] with w hw
    exact wirtBar_normSq_comp H (hH _ (sq_pos_of_pos (norm_pos_iff.mpr hw)))
  rw [wirt_eventuallyEq he]
  have hd := (Complex.ofRealCLM.hasFDerivAt.comp z
    (hH'.comp_hasFDerivAt z (normSq_hasFDerivAt z))).mul (hasFDerivAt_id z)
  change HasFDerivAt (fun w : ℂ => (H' (‖w‖ ^ 2) : ℂ) * w) _ z at hd
  unfold wirt
  rw [hd.fderiv]
  apply Complex.ext <;> simp [normSqRealDerivative, Complex.real_smul,
    Complex.sq_norm, Complex.normSq_apply] <;> ring

end Yau.Proofs.D03Aux
