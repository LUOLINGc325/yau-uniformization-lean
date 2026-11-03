import Yau.Proofs.D02HolomorphicLimit
import Yau.Proofs.D02DiscPotentialRegularity

/-! Smooth real functions composed with an actual holomorphic curve are
smooth on its original open domain. -/

open scoped Topology Manifold ContDiff
open Filter Metric Set

noncomputable section
namespace Yau.NodeProofs.D02Aux
open Yau Yau.Blueprint
set_option backward.isDefEq.respectTransparency false

theorem smoothFn_curve_contDiffAt {n : ℕ} {M : ComplexManifold n}
    {u : M.Carrier → ℝ} (hu : SmoothFn u) {f : ℂ → M.Carrier} {z : ℂ}
    (hf : ContMDiffAt 𝓘(ℂ, ℂ) (ComplexModel n) ∞ f z) :
    ContDiffAt ℝ ∞ (fun w => u (f w)) z := by
  let y := f z
  let T : ℂ → ComplexVector n := fun w => chartPt y (f w)
  have hT : ContDiffAt ℂ ∞ T z := ((contMDiffAt_iff_target.mp hf).2).contDiffAt
  have huT : ContDiffAt ℝ ∞ (inChart y u) (T z) :=
    (hu y).contDiffAt ((isOpen_extChartAt_target (I := ComplexModel n) y).mem_nhds
      (mem_extChartAt_target y))
  have hsrc : ∀ᶠ w in 𝓝 z, f w ∈ (extChartAt (ComplexModel n) y).source :=
    hf.continuousAt.preimage_mem_nhds (extChartAt_source_mem_nhds y)
  have he : (fun w => u (f w)) =ᶠ[𝓝 z] (inChart y u) ∘ T := by
    filter_upwards [hsrc] with w hw
    exact (congrArg u ((extChartAt (ComplexModel n) y).left_inv hw)).symm
  exact (huT.comp z (hT.restrict_scalars ℝ)).congr_of_eventuallyEq he

theorem smoothFn_curve_contDiffOn {n : ℕ} {M : ComplexManifold n}
    {u : M.Carrier → ℝ} (hu : SmoothFn u) {O : Set ℂ} (hO : IsOpen O)
    {f : ℂ → M.Carrier} (hf : ContMDiffOn 𝓘(ℂ, ℂ) (ComplexModel n) ∞ f O) :
    ContDiffOn ℝ ∞ (fun z => u (f z)) O :=
  fun z hz => (smoothFn_curve_contDiffAt hu (hf.contMDiffAt (hO.mem_nhds hz))).contDiffWithinAt

end Yau.NodeProofs.D02Aux
