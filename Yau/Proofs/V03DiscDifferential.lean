import Yau.Proofs.V03DiscSmooth
import Yau.Proofs.V03EuclideanRadial

/-! Actual closed-disc derivatives transform by the induced cotangent chart
differential. The formula also holds at boundary points via within derivatives. -/

open scoped Manifold Topology ContDiff Matrix ComplexOrder
open Filter

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

variable {n : ℕ} {M : ComplexManifold n}

theorem cotangentDisc_fderivWithin_coords_change {f : ℂ → CotangentPoint M}
    (hf : CotangentDisc f) {ζ : ℂ} (hζ : ζ ∈ Metric.closedBall 0 1)
    (x x' : M.Carrier) (hx : f ζ ∈ cotangentSource x) (hx' : f ζ ∈ cotangentSource x') :
    fderivWithin ℂ (fun η => cotangentChart x' (f η)) (Metric.closedBall 0 1) ζ =
      (fderiv ℂ (fun z => cotangentChart x' (cotangentChartInv x z))
        (cotangentChart x (f ζ))).comp
        (fderivWithin ℂ (fun η => cotangentChart x (f η)) (Metric.closedBall 0 1) ζ) := by
  let c : ℂ → CotangentCoord n := fun η => cotangentChart x (f η)
  let T : CotangentCoord n → CotangentCoord n := fun z => cotangentChart x' (cotangentChartInv x z)
  have hbase : chartInv x (c ζ).1 = (f ζ).1 :=
    (extChartAt (ComplexModel n) x).left_inv hx
  have hT : DifferentiableAt ℂ T (c ζ) :=
    (cotangentChartTransition_contDiffAt x x' (cotangentChart_mapsTo x hx)
      (by rw [hbase]; exact hx')).differentiableAt (by simp)
  have hc : DifferentiableWithinAt ℂ c (Metric.closedBall 0 1) ζ :=
    (cotangentDisc_coords_contDiffWithinAt hf hζ x hx).differentiableWithinAt (by simp)
  have hsource : ∀ᶠ η in 𝓝[Metric.closedBall 0 1] ζ, f η ∈ cotangentSource x :=
    (hf.1 ζ hζ).continuousWithinAt.preimage_mem_nhdsWithin
      ((isOpen_extChartAt_source (I := ComplexModel n) x).mem_nhds hx)
  have heq : (fun η => cotangentChart x' (f η)) =ᶠ[𝓝[Metric.closedBall 0 1] ζ] T ∘ c := by
    filter_upwards [hsource] with η hη
    simp only [Function.comp_apply, T, c, cotangentChart_left_inv x hη]
  rw [heq.fderivWithin_eq_of_mem hζ]
  exact fderiv_comp_fderivWithin ζ hT hc (uniqueDiffOn_complex_closedDisc ζ hζ)

end Yau.Blueprint.V03Proof
