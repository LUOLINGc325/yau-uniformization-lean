import spec.CHAIN.HeatScalarTargets
import Yau.LeafProofs.L18

/-! Chart-pair smoothness gives the same kernel's actual spatial and time smoothness. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold
namespace Yau.Proofs.F03Aux
open Yau HeatConcreteBindings LeafProofs.L18Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

theorem kernelSmooth_univ_smoothSpaceTime (H : ℝ → M.Carrier → M.Carrier → ℝ)
    (hH : KernelSmoothOn univ H) (y : M.Carrier) :
    SmoothSpaceTime (fun x t => H t x y) (Ioi (0 : ℝ)) := by
  intro a
  have hinv : chartInv y (chartPt y y)=y :=
    (extChartAt (ComplexModel n) y).left_inv (mem_extChartAt_source y)
  have hPhi : ContDiff ℝ ∞ (fun q : Parabolic.Point n => ((q.1,chartPt y y),q.2)) := by fun_prop
  have hComp := (hH a y).comp hPhi.contDiffOn
    (show MapsTo (fun q : Parabolic.Point n => ((q.1,chartPt y y),q.2))
      (chartTarget a ×ˢ Ioi (0 : ℝ)) _ from
      fun q hq => ⟨⟨⟨hq.1,mem_univ _⟩,⟨mem_extChartAt_target y,mem_univ _⟩⟩,hq.2⟩)
  simpa only [Function.comp_def,hinv] using hComp

theorem kernelSmooth_univ_smoothFn_left (H : ℝ → M.Carrier → M.Carrier → ℝ)
    (hH : KernelSmoothOn univ H) {t : ℝ} (ht : 0 < t) (y : M.Carrier) :
    SmoothFn (fun x => H t x y) := by
  intro a
  exact (kernelSmooth_univ_smoothSpaceTime H hH y a).comp
    (contDiffOn_id.prodMk contDiffOn_const) (fun z hz => ⟨hz,ht⟩)

theorem kernelSmooth_univ_smoothFn_right (H : ℝ → M.Carrier → M.Carrier → ℝ)
    (hH : KernelSmoothOn univ H) {t : ℝ} (ht : 0 < t) (x : M.Carrier) :
    SmoothFn (H t x) := by
  intro a
  change ContDiffOn ℝ ∞ (fun z : ComplexVector n => H t x (chartInv a z)) (chartTarget a)
  have hinv : chartInv x (chartPt x x)=x :=
    (extChartAt (ComplexModel n) x).left_inv (mem_extChartAt_source x)
  have hPhi : ContDiff ℝ ∞ (fun z : ComplexVector n => ((chartPt x x,z),t)) := by fun_prop
  have hComp := (hH x a).comp hPhi.contDiffOn
    (show MapsTo (fun z : ComplexVector n => ((chartPt x x,z),t)) (chartTarget a) _ from
      fun z hz => ⟨⟨⟨mem_extChartAt_target x,mem_univ _⟩,⟨hz,mem_univ _⟩⟩,ht⟩)
  simpa only [Function.comp_def,hinv] using hComp

theorem kernelSmooth_univ_continuous_left (H : ℝ → M.Carrier → M.Carrier → ℝ)
    (hH : KernelSmoothOn univ H) {t : ℝ} (ht : 0 < t) (y : M.Carrier) :
    Continuous (fun x => H t x y) := continuous_of_smoothFn (kernelSmooth_univ_smoothFn_left H hH ht y)

theorem kernelSmooth_univ_continuous_right (H : ℝ → M.Carrier → M.Carrier → ℝ)
    (hH : KernelSmoothOn univ H) {t : ℝ} (ht : 0 < t) (x : M.Carrier) :
    Continuous (H t x) := continuous_of_smoothFn (kernelSmooth_univ_smoothFn_right H hH ht x)

end Yau.Proofs.F03Aux
