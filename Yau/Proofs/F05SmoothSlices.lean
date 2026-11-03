import Yau.Geometry.Calculus

/-! Smooth space-time fields have their actual smooth time slices at every
manifold point, including a closed initial face. -/

open Set
open scoped ContDiff Manifold
noncomputable section
namespace Yau.Proofs.F05Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem F05_smooth_time_slice {I : Set ℝ} {p : M.Carrier → ℝ → ℝ}
    (hp : SmoothSpaceTime p I) (x : M.Carrier) : ContDiffOn ℝ ∞ (p x) I := by
  have hCenter : chartInv x (chartPt x x) = x :=
    (extChartAt (ComplexModel n) x).left_inv (mem_extChartAt_source x)
  have hh := (hp x).comp
    (contDiffOn_const.prodMk contDiffOn_id : ContDiffOn ℝ ∞
      (fun t : ℝ => (chartPt x x,t)) I)
    (fun t ht => ⟨mem_extChartAt_target x,ht⟩)
  simpa only [Function.comp_def,hCenter] using hh

end Yau.Proofs.F05Aux
