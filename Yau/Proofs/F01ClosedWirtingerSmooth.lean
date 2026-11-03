import Yau.Proofs.F01ClosedSpatialDerivative
import Yau.Proofs.F01SpaceTimeWirtingerSmooth

/-! The actual spatial Wirtinger and Levi jets remain jointly smooth
at both time faces, using the original within derivative on the slab. -/
noncomputable section
open Set
open scoped ContDiff
namespace Yau.NodeProofs.F01Aux
open Yau
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem closed_slab_wirt_smooth {F : E × ℝ → ℂ}
    {S : Set E} {I : Set ℝ} (hS : IsOpen S) (hI : UniqueDiffOn ℝ I)
    (hF : ContDiffOn ℝ ∞ F (S ×ˢ I)) (v : E) :
    ContDiffOn ℝ ∞ (spaceTimeWirt F v) (S ×ˢ I) := by
  have hA := closed_slab_space_direction_smooth hS hI hF v
  have hB := closed_slab_space_direction_smooth hS hI hF (Complex.I • v)
  exact contDiffOn_const.mul (hA.sub (contDiffOn_const.mul hB))

theorem closed_slab_wirtBar_smooth {F : E × ℝ → ℂ}
    {S : Set E} {I : Set ℝ} (hS : IsOpen S) (hI : UniqueDiffOn ℝ I)
    (hF : ContDiffOn ℝ ∞ F (S ×ˢ I)) (v : E) :
    ContDiffOn ℝ ∞ (spaceTimeWirtBar F v) (S ×ˢ I) := by
  have hA := closed_slab_space_direction_smooth hS hI hF v
  have hB := closed_slab_space_direction_smooth hS hI hF (Complex.I • v)
  exact contDiffOn_const.mul (hA.add (contDiffOn_const.mul hB))

theorem closed_slab_leviC_smooth {n : ℕ} {F : ComplexVector n × ℝ → ℝ}
    {S : Set (ComplexVector n)} {I : Set ℝ} (hS : IsOpen S)
    (hI : UniqueDiffOn ℝ I) (hF : ContDiffOn ℝ ∞ F (S ×ˢ I)) (i j : Fin n) :
    ContDiffOn ℝ ∞ (fun p : ComplexVector n × ℝ =>
      leviC (fun z => F (z, p.2)) p.1 i j) (S ×ˢ I) := by
  have hc : ContDiffOn ℝ ∞ (fun p => (F p : ℂ)) (S ×ˢ I) :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn hF
  exact closed_slab_wirt_smooth hS hI
    (closed_slab_wirtBar_smooth hS hI hc (stdVec i)) (stdVec j)

end Yau.NodeProofs.F01Aux
