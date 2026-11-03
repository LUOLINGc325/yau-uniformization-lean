import Yau.Proofs.F01MixedWirtingerProduct

/-! At an actual unit coefficient with zero real first jet, the conformal
mixed product has exactly its two second-order terms. -/
noncomputable section
open Set
open scoped ContDiff
namespace Yau.NodeProofs.F01Aux
open Yau

theorem mixed_wirt_mul_of_unit_zero_jet {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f g : E → ℂ) {S : Set E} (hS : IsOpen S)
    (hf : ContDiffOn ℝ ∞ f S) (hg : ContDiffOn ℝ ∞ g S)
    {z : E} (hz : z ∈ S) (hg0 : g z = 1) (hDg : fderiv ℝ g z = 0) (v w : E) :
    wirt (fun y => wirtBar (fun u => f u * g u) y v) z w =
      wirt (fun y => wirtBar f y v) z w +
      f z * wirt (fun y => wirtBar g y v) z w := by
  have hw : wirt g z w = 0 := by unfold wirt; rw [hDg]; simp
  have hb : wirtBar g z v = 0 := by unfold wirtBar; rw [hDg]; simp
  rw [mixed_wirt_mul f g hS hf hg hz v w, hg0, hw, hb]
  ring

end Yau.NodeProofs.F01Aux
