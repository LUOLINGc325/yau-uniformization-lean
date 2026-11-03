import Yau.Proofs.F01SpatialWordCalculus
import Yau.Proofs.F01SpatialThirdCommutation

/-! The actual Hessian of each successive spatial word is the genuine
spatial derivative of the preceding Hessian. This identifies the lower
jets in the explicit linear commutator expansion. -/
noncomputable section
open Set
open scoped ContDiff
namespace Yau.NodeProofs.F01Aux
variable {E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem spatial_word_hessian_direction {u : E × ℝ → F} {S : Set E} {t : ℝ}
    (hS : IsOpen S) (hu : ContDiffOn ℝ ∞ (fun z => u (z, t)) S)
    (vs : List E) (v : E) {x : E} (hx : x ∈ S) :
    fderiv ℝ (fderiv ℝ (fun z => spatialDerivativeWord (v :: vs) u (z, t))) x =
      fderiv ℝ (fun z => fderiv ℝ (fderiv ℝ
        (fun w => spatialDerivativeWord vs u (w, t))) z) x v := by
  have hw := spatialDerivativeWord_smooth_slice hS hu vs
  have hD : ContDiffOn ℝ ∞ (fderiv ℝ (fun z => spatialDerivativeWord vs u (z, t))) S :=
    hw.fderiv_of_isOpen hS (by simp)
  have hDD : ContDiffOn ℝ ∞
      (fderiv ℝ (fderiv ℝ (fun z => spatialDerivativeWord vs u (z, t)))) S :=
    hD.fderiv_of_isOpen hS (by simp)
  have hd := (hDD.contDiffAt (hS.mem_nhds hx)).differentiableAt (by simp)
  ext a b
  exact (spatial_second_direction_commute hS hw hx v a b).trans
    (fderiv_bilinear_evaluation_const hd a b v)

end Yau.NodeProofs.F01Aux
