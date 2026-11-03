import Yau.Proofs.F01ClosedTimeSpaceCommutation

/-! The genuine third spatial derivative commutes with a fixed
directional derivative. Only symmetry of the actual second derivative and
the derivative of its local symmetry identity are used. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace Yau.NodeProofs.F01Aux
variable {E F V W : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [NormedAddCommGroup W] [NormedSpace ℝ W]

theorem fderiv_bilinear_evaluation_const {B : E → V →L[ℝ] W →L[ℝ] F} {x : E}
    (hB : DifferentiableAt ℝ B x) (v : V) (w : W) (a : E) :
    fderiv ℝ (fun z => B z v w) x a = fderiv ℝ B x a v w := by
  have hi := hB.clm_apply (differentiableAt_const v)
  rw [fderiv_clm_apply hi (differentiableAt_const w), fderiv_clm_apply hB (differentiableAt_const v)]
  simp

theorem spatial_second_direction_commute {q : E → F} {S : Set E} (hS : IsOpen S)
    (hq : ContDiffOn ℝ ∞ q S) {x : E} (hx : x ∈ S) (v a b : E) :
    fderiv ℝ (fderiv ℝ (fun z => fderiv ℝ q z v)) x a b =
      fderiv ℝ (fun z => fderiv ℝ (fderiv ℝ q) z a b) x v := by
  have hD : ContDiffOn ℝ ∞ (fderiv ℝ q) S := hq.fderiv_of_isOpen hS (by simp)
  have hDD : ContDiffOn ℝ ∞ (fderiv ℝ (fderiv ℝ q)) S := hD.fderiv_of_isOpen hS (by simp)
  have hqv : ContDiffOn ℝ ∞ (fun z => fderiv ℝ q z v) S := hD.clm_apply contDiffOn_const
  have hDqv : ContDiffOn ℝ ∞ (fderiv ℝ (fun z => fderiv ℝ q z v)) S :=
    hqv.fderiv_of_isOpen hS (by simp)
  have hleft : fderiv ℝ (fderiv ℝ (fun z => fderiv ℝ q z v)) x a b =
      fderiv ℝ (fun z => fderiv ℝ (fun y => fderiv ℝ q y v) z b) x a := by
    have he := fderiv_clm_apply
      ((hDqv.contDiffAt (hS.mem_nhds hx)).differentiableAt (by simp)) (differentiableAt_const b)
    simpa using (congrArg (fun L : E →L[ℝ] F => L a) he).symm
  have hlocal : (fun z => fderiv ℝ (fun y => fderiv ℝ q y v) z b) =ᶠ[𝓝 x]
      (fun z => fderiv ℝ (fderiv ℝ q) z v b) := by
    filter_upwards [hS.mem_nhds hx] with z hz
    have he := fderiv_clm_apply
      ((hD.contDiffAt (hS.mem_nhds hz)).differentiableAt (by simp)) (differentiableAt_const v)
    have hval : fderiv ℝ (fun y => fderiv ℝ q y v) z b = fderiv ℝ (fderiv ℝ q) z b v := by
      simpa using congrArg (fun L : E →L[ℝ] F => L b) he
    exact hval.trans ((hq.contDiffAt (hS.mem_nhds hz)).isSymmSndFDerivAt (by simp) b v)
  rw [hleft, hlocal.fderiv_eq,
    fderiv_bilinear_evaluation_const ((hDD.contDiffAt (hS.mem_nhds hx)).differentiableAt (by simp)) v b a,
    fderiv_bilinear_evaluation_const ((hDD.contDiffAt (hS.mem_nhds hx)).differentiableAt (by simp)) a b v]
  exact congrArg (fun L : E →L[ℝ] F => L b)
    ((hD.contDiffAt (hS.mem_nhds hx)).isSymmSndFDerivAt (by simp) a v)

end Yau.NodeProofs.F01Aux
