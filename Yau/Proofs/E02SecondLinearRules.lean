import Yau.Proofs.E02AffinePullback
import Yau.Proofs.E02NormQuadraticJet

open scoped Topology ContDiff
noncomputable section
namespace Yau.NodeProofs.E02Aux

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem second_fderiv_linear_comp_apply (L : E →L[ℝ] F) {f : F → ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f (L x)) (v w : E) :
    fderiv ℝ (fderiv ℝ (fun y => f (L y))) x v w =
      fderiv ℝ (fderiv ℝ f) (L x) (L v) (L w) := by
  have hAt : ContDiffAt ℝ 2 f (0+L x) := by simpa only [zero_add] using hf
  have h := affinePullback_second_fderiv (0 : F) L hAt
  have hVal := congrArg (fun A : E →L[ℝ] E →L[ℝ] ℝ => A v w) h
  simpa only [zero_add,ContinuousLinearMap.bilinearComp_apply] using hVal

theorem second_fderiv_const_add_add_sub_mul {f g h : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) (hh : ContDiffAt ℝ 2 h x)
    (c θ : ℝ) :
    fderiv ℝ (fderiv ℝ (fun y => c+f y+g y-θ*h y)) x =
      fderiv ℝ (fderiv ℝ f) x+fderiv ℝ (fderiv ℝ g) x-θ • fderiv ℝ (fderiv ℝ h) x := by
  have hJet := realSecondJet_add
    (realSecondJet_add (realSecondJet_add (realSecondJet_const (E := E) c x)
      (realSecondJet_of_contDiffAt_two hf)) (realSecondJet_of_contDiffAt_two hg))
    (realSecondJet_const_mul (realSecondJet_of_contDiffAt_two hh) (-θ))
  have hC : ContDiffAt ℝ 2 (fun y => c+f y+g y+(-θ)*h y) x :=
    ((contDiffAt_const.add hf).add hg).add (contDiffAt_const.mul hh)
  have hFun : (fun y => c+f y+g y-θ*h y) = (fun y => c+f y+g y+(-θ)*h y) := by
    funext y
    ring
  rw [hFun]
  have hSecond : fderiv ℝ (fderiv ℝ (fun y => c+f y+g y+(-θ)*h y)) x =
      (0+fderiv ℝ (fderiv ℝ f) x)+fderiv ℝ (fderiv ℝ g) x+
        (-θ) • fderiv ℝ (fderiv ℝ h) x := realSecondJet_second_fderiv_eq hJet hC
  calc
    _ = (0+fderiv ℝ (fderiv ℝ f) x)+fderiv ℝ (fderiv ℝ g) x+
        (-θ) • fderiv ℝ (fderiv ℝ h) x := hSecond
    _ = _ := by
      ext v w
      simp only [_root_.add_apply,_root_.sub_apply,_root_.smul_apply,_root_.zero_apply,smul_eq_mul]
      ring

end Yau.NodeProofs.E02Aux
