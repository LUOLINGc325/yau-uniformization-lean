import Yau.Proofs.F05BootstrapRelativeProduct
import Yau.Proofs.F05BootstrapNative

/-! The computed relative cutoff equation retains both principal gradient
terms and the full drift. Its commutator contains no spatial Hessian of the
unknown. -/

open Set
open scoped ContDiff
noncomputable section
set_option maxHeartbeats 1600000
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.LeafProofs.L16Aux
variable {n : ℕ}

def F05RelSpatialCommutator (X : Set (Space n)) (a : Point n → Mat n)
    (b : Point n → RIdx n → ℝ) (φ : Space n → ℝ) (u : Point n → ℝ) (z : Point n) : ℝ :=
  (∑ i,∑ j,a z i j*
    (fderiv ℝ φ z.1 (realVec i)*F05RelD X u z (realVec j)+
      fderiv ℝ φ z.1 (realVec j)*F05RelD X u z (realVec i)+
      u z*fderiv ℝ (fderiv ℝ φ) z.1 (realVec i) (realVec j)))+
    u z*(∑ i,b z i*fderiv ℝ φ z.1 (realVec i))

theorem F05_relative_spatial_product_jets {X : Set (Space n)} {I : Set ℝ}
    (hX : UniqueDiffOn ℝ X) {φ : Space n → ℝ} (hφ : ContDiff ℝ 2 φ)
    {u : Point n → ℝ} (hu : F05RelC2 X I u) {z : Point n} (hz : z ∈ X ×ˢ I) :
    F05RelD X (fun p => φ p.1*u p) z = φ z.1 • F05RelD X u z+u z • fderiv ℝ φ z.1 ∧
    F05RelDD X (fun p => φ p.1*u p) z =
      φ z.1 • F05RelDD X u z+(fderiv ℝ φ z.1).smulRight (F05RelD X u z)+
        (F05RelD X u z).smulRight (fderiv ℝ φ z.1)+u z • fderiv ℝ (fderiv ℝ φ) z.1 ∧
    F05RelT I (fun p => φ p.1*u p) z = φ z.1*F05RelT I u z := by
  have hDφ : fderivWithin ℝ φ X z.1 = fderiv ℝ φ z.1 :=
    (hφ.differentiable (by norm_num) z.1).fderivWithin (hX z.1 hz.1)
  have hDDφ : fderivWithin ℝ (fderivWithin ℝ φ X) X z.1 = fderiv ℝ (fderiv ℝ φ) z.1 :=
    F05RelDD_eq_spatialDD (v := fun p => φ p.1) hX hz.1 (fun x hx => hφ.contDiffAt)
  refine ⟨?_,?_,?_⟩
  · unfold F05RelD
    rw [fderivWithin_fun_mul (hX z.1 hz.1)
      (hφ.differentiable (by norm_num) z.1).differentiableWithinAt
      ((hu.2.2.2.2.1 z.2 hz.2 z.1 hz.1).differentiableWithinAt (by norm_num)),hDφ]
  · have h := F05_second_fderivWithin_mul hX hφ.contDiffOn (hu.2.2.2.2.1 z.2 hz.2) hz.1
    simpa only [hDφ,hDDφ,F05RelDD,F05RelD] using h
  · exact derivWithin_const_mul_field (φ z.1)

theorem F05_relative_spatial_cutoff_operator {X : Set (Space n)} {I : Set ℝ}
    (hX : UniqueDiffOn ℝ X) {φ : Space n → ℝ} (hφ : ContDiff ℝ 2 φ)
    {u : Point n → ℝ} (hu : F05RelC2 X I u)
    (a : Point n → Mat n) (b : Point n → RIdx n → ℝ) {z : Point n} (hz : z ∈ X ×ˢ I) :
    F05RelOp X I a b (fun p => φ p.1*u p) z =
      φ z.1*F05RelOp X I a b u z-F05RelSpatialCommutator X a b φ u z := by
  obtain ⟨hD,hDD,hT⟩ := F05_relative_spatial_product_jets hX hφ hu hz
  simp only [F05RelOp,F05RelSpatialCommutator,hD,hDD,hT,
    ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply,smul_eq_mul]
  simp only [mul_add,mul_sub,add_mul,sub_mul,Finset.sum_add_distrib,Finset.sum_sub_distrib,
    Finset.mul_sum,Finset.sum_mul]
  simp only [mul_assoc,mul_left_comm,mul_comm]
  ring

end Yau.Proofs.F05Aux
