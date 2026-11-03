import Yau.Proofs.F05BootstrapRelativeProduct

/-! The actual within-time product rule for a cutoff contributes only
theta' times the value; it introduces no higher unknown derivative. -/

open Set
open scoped ContDiff
noncomputable section
set_option maxHeartbeats 1600000
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.LeafProofs.L16Aux
variable {n : ℕ}

theorem F05_relative_time_product_jets {X : Set (Space n)} {I : Set ℝ}
    (hX : UniqueDiffOn ℝ X) (hI : UniqueDiffOn ℝ I) {θ : ℝ → ℝ} (hθ : ContDiff ℝ 1 θ)
    {u : Point n → ℝ} (hu : F05RelC2 X I u) {z : Point n} (hz : z ∈ X ×ˢ I) :
    F05RelD X (fun p => θ p.2*u p) z = θ z.2 • F05RelD X u z ∧
      F05RelDD X (fun p => θ p.2*u p) z = θ z.2 • F05RelDD X u z ∧
      F05RelT I (fun p => θ p.2*u p) z = deriv θ z.2*u z+θ z.2*F05RelT I u z := by
  refine ⟨?_,?_,?_⟩
  · exact fderivWithin_const_mul (hX z.1 hz.1)
      ((hu.2.2.2.2.1 z.2 hz.2 z.1 hz.1).differentiableWithinAt (by norm_num)) (θ z.2)
  · have h := F05_second_fderivWithin_mul hX (f := fun _ => θ z.2)
      contDiffOn_const (hu.2.2.2.2.1 z.2 hz.2) hz.1
    simpa only [F05RelDD,F05RelD,fderivWithin_fun_const,fderivWithin_zero,Pi.zero_apply,
      ContinuousLinearMap.zero_smulRight,ContinuousLinearMap.smulRight_zero,zero_smul,
      smul_zero,add_zero] using h
  · have hθI : derivWithin θ I z.2 = deriv θ z.2 :=
      (hθ.differentiable (by norm_num) z.2).hasDerivAt.hasDerivWithinAt.derivWithin (hI z.2 hz.2)
    have h := derivWithin_fun_mul (hθ.differentiable (by norm_num) z.2).differentiableWithinAt
      (hu.2.2.2.2.2 z hz)
    simpa only [F05RelT,hθI] using h

theorem F05_relative_time_cutoff_operator {X : Set (Space n)} {I : Set ℝ}
    (hX : UniqueDiffOn ℝ X) (hI : UniqueDiffOn ℝ I) {θ : ℝ → ℝ} (hθ : ContDiff ℝ 1 θ)
    {u : Point n → ℝ} (hu : F05RelC2 X I u)
    (a : Point n → Mat n) (b : Point n → RIdx n → ℝ) {z : Point n} (hz : z ∈ X ×ˢ I) :
    F05RelOp X I a b (fun p => θ p.2*u p) z =
      θ z.2*F05RelOp X I a b u z+deriv θ z.2*u z := by
  obtain ⟨hD,hDD,hT⟩ := F05_relative_time_product_jets hX hI hθ hu hz
  have hPrincipal : (∑ i,∑ j,a z i j*(θ z.2*F05RelDD X u z (realVec i) (realVec j))) =
      θ z.2*(∑ i,∑ j,a z i j*F05RelDD X u z (realVec i) (realVec j)) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hDrift : (∑ i,b z i*(θ z.2*F05RelD X u z (realVec i))) =
      θ z.2*(∑ i,b z i*F05RelD X u z (realVec i)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  simp only [F05RelOp,hD,hDD,hT,ContinuousLinearMap.smul_apply,smul_eq_mul]
  rw [hPrincipal,hDrift]
  ring

end Yau.Proofs.F05Aux
