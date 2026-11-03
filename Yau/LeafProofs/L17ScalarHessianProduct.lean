import Yau.LeafProofs.L17ParabolicOperatorContraction
import Yau.LeafProofs.L16

/-! The actual second Frechet product rule needed by the Gaussian commutator. -/

open Filter
open scoped Topology ContDiff
noncomputable section

set_option backward.isDefEq.respectTransparency.types false

namespace Yau.LeafProofs.L17Aux

theorem secondFDeriv_mul_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : E → ℝ} {x : E} (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x)
    (v w : E) :
    fderiv ℝ (fderiv ℝ (fun y => f y * g y)) x v w =
      f x * fderiv ℝ (fderiv ℝ g) x v w +
      g x * fderiv ℝ (fderiv ℝ f) x v w +
      fderiv ℝ f x v * fderiv ℝ g x w + fderiv ℝ g x v * fderiv ℝ f x w := by
  have hfd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hgd : DifferentiableAt ℝ (fderiv ℝ g) x :=
    (hg.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hpd : DifferentiableAt ℝ (fderiv ℝ (fun y => f y * g y)) x :=
    ((hf.mul hg).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hfw : DifferentiableAt ℝ (fun y => fderiv ℝ f y w) x :=
    hfd.clm_apply (differentiableAt_const w)
  have hgw : DifferentiableAt ℝ (fun y => fderiv ℝ g y w) x :=
    hgd.clm_apply (differentiableAt_const w)
  have hfx : DifferentiableAt ℝ f x := hf.differentiableAt (by norm_num)
  have hgx : DifferentiableAt ℝ g x := hg.differentiableAt (by norm_num)
  have heq : (fun y => fderiv ℝ (fun z => f z * g z) y w) =ᶠ[𝓝 x]
      (fun y => f y * fderiv ℝ g y w + g y * fderiv ℝ f y w) := by
    filter_upwards [hf.eventually (by norm_num),hg.eventually (by norm_num)] with y hfy hgy
    rw [fderiv_fun_mul (hfy.differentiableAt (by norm_num)) (hgy.differentiableAt (by norm_num))]
    rfl
  calc
    _ = fderiv ℝ (fun y => fderiv ℝ (fun z => f z * g z) y w) x v := by
      rw [fderiv_clm_apply hpd (differentiableAt_const w)]
      simp
    _ = fderiv ℝ (fun y => f y * fderiv ℝ g y w + g y * fderiv ℝ f y w) x v :=
      congrArg (fun L : E →L[ℝ] ℝ => L v) (heq.fderiv_eq (𝕜 := ℝ))
    _ = _ := by
      have hleft : DifferentiableAt ℝ (fun y => f y * fderiv ℝ g y w) x := hfx.mul hgw
      have hright : DifferentiableAt ℝ (fun y => g y * fderiv ℝ f y w) x := hgx.mul hfw
      rw [fderiv_fun_add hleft hright,fderiv_fun_mul hfx hgw,
        fderiv_fun_mul hgx hfw,fderiv_clm_apply hgd (differentiableAt_const w),
        fderiv_clm_apply hfd (differentiableAt_const w)]
      simp [smul_eq_mul]
      ring

def gradientCrossContraction {n : ℕ} (a : Matrix (RIdx n) (RIdx n) ℝ)
    (f g : ComplexVector n → ℝ) (x : ComplexVector n) : ℝ :=
  ∑ i, ∑ j, a i j * (fderiv ℝ f x (realVec i) * fderiv ℝ g x (realVec j) +
    fderiv ℝ g x (realVec i) * fderiv ℝ f x (realVec j))

theorem realHessianContraction_mul {n : ℕ} (a : Matrix (RIdx n) (RIdx n) ℝ)
    {f g : ComplexVector n → ℝ} {x : ComplexVector n}
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) :
    realHessianContraction a (fun y => f y * g y) x =
      f x * realHessianContraction a g x + g x * realHessianContraction a f x +
      gradientCrossContraction a f g x := by
  unfold realHessianContraction gradientCrossContraction
  simp_rw [secondFDeriv_mul_apply hf hg]
  simp only [mul_add,Finset.sum_add_distrib,Finset.mul_sum]
  simp only [mul_left_comm,mul_comm]
  ring

theorem realHessianContraction_sub_coefficient {n : ℕ}
    (a b : Matrix (RIdx n) (RIdx n) ℝ) (f : ComplexVector n → ℝ) (x : ComplexVector n) :
    realHessianContraction (a - b) f x =
      realHessianContraction a f x - realHessianContraction b f x := by
  simp only [realHessianContraction,Matrix.sub_apply,sub_mul,Finset.sum_sub_distrib]

theorem timeD_spatial_mul {n : ℕ} {Q : Set (Yau.Parabolic.Point n)}
    {u : Yau.Parabolic.Point n → ℝ} (hu : Yau.Parabolic.C2 Q u)
    (f : ComplexVector n → ℝ) {q : Yau.Parabolic.Point n} (hq : q ∈ Q) :
    Yau.Parabolic.timeD Q (fun p => f p.1 * u p) q = f q.1 * Yau.Parabolic.timeD Q u q := by
  exact derivWithin_const_mul (f q.1) (hu.2.2.2.2.2 q hq)

theorem linearOp_spatial_mul_frozen {n : ℕ} {Q : Set (Yau.Parabolic.Point n)}
    {u : Yau.Parabolic.Point n → ℝ} (hu : Yau.Parabolic.C2 Q u)
    (f : ComplexVector n → ℝ) (a₀ : Yau.Parabolic.Mat n)
    (a : Yau.Parabolic.Point n → Yau.Parabolic.Mat n)
    {q : Yau.Parabolic.Point n} (hq : q ∈ Q) (hf : ContDiffAt ℝ 2 f q.1) :
    Yau.Parabolic.linearOp Q a (fun _ _ => 0) (fun p => f p.1 * u p) q =
      f q.1 * Yau.Parabolic.linearOp Q (fun _ => a₀) (fun _ _ => 0) u q +
      f q.1 * realHessianContraction (a₀ - a q) (fun z => u (z,q.2)) q.1 -
      u q * realHessianContraction (a q) f q.1 -
      gradientCrossContraction (a q) f (fun z => u (z,q.2)) q.1 := by
  simp only [Yau.Parabolic.linearOp,zero_mul,Finset.sum_const_zero,sub_zero]
  change Yau.Parabolic.timeD Q (fun p => f p.1 * u p) q -
    realHessianContraction (a q) (fun z => f z * u (z,q.2)) q.1 = _
  rw [timeD_spatial_mul hu f hq,realHessianContraction_mul (a q) hf (hu.2.2.2.2.1 q hq),
    realHessianContraction_sub_coefficient]
  change f q.1 * Yau.Parabolic.timeD Q u q -
    (f q.1 * realHessianContraction (a q) (fun z => u (z,q.2)) q.1 +
      u q * realHessianContraction (a q) f q.1 +
      gradientCrossContraction (a q) f (fun z => u (z,q.2)) q.1) = _
  change _ = f q.1 * (Yau.Parabolic.timeD Q u q -
    realHessianContraction a₀ (fun z => u (z,q.2)) q.1) + _ - _ - _
  ring

end Yau.LeafProofs.L17Aux
