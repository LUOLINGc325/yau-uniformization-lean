import Yau.Proofs.C01LeviRealHessian

/-! The real quadratic Levi expression in one spatial direction and one
real multiple of the clock direction, with its two exact cross terms. -/

noncomputable section

open scoped Topology ContDiff

namespace Yau.NodeProofs.C01Aux

open Yau
open Yau.Blueprint.Alignment.Y03Proof

theorem mixedLevi_two_real_directions
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    {f : V → ℝ} {z : V} (hf : ContDiffAt ℝ 2 f z) (a b : V) (r : ℝ) :
    (wirt (fun p => wirtBar (fun q => (f q : ℂ)) p (a + r • b)) z (a + r • b)).re =
      (wirt (fun p => wirtBar (fun q => (f q : ℂ)) p a) z a).re +
      2 * r * (wirt (fun p => wirtBar (fun q => (f q : ℂ)) p b) z a).re +
      r ^ 2 * (wirt (fun p => wirtBar (fun q => (f q : ℂ)) p b) z b).re := by
  let fc : V → ℂ := fun p => (f p : ℂ)
  have hfc : ContDiffAt ℝ 2 fc z :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp z hf
  have had : DifferentiableAt ℝ (fun p => wirtBar fc p a) z :=
    (wirtBar_contDiffAt hfc a).differentiableAt (by norm_num)
  have hbd : DifferentiableAt ℝ (fun p => wirtBar fc p b) z :=
    (wirtBar_contDiffAt hfc b).differentiableAt (by norm_num)
  have hinner : (fun p => wirtBar fc p (a + r • b)) =
      (fun p => wirtBar fc p a + (r : ℂ) * wirtBar fc p b) := by
    funext p
    rw [wirtBar_add_dir, wirtBar_real_smul_dir]
  have hsum := wirt_add_fn (f := fun p => wirtBar fc p a)
    (g := fun p => (r : ℂ) * wirtBar fc p b) had (hbd.const_mul _) (a + r • b)
  have hconst := wirt_const_mul_fn hbd (a + r • b) (r : ℂ)
  change (wirt (fun p => wirtBar fc p (a + r • b)) z (a + r • b)).re = _
  rw [hinner, hsum, hconst]
  simp only [wirt_add_dir, wirt_real_smul_dir, Complex.add_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  dsimp only [fc]
  rw [mixedLevi_re_swap hf a b]
  ring

end Yau.NodeProofs.C01Aux
