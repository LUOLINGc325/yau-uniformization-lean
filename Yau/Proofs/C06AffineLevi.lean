import Yau.Proofs.P07DistanceLeviCalculus

noncomputable section
open scoped Topology ContDiff

namespace Yau.Proofs.C06Aux

open Yau Yau.Blueprint Yau.LeafProofs.L22Aux

variable {n : ℕ}

theorem leviDirection_affine {f : ComplexVector n → ℝ} {z : ComplexVector n}
    (hf : ContDiffAt ℝ 2 f z) (a b : ℝ) (v : ComplexVector n) :
    leviDirection (leviC (fun x => a * f x + b) z) v =
      a * leviDirection (leviC f z) v := by
  have hF : ContDiffAt ℝ 2 (fun x => a * f x + b) z :=
    (contDiffAt_const.mul hf).add contDiffAt_const
  rw [leviDirection, leviC_quadratic_re hF, leviDirection, leviC_quadratic_re hf]
  have hb : fderiv ℝ (fun _ : ComplexVector n => b) = (fun _ => 0) := by
    funext x
    exact fderiv_const_apply b
  simp only [complexLeviQuadratic, secondFDeriv_add (contDiffAt_const.mul hf) contDiffAt_const,
    secondFDeriv_const_mul hf, hb, fderiv_const_apply, zero_apply]
  ring

end Yau.Proofs.C06Aux
