import Yau.Proofs.F04WirtingerComp

open Filter Set
open scoped Topology ContDiff Matrix ComplexOrder

noncomputable section

namespace Yau.F04Proof

open Yau.LeafProofs.L14Aux

theorem leviC_real_comp {n : ℕ} {f : ComplexVector n → ℝ} {F : ℝ → ℝ}
    {z : ComplexVector n} (hf : ContDiffAt ℝ 2 f z) (hF : ContDiffAt ℝ 2 F (f z)) :
    leviC (fun y => F (f y)) z =
      ((deriv F (f z) : ℝ) : ℂ) • leviC f z +
        ((deriv (deriv F) (f z) : ℝ) : ℂ) •
          Matrix.vecMulVec (star (complexGradient f z)) (complexGradient f z) := by
  let fC : ComplexVector n → ℂ := fun y => (f y : ℂ)
  let P : ComplexVector n → ℂ := fun y => ((deriv F (f y) : ℝ) : ℂ)
  have hfC : ContDiffAt ℝ 2 fC z := Complex.ofRealCLM.contDiff.contDiffAt.comp z hf
  have hDF : ContDiffAt ℝ 1 (deriv F) (f z) := hF.derivWithin (by norm_num)
  have hP : DifferentiableAt ℝ P z :=
    (Complex.ofRealCLM.contDiff.contDiffAt.comp z (hDF.comp z (hf.of_le (by norm_num)))).differentiableAt
      (by norm_num)
  have hFs : ∀ᶠ y in 𝓝 z, ContDiffAt ℝ 2 F (f y) :=
    hf.continuousAt.tendsto.eventually (hF.eventually (by norm_num))
  ext i j
  have hinner : (fun y => wirtBar (fun v => (F (f v) : ℂ)) y (stdVec i)) =ᶠ[𝓝 z]
      (fun y => P y * wirtBar fC y (stdVec i)) := by
    filter_upwards [hf.eventually (by norm_num), hFs] with y hyf hyF
    exact (wirt_real_comp (hyf.differentiableAt (by norm_num))
      (hyF.differentiableAt (by norm_num)).hasDerivAt (stdVec i)).2
  have houter := congrArg (fun L : ComplexVector n →L[ℝ] ℂ =>
    (1 / 2 : ℂ) * (L (stdVec j) - Complex.I * L (Complex.I • stdVec j))) hinner.fderiv_eq
  change wirt (fun y => wirtBar (fun v => (F (f v) : ℂ)) y (stdVec i)) z (stdVec j) = _
  change wirt (fun y => wirtBar (fun v => (F (f v) : ℂ)) y (stdVec i)) z (stdVec j) =
    wirt (fun y => P y * wirtBar fC y (stdVec i)) z (stdVec j) at houter
  rw [houter, wirt_mul_rule P (fun y => wirtBar fC y (stdVec i)) z (stdVec j)
    hP (wirtBar_differentiableAt hfC _)]
  have hchain : wirt P z (stdVec j) =
      ((deriv (deriv F) (f z) : ℝ) : ℂ) * wirt fC z (stdVec j) :=
    (wirt_real_comp (hf.differentiableAt (by norm_num))
      (hDF.differentiableAt (by norm_num)).hasDerivAt (stdVec j)).1
  rw [hchain]
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, Pi.star_apply, smul_eq_mul]
  dsimp only [leviC, leviMatrix, complexGradient, P, fC]
  rw [wirtBar_ofReal_eq_star f z (stdVec i)]
  ring

end Yau.F04Proof
