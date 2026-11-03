import Yau.LeafProofs.L21CayleyGraph

/-! The genuine pullback of the standard complex structure has zero Nijenhuis tensor. -/
noncomputable section
open Filter
open scoped Topology ContDiff
namespace Yau.Proofs.C04ChartsAux
open Yau Yau.LeafProofs.L21Aux
variable {n : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 5

theorem nijenhuis_zero_of_differential_intertwines
    (Z : ComplexVector n → ComplexVector n)
    (J : ComplexVector n → ComplexVector n →L[ℝ] ComplexVector n)
    (x : ComplexVector n) (hZ : ContDiffAt ℝ 2 Z x) (hJ : DifferentiableAt ℝ J x)
    (hi : Function.Injective (fderiv ℝ Z x))
    (hrel : ∀ᶠ y in 𝓝 x, ∀ v, fderiv ℝ Z y (J y v) = Complex.I • fderiv ℝ Z y v)
    (v w : ComplexVector n) : Yau.LeafCandidates.nijenhuis J x v w = 0 := by
  have hDZ : DifferentiableAt ℝ (fderiv ℝ Z) x :=
    (hZ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hD (u q : ComplexVector n) :
      fderiv ℝ Z x (fderiv ℝ J x u q) =
        Complex.I • fderiv ℝ (fderiv ℝ Z) x u q - fderiv ℝ (fderiv ℝ Z) x u (J x q) := by
    have hleft := hDZ.hasFDerivAt.clm_apply
      (hJ.hasFDerivAt.clm_apply (hasFDerivAt_const q x))
    have hright := (stdComplex n).hasFDerivAt.comp x
      (hDZ.hasFDerivAt.clm_apply (hasFDerivAt_const q x))
    have heq : (fun y => fderiv ℝ Z y (J y q)) =ᶠ[𝓝 x]
        (fun y => stdComplex n (fderiv ℝ Z y q)) := hrel.mono (fun y hy => hy q)
    have hh := congrArg (fun L : ComplexVector n →L[ℝ] ComplexVector n => L u)
      (hright.unique (hleft.congr_of_eventuallyEq heq.symm))
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.flip_apply, ContinuousLinearMap.zero_apply, map_zero,
      zero_add, stdComplex_apply] at hh
    exact eq_sub_iff_add_eq.mpr (by simpa only [add_comm] using hh.symm)
  have hI (q : ComplexVector n) : fderiv ℝ Z x (J x q) = Complex.I • fderiv ℝ Z x q :=
    (hrel.self_of_nhds) q
  have hsym (a b : ComplexVector n) :
      fderiv ℝ (fderiv ℝ Z) x a b = fderiv ℝ (fderiv ℝ Z) x b a :=
    hZ.isSymmSndFDerivAt (by norm_num) a b
  apply hi
  rw [nijenhuis_eq_tensor hJ]
  simp only [map_sub, map_add, map_zero, hI, hD, smul_sub, smul_smul,
    Complex.I_mul_I, neg_one_smul]
  rw [hsym (J x v) (J x w), hsym (J x v) w, hsym (J x w) v, hsym w v]
  abel

end Yau.Proofs.C04ChartsAux
