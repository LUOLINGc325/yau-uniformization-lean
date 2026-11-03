import Yau.LeafProofs.L12
import Mathlib.Analysis.Calculus.FDeriv.CompCLM

/-! Integrability follows from an actual nonsingular local coordinate
map intertwining with the original constant complex structure. -/

noncomputable section
open Filter
open scoped Topology ContDiff
namespace Yau.Blueprint.C02Proof
variable {n : ℕ}

theorem nijenhuis_zero_of_local_intertwining
    {F : ComplexVector n → ComplexVector n} {J : ComplexVector n → ComplexVector n →L[ℝ] ComplexVector n}
    {x : ComplexVector n} (hF : ContDiffAt ℝ 2 F x) (hJ : DifferentiableAt ℝ J x)
    (hInjective : Function.Injective (fderiv ℝ F x))
    (hEq : (fun y => (fderiv ℝ F y).comp (J y)) =ᶠ[𝓝 x]
      (fun y => (Yau.LeafProofs.L12Aux.complexStructureCLM n).comp (fderiv ℝ F y)))
    (v w : ComplexVector n) : LeafCandidates.nijenhuis J x v w = 0 := by
  let Q := fderiv ℝ F
  let I := Yau.LeafProofs.L12Aux.complexStructureCLM n
  have hQ1 : ContDiffAt ℝ 1 Q x := hF.fderiv_right (by norm_num)
  have hQ : DifferentiableAt ℝ Q x := hQ1.differentiableAt (by norm_num)
  have hL := hQ.hasFDerivAt.clm_comp hJ.hasFDerivAt
  have hR := (ContinuousLinearMap.compL ℝ (ComplexVector n) (ComplexVector n) (ComplexVector n) I).hasFDerivAt.comp x hQ.hasFDerivAt
  have hD (a b : ComplexVector n) :
      Q x (fderiv ℝ J x a b) = I (fderiv ℝ Q x a b) - fderiv ℝ Q x a (J x b) := by
    have he := congrArg (fun L : ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ComplexVector n => L a b)
      (hL.fderiv.symm.trans (hEq.fderiv_eq.trans hR.fderiv))
    have he' : Q x (fderiv ℝ J x a b) + fderiv ℝ Q x a (J x b) = I (fderiv ℝ Q x a b) := by
      simpa only [add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.compL_apply,
        ContinuousLinearMap.flip_apply] using he
    exact eq_sub_iff_add_eq.mpr he'
  have hI (a : ComplexVector n) : Q x (J x a) = I (Q x a) :=
    congrArg (fun L : ComplexVector n →L[ℝ] ComplexVector n => L a) hEq.eq_of_nhds
  have hEval (a : ComplexVector n) : fderiv ℝ (fun y => J y a) x = (fderiv ℝ J x).flip a := by
    have ha : fderiv ℝ (fun _ : ComplexVector n => a) x = 0 := (hasFDerivAt_const a x).fderiv
    simpa only [ha, ContinuousLinearMap.comp_zero, zero_add] using fderiv_clm_apply hJ (differentiableAt_const a)
  have hv : fderiv ℝ (fun _ : ComplexVector n => v) x = 0 := (hasFDerivAt_const v x).fderiv
  have hw : fderiv ℝ (fun _ : ComplexVector n => w) x = 0 := (hasFDerivAt_const w x).fderiv
  have hN : LeafCandidates.nijenhuis J x v w =
      fderiv ℝ J x (J x v) w - fderiv ℝ J x (J x w) v +
        J x (fderiv ℝ J x w v) - J x (fderiv ℝ J x v w) := by
    simp only [LeafCandidates.nijenhuis, LeafCandidates.bracket, hEval, hv, hw,
      ContinuousLinearMap.flip_apply, zero_apply, sub_zero, zero_sub, map_neg]
    abel
  have hSymm (a b : ComplexVector n) : fderiv ℝ Q x a b = fderiv ℝ Q x b a :=
    hF.isSymmSndFDerivAt (by norm_num) a b
  apply hInjective
  rw [hN, map_sub, map_add, map_sub, map_zero, hD, hD, hI, hI, hD, hD]
  have hIa (a : ComplexVector n) : I a = Complex.I • a := rfl
  simp only [hIa, smul_sub, smul_smul, Complex.I_mul_I, neg_one_smul]
  rw [hSymm (J x v) (J x w), hSymm (J x v) w, hSymm (J x w) v, hSymm w v]
  abel

end Yau.Blueprint.C02Proof
