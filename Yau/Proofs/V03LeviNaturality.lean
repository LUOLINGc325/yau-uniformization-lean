import Yau.Proofs.V03LeviChain

/-! Full complex mixed Wirtinger naturality under the actual holomorphic
coordinate map, including unequal tangent arguments. -/

open scoped Topology ContDiff

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau

theorem secondFDeriv_complex_cross {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    {f : E → F} {z : E} (hf : ContDiffAt ℂ 2 f z) (v w : E) :
    fderiv ℝ (fderiv ℝ f) z w (Complex.I • v) =
      fderiv ℝ (fderiv ℝ f) z (Complex.I • w) v := by
  rw [secondFDeriv_restrict_complex hf, secondFDeriv_restrict_complex hf]
  simp only [map_smul, smul_apply]

theorem mixedWirt_holomorphic_comp {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    {T : E → F} {f : F → ℝ} {z : E} (hT : ContDiffAt ℂ 2 T z)
    (hf : ContDiffAt ℝ 2 f (T z)) (v w : E) :
    wirt (fun y => wirtBar (fun y' => (f (T y') : ℂ)) y v) z w =
      wirt (fun y => wirtBar (fun y' => (f y' : ℂ)) y
        (fderiv ℂ T z v)) (T z) (fderiv ℂ T z w) := by
  have hd := hT.differentiableAt (by norm_num)
  have hreal (u : E) : fderiv ℝ T z u = fderiv ℂ T z u :=
    congrArg (fun L : E →L[ℝ] F => L u) (hd.fderiv_restrictScalars ℝ)
  have hTR := hT.restrict_scalars ℝ
  have hcomp : ContDiffAt ℝ 2 (f ∘ T) z := hf.comp z hTR
  have hcompC : ContDiffAt ℝ 2 (fun y => ((f ∘ T) y : ℂ)) z :=
    hcomp.continuousLinearMap_comp Complex.ofRealCLM
  have hfC : ContDiffAt ℝ 2 (fun y => (f y : ℂ)) (T z) :=
    hf.continuousLinearMap_comp Complex.ofRealCLM
  change wirt (fun y => wirtBar (fun y' => ((f ∘ T) y' : ℂ)) y v) z w = _
  rw [mixedWirt_eq_secondFDeriv
      ((hcompC.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero),
    mixedWirt_eq_secondFDeriv
      ((hfC.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero)]
  simp only [secondFDeriv_ofReal hcomp, secondFDeriv_ofReal hf,
    secondFDeriv_comp hTR hf, secondFDeriv_complex_I_I hT,
    secondFDeriv_complex_cross hT, map_neg, hreal, map_smul,
    Complex.ofReal_add, Complex.ofReal_neg]
  ring

end Yau.Blueprint.V03Proof
