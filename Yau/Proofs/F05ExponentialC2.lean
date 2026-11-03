import Yau.Proofs.F05ExponentialTransform

/-! The actual exponential of a finite-C2 scalar solution is finite-C2 on
its original closed cylinder, with its literal gradient and Hessian. -/

open Set Filter
open scoped Topology ContDiff
noncomputable section
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency.types true
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.LeafProofs.L16Aux

local instance f05_expHessianGroup {n : ℕ} : NormedAddCommGroup (Space n →L[ℝ] Space n →L[ℝ] ℝ) := inferInstance
local instance f05_expHessianSpace {n : ℕ} : NormedSpace ℝ (Space n →L[ℝ] Space n →L[ℝ] ℝ) := inferInstance

theorem F05_secondFDeriv_exp {n : ℕ} {f : Space n → ℝ} {x : Space n}
    (hf : ContDiffAt ℝ 2 f x) :
    fderiv ℝ (fderiv ℝ (fun y => Real.exp (f y))) x =
      Real.exp (f x) • (fderiv ℝ (fderiv ℝ f) x+(fderiv ℝ f x).smulRight (fderiv ℝ f x)) := by
  have hD := hf.differentiableAt (by norm_num)
  have hDD := (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hNear : fderiv ℝ (fun y => Real.exp (f y)) =ᶠ[𝓝 x]
      (fun y => Real.exp (f y) • fderiv ℝ f y) := by
    filter_upwards [hf.eventually (by norm_num)] with y hy
    exact fderiv_exp (hy.differentiableAt (by norm_num))
  rw [hNear.fderiv_eq,fderiv_fun_smul hD.exp hDD,fderiv_exp hD]
  apply ContinuousLinearMap.ext
  intro v
  apply ContinuousLinearMap.ext
  intro w
  simp only [add_apply,smul_apply,
    ContinuousLinearMap.smulRight_apply,smul_eq_mul]
  ring

theorem F05_c2_exp {n : ℕ} {D : Set (Space n)} {T : ℝ} (hT : 0 < T)
    {w : Point n → ℝ} (hw : C2 (cylinder D 0 T) w) :
    C2 (cylinder D 0 T) (fun q => Real.exp (w q)) := by
  have hE : ContinuousOn (fun q => Real.exp (w q)) (cylinder D 0 T) := Real.continuous_exp.comp_continuousOn hw.1
  have hGrad (p : Point n) (hp : p ∈ cylinder D 0 T) :
      spatialD (fun q => Real.exp (w q)) p = Real.exp (w p) • spatialD w p :=
    fderiv_exp ((hw.2.2.2.2.1 p hp).differentiableAt (by norm_num))
  have hHessian (p : Point n) (hp : p ∈ cylinder D 0 T) :
      spatialDD (fun q => Real.exp (w q)) p = Real.exp (w p) •
        (spatialDD w p+(spatialD w p).smulRight (spatialD w p)) :=
    F05_secondFDeriv_exp (hw.2.2.2.2.1 p hp)
  have hTensor : Continuous (fun z : (Space n →L[ℝ] ℝ) × (Space n →L[ℝ] ℝ) => z.1.smulRight z.2) :=
    (isBoundedBilinearMap_smulRight : IsBoundedBilinearMap ℝ
      (fun z : (Space n →L[ℝ] ℝ) × (Space n →L[ℝ] ℝ) => z.1.smulRight z.2)).continuous
  refine ⟨hE,(hE.smul hw.2.1).congr hGrad,?_,?_,?_,?_⟩
  · exact (hE.smul (hw.2.2.1.add (hTensor.comp_continuousOn (hw.2.1.prodMk hw.2.1)))).congr hHessian
  · exact (hE.mul hw.2.2.2.1).congr (fun p hp => F05_timeD_exp hT hw hp)
  · intro p hp
    exact (hw.2.2.2.2.1 p hp).exp
  · intro p hp
    exact (hw.2.2.2.2.2 p hp).exp

end Yau.Proofs.F05Aux
