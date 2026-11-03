import Yau.Proofs.C01LeviCoordinates

/-! The actual first and mixed jets on a spatial affine complex line. -/

noncomputable section

open scoped Topology ContDiff

namespace Yau.NodeProofs.C01Aux

open Yau
open Yau.Blueprint.Alignment.Y03Proof

theorem spatial_affine_wirtinger {n : ℕ} (f : ComplexVector n → ℂ)
    (z v : ComplexVector n) (hf : ContDiffAt ℝ 2 f z) :
    wirt (fun p : ℂ => f (z + p • v)) 0 1 = wirt f z v ∧
      wirtBar (fun p : ℂ => f (z + p • v)) 0 1 = wirtBar f z v := by
  let γ : ℂ → ComplexVector n := fun p => z + p • v
  have hd : HasDerivAt γ v 0 := by
    simpa only [one_smul, id_eq] using! ((hasDerivAt_id (0 : ℂ)).smul_const v).const_add z
  have hF : DifferentiableAt ℝ f (γ 0) := by
    simpa only [γ, zero_smul, add_zero] using hf.differentiableAt (by norm_num)
  have hw := wirt_comp_holomorphic (f := f) (γ := γ) (z := (0 : ℂ)) (v := (1 : ℂ)) hF hd.differentiableAt
  have hb := wirtBar_comp_holomorphic (f := f) (γ := γ) (z := (0 : ℂ)) (v := (1 : ℂ)) hF hd.differentiableAt
  rw [hd.hasFDerivAt.fderiv] at hw hb
  constructor
  · simpa only [γ, Function.comp_def, ContinuousLinearMap.toSpanSingleton_apply,
      one_smul, zero_smul, add_zero] using hw
  · simpa only [γ, Function.comp_def, ContinuousLinearMap.toSpanSingleton_apply,
      one_smul, zero_smul, add_zero] using hb

theorem spatial_affine_mixed {n : ℕ} (f : ComplexVector n → ℂ)
    (z v : ComplexVector n) (hf : ContDiffAt ℝ 2 f z) :
    wirt (fun p => wirtBar (fun q : ℂ => f (z + q • v)) p 1) 0 1 =
      wirt (fun p => wirtBar f p v) z v := by
  let γ : ℂ → ComplexVector n := fun p => z + p • v
  have hd : HasDerivAt γ v 0 := by
    simpa only [one_smul, id_eq] using! ((hasDerivAt_id (0 : ℂ)).smul_const v).const_add z
  have hγ : ContDiffAt ℂ 2 γ 0 := by fun_prop
  have hF : ContDiffAt ℝ 2 f (γ 0) := by simpa only [γ, zero_smul, add_zero] using hf
  have hm := levi_direction_comp_holomorphic (f := f) (γ := γ) (z := (0 : ℂ)) hF hγ (1 : ℂ)
  rw [hd.hasFDerivAt.fderiv] at hm
  simpa only [γ, Function.comp_def, ContinuousLinearMap.toSpanSingleton_apply,
    one_smul, zero_smul, add_zero] using hm

end Yau.NodeProofs.C01Aux
