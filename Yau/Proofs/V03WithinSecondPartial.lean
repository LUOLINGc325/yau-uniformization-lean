import Yau.Proofs.V03RealTraceDerivative
import Yau.Proofs.V03LeviChain

/-! Actual iterated within directional derivatives agree with ordinary
second derivatives at every interior point, and affine slices retain their
genuine joint Hessian. -/

open scoped Topology ContDiff
open Filter

noncomputable section
namespace Yau.Blueprint.V03Proof

theorem secondWithin_directional_eq {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {S : Set E} {f : E → F} {p : E} (hS : S ∈ 𝓝 p) (hf : ContDiffAt ℝ 2 f p) (v w : E) :
    fderivWithin ℝ (fun q => fderivWithin ℝ f S q v) S p w =
      fderiv ℝ (fderiv ℝ f) p w v := by
  have hp : p ∈ interior S := mem_interior_iff_mem_nhds.mpr hS
  have he : (fun q => fderivWithin ℝ f S q v) =ᶠ[𝓝 p] (fun q => fderiv ℝ f q v) := by
    filter_upwards [isOpen_interior.mem_nhds hp] with q hq
    rw [fderivWithin_of_mem_nhds (mem_interior_iff_mem_nhds.mp hq)]
  rw [fderivWithin_of_mem_nhds hS, he.fderiv_eq]
  exact (fderiv_real_clm_apply
    ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero) w v).symm

theorem secondFDeriv_spatial_slice {P Q : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup Q] [NormedSpace ℝ Q]
    {f : P × Q → ℝ} {p : P} {q : Q} (hf : ContDiffAt ℝ 2 f (p, q)) (v w : Q) :
    fderiv ℝ (fderiv ℝ (fun x => f (p, x))) q v w =
      fderiv ℝ (fderiv ℝ f) (p, q) (0, v) (0, w) := by
  have hT : ContDiffAt ℝ 2 (fun x : Q => (p, x)) q :=
    (contDiff_const.prodMk contDiff_id).contDiffAt
  have hh := secondFDeriv_comp hT hf v w
  have hDf (x : Q) : HasFDerivAt (fun x : Q => (p, x))
      ((0 : Q →L[ℝ] P).prod (ContinuousLinearMap.id ℝ Q)) x :=
    (hasFDerivAt_const (𝕜 := ℝ) p x).prodMk (hasFDerivAt_id x)
  have hd : fderiv ℝ (fun x : Q => (p, x)) q =
      (0 : Q →L[ℝ] P).prod (ContinuousLinearMap.id ℝ Q) := by
    exact (hDf q).fderiv
  have hdd : fderiv ℝ (fderiv ℝ (fun x : Q => (p, x))) q = 0 := by
    have he : fderiv ℝ (fun x : Q => (p, x)) = fun _ =>
        (0 : Q →L[ℝ] P).prod (ContinuousLinearMap.id ℝ Q) := by
      funext x
      exact (hDf x).fderiv
    rw [he]
    exact (hasFDerivAt_const (𝕜 := ℝ)
      ((0 : Q →L[ℝ] P).prod (ContinuousLinearMap.id ℝ Q)) q).fderiv
  simpa only [Function.comp_def, hd, hdd, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.zero_apply, ContinuousLinearMap.id_apply, map_zero, add_zero] using hh

end Yau.Blueprint.V03Proof
