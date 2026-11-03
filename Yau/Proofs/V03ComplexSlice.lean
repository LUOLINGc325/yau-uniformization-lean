import Yau.Proofs.V03ComplexCompactTrace

/-! A parameter slice in an open complex factor has the genuine complex
derivative of the joint within map, even at the other factor's boundary. -/

open scoped Topology ContDiff

noncomputable section
namespace Yau.Blueprint.V03Proof

variable {E P F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup P] [NormedSpace ℂ P]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem hasFDerivAt_complex_parameter_slice {U : Set E} (hU : IsOpen U) {J : Set P}
    {f : E × P → F} {z : E} {t : P} (hz : z ∈ U) (ht : t ∈ J)
    (hf : DifferentiableWithinAt ℂ f (U ×ˢ J) (z, t)) :
    HasFDerivAt (fun x => f (x, t))
      ((fderivWithin ℂ f (U ×ˢ J) (z, t)).comp
        ((ContinuousLinearMap.id ℂ E).prod (0 : E →L[ℂ] P))) z := by
  have hinc : HasFDerivWithinAt (fun x : E => (x, t))
      ((ContinuousLinearMap.id ℂ E).prod (0 : E →L[ℂ] P)) U z :=
    ((hasFDerivAt_id z).prodMk (hasFDerivAt_const (𝕜 := ℂ) t z)).hasFDerivWithinAt
  have hmap : Set.MapsTo (fun x : E => (x, t)) U (U ×ˢ J) := fun x hx => ⟨hx, ht⟩
  exact (hf.hasFDerivWithinAt.comp z hinc hmap).hasFDerivAt (hU.mem_nhds hz)

theorem fderiv_complex_parameter_slice {U : Set E} (hU : IsOpen U) {J : Set P}
    {f : E × P → F} {z : E} {t : P} (hz : z ∈ U) (ht : t ∈ J)
    (hf : DifferentiableWithinAt ℂ f (U ×ˢ J) (z, t)) (v : E) :
    fderiv ℂ (fun x => f (x, t)) z v = fderivWithin ℂ f (U ×ˢ J) (z, t) (v, 0) := by
  have hh := congrArg (fun A : E →L[ℂ] F => A v)
    (hasFDerivAt_complex_parameter_slice hU hz ht hf).fderiv
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.zero_apply] using hh

end Yau.Blueprint.V03Proof
