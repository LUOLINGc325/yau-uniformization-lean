import Yau.Proofs.V03MetricTime

/-! Partial derivatives in an open spatial factor agree with the actual
joint within derivative, even at an endpoint of the parameter domain. -/

open scoped Topology ContDiff

noncomputable section
namespace Yau.Blueprint.V03Proof

variable {E P F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem hasFDerivAt_spatial_slice {S : Set E} (hS : IsOpen S) {J : Set P}
    {f : E × P → F} {z : E} {t : P} (hz : z ∈ S) (ht : t ∈ J)
    (hf : DifferentiableWithinAt ℝ f (S ×ˢ J) (z, t)) :
    HasFDerivAt (fun x => f (x, t))
      ((fderivWithin ℝ f (S ×ˢ J) (z, t)).comp
        ((ContinuousLinearMap.id ℝ E).prod (0 : E →L[ℝ] P))) z := by
  have hinc : HasFDerivWithinAt (fun x : E => (x, t))
      ((ContinuousLinearMap.id ℝ E).prod (0 : E →L[ℝ] P)) S z :=
    ((hasFDerivAt_id z).prodMk (hasFDerivAt_const (𝕜 := ℝ) t z)).hasFDerivWithinAt
  have hmaps : Set.MapsTo (fun x : E => (x, t)) S (S ×ˢ J) := fun x hx => ⟨hx, ht⟩
  have hh := hf.hasFDerivWithinAt.comp z hinc hmaps
  exact hh.hasFDerivAt (hS.mem_nhds hz)

theorem fderiv_spatial_slice {S : Set E} (hS : IsOpen S) {J : Set P}
    {f : E × P → F} {z : E} {t : P} (hz : z ∈ S) (ht : t ∈ J)
    (hf : DifferentiableWithinAt ℝ f (S ×ˢ J) (z, t)) (v : E) :
    fderiv ℝ (fun x => f (x, t)) z v =
      fderivWithin ℝ f (S ×ˢ J) (z, t) (v, 0) := by
  have hh := congrArg (fun A : E →L[ℝ] F => A v) (hasFDerivAt_spatial_slice hS hz ht hf).fderiv
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.zero_apply] using hh

theorem partialFDeriv_contDiffOn {S : Set E} {J : Set P} {f : E × P → F}
    (hSJ : UniqueDiffOn ℝ (S ×ˢ J)) (hf : ContDiffOn ℝ ∞ f (S ×ˢ J)) (v : E) :
    ContDiffOn ℝ ∞ (fun p => fderivWithin ℝ f (S ×ˢ J) p (v, 0)) (S ×ˢ J) := by
  exact (hf.fderivWithin hSJ (m := ∞) (by simp)).clm_apply contDiffOn_const

end Yau.Blueprint.V03Proof
