import Yau.Proofs.F05BootstrapDefinitions
import Mathlib.Analysis.Calculus.UniformLimitsDeriv

/-! Uniform limits of genuine derivative fields remain actual derivatives
on a closed convex set, including its boundary. The proof first identifies
the derivative in the open interior and then takes its actual boundary limit. -/

open Set Filter
open scoped Topology
noncomputable section
namespace Yau.Proofs.F05Aux

theorem F05_uniform_derivative_closed_convex
    {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    {X : Set E} (hcX : Convex ℝ X) (hClosure : closure (interior X) = X)
    {f : ℕ → E → V} {A : ℕ → E → E →L[ℝ] V}
    {fLim : E → V} {ALim : E → E →L[ℝ] V}
    (hf : ∀ k, ContinuousOn (f k) X) (hA : ∀ k, ContinuousOn (A k) X)
    (hDeriv : ∀ k x, x ∈ X → HasFDerivWithinAt (f k) (A k x) X x)
    (hLim : TendstoUniformlyOn f fLim atTop X)
    (hALim : TendstoUniformlyOn A ALim atTop X) {x : E} (hx : x ∈ X) :
    HasFDerivWithinAt fLim (ALim x) X x := by
  have hfLim : ContinuousOn fLim X :=
    hLim.continuousOn (Frequently.of_forall hf)
  have hContinuousA : ContinuousOn ALim X :=
    hALim.continuousOn (Frequently.of_forall hA)
  have hInterior (y : E) (hy : y ∈ interior X) : HasFDerivAt fLim (ALim y) y := by
    apply hasFDerivAt_of_tendstoUniformlyOn isOpen_interior
      (hALim.mono interior_subset)
    · intro k z hz
      exact (hDeriv k z (interior_subset hz)).hasFDerivAt
        (mem_of_superset (isOpen_interior.mem_nhds hz) interior_subset)
    · intro z hz
      exact hLim.tendsto_at (interior_subset hz)
    · exact hy
  rw [← hClosure]
  apply hasFDerivWithinAt_closure_of_tendsto_fderiv
    (fun y hy => (hInterior y hy).differentiableAt.differentiableWithinAt)
    hcX.interior isOpen_interior
  · intro y hy
    rw [hClosure] at hy
    exact (hfLim y hy).mono interior_subset
  · apply ((hContinuousA x hx).mono interior_subset).congr'
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact (hInterior y hy).fderiv.symm

end Yau.Proofs.F05Aux
