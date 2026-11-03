import Yau.Proofs.P06ScalarSmoothHeatCutoffs

/-! In complex dimension zero the original scalar Laplacian is zero,
so the genuine stationary flow satisfies the entire original heat class. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff Manifold

namespace Yau.NodeProofs.P06Aux.ScalarSmooth
open Yau Yau.Blueprint

theorem boundedScalarHeat_zeroDim {M : ComplexManifold 0} (g : HermitianField M)
    (f : M.Carrier → ℝ) (hf : SmoothFn f) (hb : ∃ C : ℝ, ∀ x, |f x| ≤ C) :
    IsBoundedScalarHeat g f (fun _ => f) := by
  obtain ⟨C,hb⟩ := hb
  refine ⟨?_,⟨rfl,?_⟩,?_,?_⟩
  · intro a
    exact (hf a).comp contDiffOn_fst (fun p hp => hp.1)
  · intro x K _ _ j ε hε
    refine ⟨1,zero_lt_one,?_⟩
    intro t _ _ z _
    have he : (fun w => inChart x f w - inChart x f w) = fun _ => (0 : ℝ) :=
      funext (fun _ => sub_self _)
    rw [he]
    simpa only [iteratedFDeriv_fun_zero,Pi.zero_apply,norm_zero] using hε
  · intro T _
    exact ⟨|C|+1,by positivity,fun x t _ _ => (hb x).trans (by linarith [le_abs_self C])⟩
  · intro x t _
    have hl : laplacian g f x = 0 := by simp [laplacian,traceWith,Matrix.trace]
    rw [hl]
    exact hasDerivAt_const t (f x)

end Yau.NodeProofs.P06Aux.ScalarSmooth
