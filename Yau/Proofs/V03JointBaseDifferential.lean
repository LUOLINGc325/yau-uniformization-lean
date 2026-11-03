import Yau.Proofs.V03JointCotangentDifferential
import Yau.Proofs.V03Transitions

/-! Actual joint base-chart within derivatives obey the genuine manifold
coordinate change law, also at the original spatial circle. -/

open scoped Manifold Topology ContDiff
open Filter

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

theorem cotangentHolomorphicOn_fderivWithin_base_change {n : ℕ} {M : ComplexManifold n}
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P]
    {f : P → CotangentPoint M} {S : Set P} (hf : CotangentHolomorphicOn f S)
    {p : P} (hp : p ∈ S) (hS : UniqueDiffWithinAt ℂ S p)
    (x x' : M.Carrier) (hx : f p ∈ cotangentSource x) (hx' : f p ∈ cotangentSource x') :
    fderivWithin ℂ (fun r => chartPt x' (f r).1) S p =
      (tangentCoordChange (ComplexModel n) x x' (f p).1).comp
        (fderivWithin ℂ (fun r => chartPt x (f r).1) S p) := by
  let c : P → ComplexVector n := fun r => chartPt x (f r).1
  let T : ComplexVector n → ComplexVector n := fun z => chartPt x' (chartInv x z)
  have hb : chartInv x (c p) = (f p).1 := (extChartAt (ComplexModel n) x).left_inv hx
  have ht : c p ∈ chartTarget x := (extChartAt (ComplexModel n) x).map_source hx
  have hT : DifferentiableAt ℂ T (c p) :=
    (chartTransition_contDiffAt x x' ht (by rw [hb]; exact hx')).differentiableAt (by simp)
  have hc : DifferentiableWithinAt ℂ c S p :=
    (cotangentHolomorphicOn_coords_contDiffWithinAt hf hp x hx).fst.differentiableWithinAt (by simp)
  have hs : ∀ᶠ r in 𝓝[S] p, f r ∈ cotangentSource x :=
    (hf.1 p hp).continuousWithinAt.preimage_mem_nhdsWithin
      ((isOpen_extChartAt_source (I := ComplexModel n) x).mem_nhds hx)
  have he : (fun r => chartPt x' (f r).1) =ᶠ[𝓝[S] p] T ∘ c := by
    filter_upwards [hs] with r hr
    exact congrArg (chartPt x') ((extChartAt (ComplexModel n) x).left_inv hr).symm
  rw [he.fderivWithin_eq_of_mem hp, fderiv_comp_fderivWithin p hT hc hS]
  have hDT := chartTransition_fderiv_eq_coordChange x x' ht
  rw [hb] at hDT
  rw [hDT]

end Yau.Blueprint.V03Proof
