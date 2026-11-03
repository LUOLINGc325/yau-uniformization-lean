import Yau.Proofs.V03VectorAreaSum

/-! Component evaluation of a native finite Euclidean within derivative. -/

noncomputable section
namespace Yau.Blueprint.V03Proof

theorem fderivWithin_euclidean_component {E ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [Fintype ι]
    {f : E → EuclideanSpace ℂ ι} {S : Set E} {z : E}
    (hS : UniqueDiffWithinAt ℂ S z) (hf : DifferentiableWithinAt ℂ f S z) (v : E) (i : ι) :
    fderivWithin ℂ (fun x => f x i) S z v = fderivWithin ℂ f S z v i := by
  have hd := (hasFDerivWithinAt_piLp 2).mp hf.hasFDerivWithinAt i
  exact congrArg (fun A : E →L[ℂ] ℂ => A v) (hd.fderivWithin hS)

end Yau.Blueprint.V03Proof
