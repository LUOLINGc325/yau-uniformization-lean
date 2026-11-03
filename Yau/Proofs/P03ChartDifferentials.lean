import Yau.Proofs.P03DeterminantFibres
import Yau.Proofs.P03HolomorphicChartCriteria

open scoped Manifold Topology

noncomputable section

namespace Yau.NodeProofs.P03Aux

variable {n : ℕ} {M : ComplexManifold n}

/-- The ordinary chart differential is the actual intrinsic manifold
differential composed with the genuine inverse-chart frame map. -/
theorem chartDerivative_eq_intrinsic_comp {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (f : M.Carrier → F) (hf : MDifferentiable (ComplexModel n) 𝓘(ℂ, F) f)
    (a x : M.Carrier) (hx : x ∈ (extChartAt (ComplexModel n) a).source) :
    fderiv ℂ (inChart a f) (chartPt a x) =
      (mfderiv (ComplexModel n) 𝓘(ℂ, F) f x).comp
        (chartFrameEquiv a x hx).toContinuousLinearMap := by
  have htarget := (extChartAt (ComplexModel n) a).map_source hx
  have hi := mdifferentiableWithinAt_extChartAt_symm (I := ComplexModel n) htarget
  rw [ModelWithCorners.range_eq_univ, mdifferentiableWithinAt_univ] at hi
  have heq : (extChartAt (ComplexModel n) a).symm ((extChartAt (ComplexModel n) a) x) = x :=
    (extChartAt (ComplexModel n) a).left_inv hx
  have hc := mfderiv_comp_of_eq (I := 𝓘(ℂ, ComplexVector n)) (I' := ComplexModel n)
    (I'' := 𝓘(ℂ, F)) (g := f) (f := (extChartAt (ComplexModel n) a).symm)
    (hf x) hi heq
  rw [heq, mfderiv_eq_fderiv] at hc
  ext v
  exact congrArg (fun L => L v) hc

end Yau.NodeProofs.P03Aux
