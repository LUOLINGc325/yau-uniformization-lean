import Yau.Proofs.P03ChartDifferentials
import Yau.Proofs.P03FirstJets
import Yau.Proofs.P03HolomorphicEvaluation
import Yau.Proofs.P03DerivativeEvaluation

open scoped Manifold Topology

noncomputable section

namespace Yau.NodeProofs.P03Aux

variable {n : ℕ} {M : ComplexManifold n}

theorem chartDerivative_change_frame {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (f : M.Carrier → F) (hf : MDifferentiable (ComplexModel n) 𝓘(ℂ, F) f)
    (a x : M.Carrier) (hx : x ∈ (extChartAt (ComplexModel n) a).source) :
    fderiv ℂ (inChart a f) (chartPt a x) =
      (fderiv ℂ (inChart x f) (chartPt x x)).comp
        ((chartFrameEquiv a x hx).trans
          (chartFrameEquiv x x (mem_extChartAt_source x)).symm).toContinuousLinearMap := by
  rw [chartDerivative_eq_intrinsic_comp f hf a x hx,
    chartDerivative_eq_intrinsic_comp f hf x x (mem_extChartAt_source x)]
  ext v
  change mfderiv (ComplexModel n) 𝓘(ℂ, F) f x (chartVec a x v) =
    mfderiv (ComplexModel n) 𝓘(ℂ, F) f x
      (chartVec x x (tangentCoords x x (chartVec a x v)))
  rw [chartVec_tangentCoords x x (mem_extChartAt_source x)]

/-- Original scalar first jets produce global functions whose differentials
are injective in any prescribed genuine chart at the chosen point. -/
theorem scalar_jets_injective_chart_differentials
    (hjets : ∀ (pts : Finset M.Carrier) (k : ℕ)
      (Pj : M.Carrier → MvPolynomial (Fin n) ℂ),
      ∃ f, IsHolomorphicFn f ∧ ∀ p ∈ pts, JetAgreeFn f p (Pj p) k)
    (a x : M.Carrier) (hx : x ∈ (extChartAt (ComplexModel n) a).source) :
    ∃ f : Fin n → holomorphicFunctions M,
      Function.Injective (tupleDerivativeCLM a f (chartPt a x)) := by
  classical
  obtain ⟨g, hg, hDg⟩ := scalar_jets_coordinate_differentials hjets x
  let f : Fin n → holomorphicFunctions M := fun i => holomorphicFunctionOf (g i) (hg i)
  let T := (chartFrameEquiv a x hx).trans
    (chartFrameEquiv x x (mem_extChartAt_source x)).symm
  refine ⟨f, ?_⟩
  intro v w h
  apply T.injective
  ext i
  have hi := congrFun h i
  change fderiv ℂ (inChart a (g i)) (chartPt a x) v =
    fderiv ℂ (inChart a (g i)) (chartPt a x) w at hi
  have he := chartDerivative_change_frame (g i) (hg i) a x hx
  rw [hDg i] at he
  rw [he] at hi
  exact hi

end Yau.NodeProofs.P03Aux
