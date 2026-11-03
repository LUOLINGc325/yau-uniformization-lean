import Yau.Proofs.P03ImmersionGoodSets
import Yau.Proofs.P03CompactScalarFrames
import Yau.Proofs.P03DerivativeParameterLinearity
import Yau.Proofs.P03SpanParameterDensity
import Yau.Proofs.P03SpanContinuity
import Yau.Proofs.P03ParameterDimensionBounds
import Yau.Proofs.P03Dimension

open scoped Manifold Topology
open Set

noncomputable section

namespace Yau.NodeProofs.P03Aux

variable {n : ℕ} {M : ComplexManifold n}

theorem immersionGoodSet_dense
    (hjets : ∀ (pts : Finset M.Carrier) (k : ℕ)
      (Pj : M.Carrier → MvPolynomial (Fin n) ℂ),
      ∃ f, IsHolomorphicFn f ∧ ∀ p ∈ pts, JetAgreeFn f p (Pj p) k)
    (a : M.Carrier) (K : Set (ComplexVector n))
    (hK : IsCompact K) (hsub : K ⊆ chartTarget a) :
    Dense (immersionGoodSet a K (2 * n + 1)) := by
  classical
  intro base
  obtain ⟨L, W, hspan⟩ :=
    exists_functions_derivatives_spanning_on_chart_compact hjets a K hK hsub
  let Vc : ComplexVector n → Fin (2 * n + 1) → ComplexVector n :=
    fun z j => functionDerivativeCoordinates (base j) a z
  let Wc : ComplexVector n → Fin L → ComplexVector n :=
    fun z l => functionDerivativeCoordinates (W l) a z
  let U := chartTarget a ∩ {z | Submodule.span ℂ (range (Wc z)) = ⊤}
  have hWo (l : Fin L) : DifferentiableOn ℂ (fun z => Wc z l) (chartTarget a) :=
    functionDerivativeCoordinates_differentiableOn (W l) a
  have hU : IsOpen U := isOpen_finite_span_top_inter Wc (isOpen_extChartAt_target a)
    (fun l => (hWo l).continuousOn)
  have hVdiff (j : Fin (2 * n + 1)) : DifferentiableOn ℝ (fun z => Vc z j) U :=
    ((functionDerivativeCoordinates_differentiableOn (base j) a).restrictScalars ℝ).mono
      inter_subset_left
  have hWdiff (l : Fin L) : DifferentiableOn ℝ (fun z => Wc z l) U :=
    ((hWo l).restrictScalars ℝ).mono inter_subset_left
  have hpar := dense_spanning_affine_parameters Vc Wc hU hVdiff hWdiff
    (fun z hz => hz.2) (scalar_immersion_dimension_bound (dimension_pos M))
  have hzinU (z : K) : z.1 ∈ U := ⟨hsub z.2, hspan z.1 z.2⟩
  have hdense : Dense ((finiteAffinePerturbation base W) ⁻¹' immersionGoodSet a K (2 * n + 1)) := by
    apply hpar.mono
    intro T hT
    change ∀ z : K, Function.Injective (tupleDerivativeCLM a
      (finiteAffinePerturbation base W T) z.1)
    intro z
    apply (derivativeRows_span_top_iff_tupleDerivative_injective _ a z.1).mp
    have hvalues : (fun j => functionDerivativeCoordinates
        (finiteAffinePerturbation base W T j) a z.1) =
        affineVectorTuple (Vc z.1) (Wc z.1) T := by
      funext j
      exact derivativeCoordinates_finiteAffinePerturbation base W T a z.1 (hsub z.2) j
    rw [hvalues]
    exact hT z.1 (hzinU z)
  exact finiteAffinePerturbation_mem_closure base W hdense

end Yau.NodeProofs.P03Aux
