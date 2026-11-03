import Yau.Proofs.P03PairGoodSets
import Yau.Proofs.P03CompactSeparatingFunctions
import Yau.Proofs.P03SeparationParameterDensity
import Yau.Proofs.P03FiniteAffinePerturbations
import Yau.Proofs.P03ParameterDimensionBounds

open scoped Manifold Topology
open Set

noncomputable section

namespace Yau.NodeProofs.P03Aux

variable {n : ℕ} {M : ComplexManifold n}

theorem pairGoodSet_dense
    (hjets : ∀ (pts : Finset M.Carrier) (k : ℕ)
      (Pj : M.Carrier → MvPolynomial (Fin n) ℂ),
      ∃ f, IsHolomorphicFn f ∧ ∀ p ∈ pts, JetAgreeFn f p (Pj p) k)
    (a b : M.Carrier) (K : Set (ComplexVector n × ComplexVector n))
    (hK : IsCompact K) (hsub : K ⊆ chartPairDomain a b) :
    Dense (pairGoodSet a b K (2 * n + 1)) := by
  classical
  intro base
  let C := chartPairMap a b '' K
  have hC : IsCompact C := hK.image_of_continuousOn
    ((chartPairMap_continuousOn a b).mono (fun z hz => (hsub hz).1))
  have hne : ∀ p ∈ C, p.1 ≠ p.2 := by
    rintro _ ⟨z, hz, rfl⟩
    exact (hsub hz).2
  obtain ⟨L, W, hW, hsep⟩ := exists_functions_separating_on_compact hjets C hC hne
  let Wq : Fin L → holomorphicFunctions M := fun l => holomorphicFunctionOf (W l) (hW l)
  let Vc : (ComplexVector n × ComplexVector n) → Fin (2 * n + 1) → ℂ :=
    fun z j => (base j).1 (chartInv a z.1) - (base j).1 (chartInv b z.2)
  let Wc : (ComplexVector n × ComplexVector n) → Fin L → ℂ :=
    fun z l => W l (chartInv a z.1) - W l (chartInv b z.2)
  let S := chartTarget a ×ˢ chartTarget b
  let U := S ∩ {z | ∃ l, Wc z l ≠ 0}
  have hS : IsOpen S := (isOpen_extChartAt_target a).prod (isOpen_extChartAt_target b)
  have hWo (l : Fin L) : DifferentiableOn ℂ (fun z => Wc z l) S :=
    holomorphicPairDifference_differentiableOn (Wq l) a b
  have hU : IsOpen U := by
    have ho : IsOpen {c : ℂ | c ≠ 0} := isOpen_ne
    have heq : U = ⋃ l : Fin L, S ∩ {z | Wc z l ≠ 0} := by
      ext z
      simp only [U, mem_inter_iff, mem_setOf_eq, mem_iUnion]
      aesop
    rw [heq]
    exact isOpen_iUnion (fun l => (hWo l).continuousOn.isOpen_inter_preimage hS ho)
  have hVdiff (j : Fin (2 * n + 1)) : DifferentiableOn ℝ (fun z => Vc z j) U :=
    ((holomorphicPairDifference_differentiableOn (base j) a b).restrictScalars ℝ).mono
      inter_subset_left
  have hWdiff (l : Fin L) : DifferentiableOn ℝ (fun z => Wc z l) U :=
    ((hWo l).restrictScalars ℝ).mono inter_subset_left
  have hpar := dense_separating_affine_parameters Vc Wc hU hVdiff hWdiff
    (fun z hz => hz.2) (scalar_pair_dimension_bound n)
  have hzinU (z : K) : z.1 ∈ U :=
    ⟨(hsub z.2).1, hsep (chartPairMap a b z.1) ⟨z.1, z.2, rfl⟩⟩
  have hdense : Dense ((finiteAffinePerturbation base Wq) ⁻¹' pairGoodSet a b K (2 * n + 1)) := by
    apply hpar.mono
    intro T hT
    change ∀ z : K, (fun j => (finiteAffinePerturbation base Wq T j).1
      (chartInv a z.1.1) - (finiteAffinePerturbation base Wq T j).1 (chartInv b z.1.2)) ≠ 0
    intro z
    have hvalues : (fun j => (finiteAffinePerturbation base Wq T j).1
        (chartInv a z.1.1) - (finiteAffinePerturbation base Wq T j).1 (chartInv b z.1.2)) =
        affineScalarTuple Vc Wc T z.1 := by
      funext j
      let e : holomorphicFunctions M →ₗ[ℂ] ℂ :=
        { toFun := fun f => f.1 (chartInv a z.1.1) - f.1 (chartInv b z.1.2)
          map_add' := by
            intro f g
            change (f.1 (chartInv a z.1.1) + g.1 (chartInv a z.1.1)) -
              (f.1 (chartInv b z.1.2) + g.1 (chartInv b z.1.2)) = _
            ring
          map_smul' := by
            intro c f
            change c * f.1 (chartInv a z.1.1) - c * f.1 (chartInv b z.1.2) =
              c * (f.1 (chartInv a z.1.1) - f.1 (chartInv b z.1.2))
            ring }
      exact finiteAffinePerturbation_linearMap e base Wq T j
    rw [hvalues]
    exact hT z.1 (hzinU z)
  exact finiteAffinePerturbation_mem_closure base Wq hdense

end Yau.NodeProofs.P03Aux
