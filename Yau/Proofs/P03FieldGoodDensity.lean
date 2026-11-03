import Yau.Proofs.P03FieldGoodSets
import Yau.Proofs.P03CompactSpanningFields
import Yau.Proofs.P03SpanParameterDensity
import Yau.Proofs.P03SectionArrayRestriction
import Yau.Proofs.P03ParameterDimensionBounds
import Yau.Proofs.P03Dimension

open scoped Manifold Topology
open Set

noncomputable section

namespace Yau.NodeProofs.P03Aux

variable {n : ℕ} {M : ComplexManifold n} {ι : Type*}

theorem fieldGoodSet_dense (a : ι → M.Carrier) (r : ι → ℝ)
    (hsub : ∀ i, chartClosedBall (a i) (r i) ⊆ chartTarget (a i))
    (hcover : ∀ x : M.Carrier, ∃ i,
      x ∈ (extChartAt (ComplexModel n) (a i)).source ∧
      chartPt (a i) x ∈ Metric.ball (chartPt (a i) (a i)) (r i))
    (hjets : ∀ (pts : Finset M.Carrier) (k : ℕ)
      (Pj : M.Carrier → Fin n → MvPolynomial (Fin n) ℂ),
      ∃ V : VectorField M, IsHolomorphicField V ∧ ∀ p ∈ pts, JetAgreeField V p (Pj p) k)
    (i : ι) : Dense (fieldGoodSet a r (2 * n) i) := by
  classical
  intro base
  let K : Set M.Carrier := chartInv (a i) '' chartClosedBall (a i) (r i)
  have hK : IsCompact K := compactChartBall_isCompact (a i) (hsub i)
  obtain ⟨L, W, hW, hspan⟩ := exists_fields_spanning_on_compact hjets K hK
  let Wq : Fin L → closedSectionArrays a r := fun l => fieldClosedSectionArray a r hsub (W l) (hW l)
  let V : Fin (2 * n) → VectorField M := fun j => sectionArrayField a r hcover (base j)
  have hV (j : Fin (2 * n)) : IsHolomorphicField (V j) :=
    sectionArrayField_holomorphic a r hcover (base j) hsub
  let Vc : ComplexVector n → Fin (2 * n) → ComplexVector n := fun z j => fieldCoords (V j) (a i) z
  let Wc : ComplexVector n → Fin L → ComplexVector n := fun z l => fieldCoords (W l) (a i) z
  let U : Set (ComplexVector n) := chartTarget (a i) ∩
    {z | Submodule.span ℂ (range (Wc z)) = ⊤}
  have hWo (l : Fin L) : DifferentiableOn ℂ (fun z => Wc z l) (chartTarget (a i)) :=
    (holomorphicField_iff_chartDifferentiable (W l)).mp (hW l) (a i)
  have hU : IsOpen U := isOpen_finite_span_top_inter Wc (isOpen_extChartAt_target (a i))
    (fun l => (hWo l).continuousOn)
  have hVdiff (j : Fin (2 * n)) : DifferentiableOn ℝ (fun z => Vc z j) U :=
    (((holomorphicField_iff_chartDifferentiable (V j)).mp (hV j) (a i)).restrictScalars ℝ).mono
      inter_subset_left
  have hWdiff (l : Fin L) : DifferentiableOn ℝ (fun z => Wc z l) U :=
    ((hWo l).restrictScalars ℝ).mono inter_subset_left
  have hpar := dense_spanning_affine_parameters Vc Wc hU hVdiff hWdiff
    (fun z hz => hz.2) (field_span_dimension_bound (dimension_pos M))
  have hzinU (z : chartClosedBall (a i) (r i)) : z.1 ∈ U := by
    have hzt := hsub i z.2
    have hx := (extChartAt (ComplexModel n) (a i)).map_target hzt
    refine ⟨hzt, ?_⟩
    exact (span_top_iff_tangentCoords (a i) (chartInv (a i) z) hx
      (fun l => W l (chartInv (a i) z))).mpr
        (hspan (chartInv (a i) z) ⟨z, z.2, rfl⟩)
  have hbase (z : chartClosedBall (a i) (r i)) (j : Fin (2 * n)) :
      Vc z.1 j = (base j).1 i z :=
    (fieldCoords_sectionArrayField_eq a r hcover (base j) hsub i z.2).trans (dif_pos z.2)
  have hdense : Dense ((finiteAffinePerturbation base Wq) ⁻¹' fieldGoodSet a r (2 * n) i) := by
    apply hpar.mono
    intro T hT
    change ∀ z : chartClosedBall (a i) (r i),
      Submodule.span ℂ (range fun j => (finiteAffinePerturbation base Wq T j).1 i z) = ⊤
    intro z
    have hvalues : (fun j => (finiteAffinePerturbation base Wq T j).1 i z) =
        affineVectorTuple (Vc z.1) (Wc z.1) T := by
      funext j
      rw [sectionCoordinates_finiteAffinePerturbation]
      change (base j).1 i z + ∑ l, T j l • (Wq l).1 i z =
        Vc z.1 j + ∑ l, T j l • Wc z.1 l
      rw [hbase]
      rfl
    rw [hvalues]
    exact hT z.1 (hzinU z)
  exact finiteAffinePerturbation_mem_closure base Wq hdense

end Yau.NodeProofs.P03Aux
