import Yau.Proofs.P03SpanContinuity
import Yau.Proofs.P03FieldChartCriteria

open scoped Manifold Topology
open Set

noncomputable section

namespace Yau.NodeProofs.P03Aux

variable {n m : ℕ} {M : ComplexManifold n}

theorem fieldCoords_at_chartPt (V : VectorField M) (a x : M.Carrier)
    (hx : x ∈ (extChartAt (ComplexModel n) a).source) :
    fieldCoords V a (chartPt a x) = tangentCoords a x (V x) := by
  change tangentCoords a
    ((extChartAt (ComplexModel n) a).symm ((extChartAt (ComplexModel n) a) x))
    (V ((extChartAt (ComplexModel n) a).symm ((extChartAt (ComplexModel n) a) x))) = _
  rw [(extChartAt (ComplexModel n) a).left_inv hx]

/-- Finite spanning by fixed genuine holomorphic tangent fields is an open
condition on the actual manifold. -/
theorem isOpen_field_span_locus (V : Fin m → VectorField M)
    (hV : ∀ i, IsHolomorphicField (V i)) :
    IsOpen {x : M.Carrier | Submodule.span ℂ (range fun i => V i x) = ⊤} := by
  apply isOpen_iff_forall_mem_open.mpr
  intro x hx
  let O : Set (ComplexVector n) := chartTarget x ∩
    {z | Submodule.span ℂ (range fun i => fieldCoords (V i) x z) = ⊤}
  have hO : IsOpen O := isOpen_finite_span_top_inter
    (fun z i => fieldCoords (V i) x z) (isOpen_extChartAt_target x)
    (fun i => ((holomorphicField_iff_chartDifferentiable (V i)).mp (hV i) x).continuousOn)
  let B : Set M.Carrier := (extChartAt (ComplexModel n) x).source ∩ (chartPt x) ⁻¹' O
  have hB : IsOpen B := isOpen_extChartAt_preimage' x hO
  have hvalues (y : M.Carrier) (hy : y ∈ (extChartAt (ComplexModel n) x).source) :
      (fun i => fieldCoords (V i) x (chartPt x y)) = (fun i => tangentCoords x y (V i y)) :=
    funext (fun i => fieldCoords_at_chartPt (V i) x y hy)
  refine ⟨B, ?_, hB, ?_⟩
  · intro y hy
    have hc := hy.2.2
    change Submodule.span ℂ (range fun i => fieldCoords (V i) x (chartPt x y)) = ⊤ at hc
    rw [hvalues y hy.1] at hc
    exact (span_top_iff_tangentCoords x y hy.1 (fun i => V i y)).mp hc
  · refine ⟨mem_extChartAt_source x, mem_extChartAt_target x, ?_⟩
    change Submodule.span ℂ (range fun i => fieldCoords (V i) x (chartPt x x)) = ⊤
    rw [hvalues x (mem_extChartAt_source x)]
    exact (span_top_iff_tangentCoords x x (mem_extChartAt_source x) (fun i => V i x)).mpr hx

end Yau.NodeProofs.P03Aux
