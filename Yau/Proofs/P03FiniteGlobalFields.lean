import Yau.Proofs.P03FieldGoodDensity
import Yau.Proofs.P03SectionArrayAtlas

open scoped Manifold Topology
open Set

noncomputable section

namespace Yau.NodeProofs.P03Aux

/-- One finite tuple of genuine holomorphic tangent fields spans every
intrinsic fibre. The only interpolation premise is the original finite-jet
clause, and one Baire choice is made before the arbitrary point. -/
theorem finite_spanning_tuple_of_field_jets {n : ℕ} (M : ComplexManifold n)
    (hjets : ∀ (pts : Finset M.Carrier) (k : ℕ)
      (Pj : M.Carrier → Fin n → MvPolynomial (Fin n) ℂ),
      ∃ V : VectorField M, IsHolomorphicField V ∧ ∀ p ∈ pts, JetAgreeField V p (Pj p) k) :
    ∃ V : Fin (2 * n) → VectorField M,
      (∀ j, IsHolomorphicField (V j)) ∧
      ∀ x, Submodule.span ℂ (range fun j => V j x) = ⊤ := by
  classical
  obtain ⟨T, hT, r, hr, hsub, hcover⟩ := exists_countable_section_array_atlas M
  letI : Countable T := hT.to_subtype
  let a : T → M.Carrier := Subtype.val
  letI : BaireSpace (Fin (2 * n) → closedSectionArrays a r) := sectionArrayTuple_baire a r (2 * n)
  letI : Nonempty (Fin (2 * n) → closedSectionArrays a r) := ⟨0⟩
  obtain ⟨b, hb⟩ := exists_mem_all_open_dense (fieldGoodSet a r (2 * n))
    (fieldGoodSet_isOpen a r (2 * n)) (fieldGoodSet_dense a r hsub hcover hjets)
  let V : Fin (2 * n) → VectorField M := fun j => sectionArrayField a r hcover (b j)
  refine ⟨V, (fun j => sectionArrayField_holomorphic a r hcover (b j) hsub), ?_⟩
  intro x
  obtain ⟨i, hxs, hxi⟩ := hcover x
  let z : chartClosedBall (a i) (r i) := ⟨chartPt (a i) x, Metric.ball_subset_closedBall hxi⟩
  have hsp : Submodule.span ℂ (range fun j => (b j).1 i z) = ⊤ := hb i z
  have hvalues : (fun j => tangentCoords (a i) x (V j x)) = (fun j => (b j).1 i z) := by
    funext j
    calc
      tangentCoords (a i) x (V j x) = fieldCoords (V j) (a i) (chartPt (a i) x) :=
        (fieldCoords_at_chartPt (V j) (a i) x hxs).symm
      _ = (b j).1 i z :=
        (fieldCoords_sectionArrayField_eq a r hcover (b j) hsub i z.2).trans (dif_pos z.2)
  rw [← hvalues] at hsp
  exact (span_top_iff_tangentCoords (a i) x hxs (fun j => V j x)).mp hsp

end Yau.NodeProofs.P03Aux
