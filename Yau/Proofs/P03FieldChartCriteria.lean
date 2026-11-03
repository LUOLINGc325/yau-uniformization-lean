import Yau.Proofs.P03HolomorphicChartCriteria

open scoped Manifold Topology
open Bundle Filter

noncomputable section

namespace Yau.NodeProofs.P03Aux

variable {n : ℕ} {M : ComplexManifold n}

theorem mdifferentiableAt_iff_inChart {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℂ F] (f : M.Carrier → F) (a x : M.Carrier)
    (hx : x ∈ (extChartAt (ComplexModel n) a).source) :
    MDifferentiableAt (ComplexModel n) 𝓘(ℂ, F) f x ↔
      DifferentiableAt ℂ (inChart a f) (chartPt a x) := by
  have hx' : x ∈ (chartAt (ComplexVector n) a).source := by
    simpa only [extChartAt_source] using hx
  rw [mdifferentiableAt_iff_source_of_mem_source
    (I := ComplexModel n) (I' := 𝓘(ℂ, F)) hx',
    ModelWithCorners.range_eq_univ, mdifferentiableWithinAt_univ,
    mdifferentiableAt_iff_differentiableAt]
  rfl

def fieldSectionCoordinate (V : VectorField M) (a x : M.Carrier) : ComplexVector n :=
  (trivializationAt (ComplexVector n) (TangentSpace (ComplexModel n)) a ⟨x, V x⟩).2

theorem fieldSectionCoordinate_eq (V : VectorField M) (a x : M.Carrier)
    (hx : x ∈ (extChartAt (ComplexModel n) a).source) :
    fieldSectionCoordinate V a x = tangentCoords a x (V x) := by
  have ht : x ∈ (trivializationAt (ComplexVector n) (TangentSpace (ComplexModel n)) a).baseSet := by
    simpa only [TangentBundle.trivializationAt_baseSet, extChartAt_source] using hx
  change (trivializationAt (ComplexVector n) (TangentSpace (ComplexModel n)) a ⟨x, V x⟩).2 = _
  rw [← Trivialization.continuousLinearMapAt_apply_of_mem (R := ℂ) _ ht,
    TangentBundle.continuousLinearMapAt_trivializationAt
      (by simpa only [extChartAt_source] using hx)]
  rfl

theorem field_mdifferentiableAt_iff (V : VectorField M) (a x : M.Carrier)
    (hx : x ∈ (extChartAt (ComplexModel n) a).source) :
    MDifferentiableAt (ComplexModel n) (ComplexModel n).tangent
      (fun p => (⟨p, V p⟩ : TangentBundle (ComplexModel n) M.Carrier)) x ↔
      DifferentiableAt ℂ (fieldCoords V a) (chartPt a x) := by
  have ht : x ∈ (trivializationAt (ComplexVector n) (TangentSpace (ComplexModel n)) a).baseSet := by
    simpa only [TangentBundle.trivializationAt_baseSet, extChartAt_source] using hx
  have hs : MDifferentiableAt (ComplexModel n) (ComplexModel n).tangent
      (fun p => (⟨p, V p⟩ : TangentBundle (ComplexModel n) M.Carrier)) x ↔
      MDifferentiableAt (ComplexModel n) (ComplexModel n) (fieldSectionCoordinate V a) x :=
    (trivializationAt (ComplexVector n) (TangentSpace (ComplexModel n)) a).mdifferentiableAt_section_iff
      (ComplexModel n) V ht
  rw [hs, mdifferentiableAt_iff_inChart (fieldSectionCoordinate V a) a x hx]
  have he : inChart a (fieldSectionCoordinate V a) =ᶠ[𝓝 (chartPt a x)] fieldCoords V a := by
    apply Filter.eventually_of_mem ((isOpen_extChartAt_target a).mem_nhds
      ((extChartAt (ComplexModel n) a).map_source hx))
    intro z hz
    exact fieldSectionCoordinate_eq V a (chartInv a z) ((extChartAt (ComplexModel n) a).map_target hz)
  exact he.differentiableAt_iff

theorem holomorphicField_iff_chartDifferentiable (V : VectorField M) :
    IsHolomorphicField V ↔
      ∀ a : M.Carrier, DifferentiableOn ℂ (fieldCoords V a) (chartTarget a) := by
  constructor
  · intro hV a z hz
    have hd := (field_mdifferentiableAt_iff V a (chartInv a z)
      ((extChartAt (ComplexModel n) a).map_target hz)).mp (hV (chartInv a z))
    have hi : chartPt a (chartInv a z) = z := (extChartAt (ComplexModel n) a).right_inv hz
    apply DifferentiableAt.differentiableWithinAt
    simpa only [hi] using hd
  · intro hV p
    apply (field_mdifferentiableAt_iff V p p (mem_extChartAt_source p)).mpr
    exact (hV p).differentiableAt
      ((isOpen_extChartAt_target p).mem_nhds (mem_extChartAt_target p))

end Yau.NodeProofs.P03Aux
