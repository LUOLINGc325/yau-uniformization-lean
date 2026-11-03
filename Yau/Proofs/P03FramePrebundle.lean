import Yau.Proofs.P03FramePretrivialization

open scoped Manifold Topology Bundle ContDiff
open Bundle Topology

noncomputable section

namespace Yau.NodeProofs.P03Aux

variable {n r : ℕ} {M : ComplexManifold n}
variable (E : M.Carrier → Type*) [∀ x, TopologicalSpace (E x)]
  [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
variable (coordinate : ∀ (a x : M.Carrier),
  x ∈ (extChartAt (ComplexModel n) a).source → E x ≃L[ℂ] ComplexVector r)
variable (transition : M.Carrier → M.Carrier → M.Carrier →
  ComplexVector r →L[ℂ] ComplexVector r)
variable (hcontinuous : ∀ a b, ContinuousOn (transition a b)
  ((extChartAt (ComplexModel n) a).source ∩ (extChartAt (ComplexModel n) b).source))
variable (hcoordinate : ∀ (a b x : M.Carrier)
  (ha : x ∈ (extChartAt (ComplexModel n) a).source)
  (hb : x ∈ (extChartAt (ComplexModel n) b).source) (v : ComplexVector r),
  transition a b x v = coordinate b x hb ((coordinate a x ha).symm v))

/-- Assemble the concrete chart coordinates with their proved transition maps.
The resulting atlas contains exactly these chart pretrivializations. -/
def chartCoordinateVectorPrebundle : VectorPrebundle ℂ (ComplexVector r) E where
  pretrivializationAtlas := Set.range (chartCoordinatePretrivialization E coordinate)
  pretrivialization_linear' := by rintro _ ⟨a, rfl⟩; infer_instance
  pretrivializationAt := chartCoordinatePretrivialization E coordinate
  mem_base_pretrivializationAt := mem_extChartAt_source
  pretrivialization_mem_atlas := Set.mem_range_self
  exists_coordChange := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    refine ⟨transition a b, hcontinuous a b, ?_⟩
    intro x hx v
    rw [chartCoordinatePretrivialization_symm E coordinate a x hx.1,
      chartCoordinatePretrivialization_apply E coordinate b x hx.2]
    exact hcoordinate a b x hx.1 hx.2 v
  totalSpaceMk_isInducing := chartCoordinatePretrivialization_isInducing E coordinate

theorem chartCoordinateVectorPrebundle_isContMDiff
    (hregular : ∀ a b,
      ContMDiffOn (ComplexModel n) 𝓘(ℂ, ComplexVector r →L[ℂ] ComplexVector r) ⊤
        (transition a b)
        ((extChartAt (ComplexModel n) a).source ∩
          (extChartAt (ComplexModel n) b).source)) :
    (chartCoordinateVectorPrebundle E coordinate transition hcontinuous hcoordinate).IsContMDiff
      (ComplexModel n) ⊤ := by
  constructor
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
  refine ⟨transition a b, hregular a b, ?_⟩
  intro x hx v
  rw [chartCoordinatePretrivialization_symm E coordinate a x hx.1,
    chartCoordinatePretrivialization_apply E coordinate b x hx.2]
  exact hcoordinate a b x hx.1 hx.2 v

end Yau.NodeProofs.P03Aux
