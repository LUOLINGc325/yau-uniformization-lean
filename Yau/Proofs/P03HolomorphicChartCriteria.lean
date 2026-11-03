import Yau.Geometry.Calculus

open scoped Manifold Topology

noncomputable section

namespace Yau.NodeProofs.P03Aux

variable {n : ℕ} {M : ComplexManifold n}

theorem mdifferentiable_iff_chartDifferentiable {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℂ F] (f : M.Carrier → F) :
    MDifferentiable (ComplexModel n) 𝓘(ℂ, F) f ↔
      ∀ a : M.Carrier, DifferentiableOn ℂ (inChart a f) (chartTarget a) := by
  constructor
  · intro hf a z hz
    have hx : chartInv a z ∈ (chartAt (ComplexVector n) a).source := by
      simpa only [extChartAt_source, chartInv] using (extChartAt (ComplexModel n) a).map_target hz
    have h := (mdifferentiableAt_iff_source_of_mem_source
      (I := ComplexModel n) (I' := 𝓘(ℂ, F)) hx).mp (hf (chartInv a z))
    rw [ModelWithCorners.range_eq_univ, mdifferentiableWithinAt_univ,
      mdifferentiableAt_iff_differentiableAt] at h
    have hi : chartPt a (chartInv a z) = z := (extChartAt (ComplexModel n) a).right_inv hz
    apply DifferentiableAt.differentiableWithinAt
    change DifferentiableAt ℂ (inChart a f) (chartPt a (chartInv a z)) at h
    simpa only [hi] using h
  · intro hf p
    rw [mdifferentiableAt_iff_source_of_mem_source
      (I := ComplexModel n) (I' := 𝓘(ℂ, F)) (mem_chart_source (ComplexVector n) p),
      ModelWithCorners.range_eq_univ, mdifferentiableWithinAt_univ,
      mdifferentiableAt_iff_differentiableAt]
    change DifferentiableAt ℂ (inChart p f) (chartPt p p)
    exact (hf p).differentiableAt
      ((isOpen_extChartAt_target p).mem_nhds (mem_extChartAt_target p))

end Yau.NodeProofs.P03Aux
