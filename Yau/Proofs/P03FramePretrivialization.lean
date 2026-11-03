import Yau.Geometry.HolomorphicBundle

open scoped Manifold Topology Bundle
open Bundle Topology

noncomputable section

namespace Yau.NodeProofs.P03Aux

variable {n r : ℕ} {M : ComplexManifold n}
variable (E : M.Carrier → Type*) [∀ x, TopologicalSpace (E x)]
  [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
variable (coordinate : ∀ (a x : M.Carrier),
  x ∈ (extChartAt (ComplexModel n) a).source → E x ≃L[ℂ] ComplexVector r)

/-- A local fibre equivalence over each actual chart gives a linear
pretrivialization, extended by zero outside that chart. -/
def chartCoordinatePretrivialization (a : M.Carrier) :
    Pretrivialization (ComplexVector r) (π (ComplexVector r) E) := by
  classical
  exact
    { toFun := fun p => ⟨p.1,
        if hx : p.1 ∈ (extChartAt (ComplexModel n) a).source then
          coordinate a p.1 hx p.2 else 0⟩
      invFun := fun p => ⟨p.1,
        if hx : p.1 ∈ (extChartAt (ComplexModel n) a).source then
          (coordinate a p.1 hx).symm p.2 else 0⟩
      source := (π (ComplexVector r) E) ⁻¹' (extChartAt (ComplexModel n) a).source
      target := (extChartAt (ComplexModel n) a).source ×ˢ Set.univ
      map_source' := by rintro ⟨x, v⟩ hx; exact ⟨hx, Set.mem_univ _⟩
      map_target' := by rintro ⟨x, v⟩ hx; exact hx.1
      left_inv' := by
        rintro ⟨x, v⟩ hx
        simp only [Set.mem_preimage] at hx
        simp only [dite_eq_left hx, ContinuousLinearEquiv.symm_apply_apply]
      right_inv' := by
        rintro ⟨x, v⟩ ⟨hx, _⟩
        simp only [dite_eq_left hx, ContinuousLinearEquiv.apply_symm_apply]
      open_target := by
        have h : IsOpen (extChartAt (ComplexModel n) a).source := by
          simpa only [extChartAt_source] using (chartAt (ComplexVector n) a).open_source
        exact h.prod isOpen_univ
      baseSet := (extChartAt (ComplexModel n) a).source
      open_baseSet := by simpa only [extChartAt_source] using
        (chartAt (ComplexVector n) a).open_source
      source_eq := rfl
      target_eq := rfl
      proj_toFun := by intros; rfl }

@[simp] theorem chartCoordinatePretrivialization_baseSet (a : M.Carrier) :
    (chartCoordinatePretrivialization E coordinate a).baseSet =
      (extChartAt (ComplexModel n) a).source := rfl

theorem chartCoordinatePretrivialization_apply (a x : M.Carrier)
    (hx : x ∈ (extChartAt (ComplexModel n) a).source) (v : E x) :
    chartCoordinatePretrivialization E coordinate a ⟨x, v⟩ = (x, coordinate a x hx v) := by
  classical
  simp only [chartCoordinatePretrivialization, Pretrivialization.toFun', dite_eq_left hx]

theorem chartCoordinatePretrivialization_symm (a x : M.Carrier)
    (hx : x ∈ (extChartAt (ComplexModel n) a).source) (v : ComplexVector r) :
    (chartCoordinatePretrivialization E coordinate a).symm x v =
      (coordinate a x hx).symm v := by
  classical
  apply (coordinate a x hx).injective
  rw [ContinuousLinearEquiv.apply_symm_apply]
  have h := (chartCoordinatePretrivialization E coordinate a).apply_mk_symm hx v
  rw [chartCoordinatePretrivialization_apply E coordinate a x hx] at h
  exact congrArg Prod.snd h

instance chartCoordinatePretrivialization_isLinear (a : M.Carrier) :
    (chartCoordinatePretrivialization E coordinate a).IsLinear ℂ where
  linear x hx := by
    classical
    refine ⟨?_, ?_⟩
    · intro v w
      simp only [chartCoordinatePretrivialization_apply E coordinate a x hx, map_add]
    · intro c v
      simp only [chartCoordinatePretrivialization_apply E coordinate a x hx, map_smul]

theorem chartCoordinatePretrivialization_isInducing (x : M.Carrier) :
    IsInducing (chartCoordinatePretrivialization E coordinate x ∘ TotalSpace.mk x) := by
  have h := (coordinate x x (mem_extChartAt_source x)).toHomeomorph.isInducing
  have he : (chartCoordinatePretrivialization E coordinate x ∘ TotalSpace.mk x) =
      fun v => (x, coordinate x x (mem_extChartAt_source x) v) := by
    funext v
    exact chartCoordinatePretrivialization_apply E coordinate x x (mem_extChartAt_source x) v
  rw [he]
  exact isInducing_const_prod.mpr h

end Yau.NodeProofs.P03Aux
