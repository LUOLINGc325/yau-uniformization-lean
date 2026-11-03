import Yau.LeafProofs.L16DefiningFlattening

/-! Smooth inverse charts on genuine open sets retain all orders of regularity. -/

open Filter Set
open scoped Topology ContDiff
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency.types false

namespace Yau.Proofs.F05Aux

theorem smooth_inverse_chart {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {V : Set E} (hV : IsOpen V) (hf : ContDiffOn ℝ ∞ f V)
    {x : E} (hx : x ∈ V) {L : E ≃L[ℝ] F} (hD : HasFDerivAt f (L : E →L[ℝ] F) x) :
    ∃ c : OpenPartialHomeomorph E F, x ∈ c.source ∧ c.source ⊆ V ∧
      (c : E → F) = f ∧ ContDiffOn ℝ ∞ c c.source ∧ ContDiffOn ℝ ∞ c.symm c.target := by
  have hfAt := hf.contDiffAt (hV.mem_nhds hx)
  let c₀ := hfAt.toOpenPartialHomeomorph f hD (by simp)
  have hx₀ : x ∈ c₀.source := hfAt.mem_toOpenPartialHomeomorph_source hD (by simp)
  have hderiv := ((hf.continuousOn_fderiv_of_isOpen hV (by simp)) x hx).continuousAt
    (hV.mem_nhds hx)
  have hInv : (Set.range ((↑) : (E ≃L[ℝ] F) → E →L[ℝ] F)) ∈ 𝓝 (fderiv ℝ f x) := by
    rw [hD.fderiv]
    exact L.nhds
  have hN : V ∩ (fderiv ℝ f) ⁻¹' Set.range ((↑) : (E ≃L[ℝ] F) → E →L[ℝ] F) ∈ 𝓝 x :=
    inter_mem (hV.mem_nhds hx) (hderiv hInv)
  obtain ⟨W,hWsub,hWo,hxW⟩ := mem_nhds_iff.mp hN
  let c := c₀.restrOpen W hWo
  have hcV : c.source ⊆ V := fun y hy => (hWsub hy.2).1
  have hcf : (c : E → F) = f := rfl
  refine ⟨c, ⟨hx₀,hxW⟩, hcV, hcf, ?_, ?_⟩
  · exact hf.mono hcV
  · intro y hy
    have hsy : c.symm y ∈ c.source := c.map_target hy
    obtain ⟨Ly,hLy⟩ := (hWsub hsy.2).2
    have hfsy := hf.contDiffAt (hV.mem_nhds (hcV hsy))
    have hdsy : HasFDerivAt c (Ly : E →L[ℝ] F) (c.symm y) := by
      rw [hcf, hLy]
      exact (hfsy.differentiableAt (by simp)).hasFDerivAt
    exact (c.contDiffAt_symm hy hdsy (by simpa only [hcf] using hfsy)).contDiffWithinAt

end Yau.Proofs.F05Aux
