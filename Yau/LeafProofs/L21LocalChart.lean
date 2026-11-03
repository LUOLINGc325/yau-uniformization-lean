import Mathlib

/-! A genuine smooth local chart from an invertible real differential at
every point of a prescribed source neighborhood. -/

open scoped ContDiff Topology
noncomputable section
namespace Yau.LeafProofs.L21Aux

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem isInvertible_of_norm_sub_id_lt_one (L : E →L[ℝ] E)
    (h : ‖L - ContinuousLinearMap.id ℝ E‖ < 1) : L.IsInvertible := by
  have hh : ‖(1 : E →L[ℝ] E) - L‖ < 1 := by
    simpa only [norm_sub_rev, ContinuousLinearMap.one_def] using h
  have hu : IsUnit L := by simpa using isUnit_one_sub_of_norm_lt_one hh
  obtain ⟨u, hu⟩ := hu
  exact ⟨ContinuousLinearEquiv.ofUnit u, hu⟩

theorem local_chart_of_invertible_derivatives
    (F : E → E) (hF : ContDiff ℝ ∞ F)
    (U : Set E) (hU : IsOpen U) (p : E) (hp : p ∈ U)
    (hi : ∀ x ∈ U, (fderiv ℝ F x).IsInvertible) :
    ∃ e : OpenPartialHomeomorph E E,
      p ∈ e.source ∧ e.source ⊆ U ∧ (e : E → E) = F ∧
      ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target := by
  obtain ⟨D, hD⟩ := hi p hp
  have hFD : HasFDerivAt F (D : E →L[ℝ] E) p := by
    rw [hD]
    exact (hF.differentiable (by simp) p).hasFDerivAt
  let e₀ := hF.contDiffAt.toOpenPartialHomeomorph F hFD (by simp)
  let e := e₀.restrOpen U hU
  have hp₀ : p ∈ e₀.source :=
    hF.contDiffAt.mem_toOpenPartialHomeomorph_source hFD (by simp)
  have hsource : e.source ⊆ U := fun _ hx => hx.2
  have hcoe : (e : E → E) = F := rfl
  refine ⟨e, ⟨hp₀, hp⟩, hsource, hcoe, ?_, ?_⟩
  · rw [hcoe]
    exact hF.contDiffOn
  · intro y hy
    have hxU : e.symm y ∈ U := hsource (e.map_target hy)
    obtain ⟨D₁, hD₁⟩ := hi (e.symm y) hxU
    have hd : HasFDerivAt e (D₁ : E →L[ℝ] E) (e.symm y) := by
      rw [hcoe, hD₁]
      exact (hF.differentiable (by simp) _).hasFDerivAt
    apply (e.contDiffAt_symm hy hd ?_).contDiffWithinAt
    rw [hcoe]
    exact hF.contDiffAt

theorem local_chart_of_small_derivative
    (F : E → E) (hF : ContDiff ℝ ∞ F)
    (hclose : ∀ x ∈ Metric.ball (0 : E) (1 / 2 : ℝ),
      ‖fderiv ℝ F x - ContinuousLinearMap.id ℝ E‖ ≤ (1 / 4 : ℝ)) :
    ∃ e : OpenPartialHomeomorph E E,
      0 ∈ e.source ∧ e.source ⊆ Metric.ball 0 (1 / 2 : ℝ) ∧ (e : E → E) = F ∧
      ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target := by
  apply local_chart_of_invertible_derivatives F hF _ Metric.isOpen_ball 0 (by simp)
  intro x hx
  exact isInvertible_of_norm_sub_id_lt_one _ (lt_of_le_of_lt (hclose x hx) (by norm_num))

end Yau.LeafProofs.L21Aux
