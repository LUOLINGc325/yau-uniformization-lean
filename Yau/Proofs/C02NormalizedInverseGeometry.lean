import Yau.Proofs.C02NormalizedInverseDifferential
import Yau.Proofs.C02NormalCompositionImmersion
import Yau.Proofs.C02InverseDifferentialBounds

/-! The same normalized inverse supplies nonsingularity, quantitative
length comparison, and exact complex-structure intertwining. -/

noncomputable section
namespace Yau.Blueprint.C02Proof
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

theorem normalizedInverseSource_differential_geometry
    (e : OpenPartialHomeomorph E E) (he0 : (0 : E) ∈ e.source)
    (hf : Differentiable ℝ (e : E → E))
    (hClose : ∀ y ∈ e.source,
      ‖fderiv ℝ (e : E → E) y - ContinuousLinearMap.id ℝ E‖ ≤ 1 / 4)
    (r : ℝ) (hr : r ≠ 0) (z : E)
    (hy : e 0 + (Real.sqrt (2 : ℝ) / r) • fderiv ℝ (e : E → E) 0 z ∈ e.target) :
    DifferentiableAt ℝ (normalizedInverseSource e r) z ∧
      (fderiv ℝ (normalizedInverseSource e r) z).IsInvertible ∧
      ∀ v, (1 / 3 : ℝ) * ‖v‖ ≤ ‖fderiv ℝ (normalizedInverseSource e r) z v‖ ∧
        ‖fderiv ℝ (normalizedInverseSource e r) z v‖ ≤ 6 * ‖v‖ := by
  let y := e.symm (e 0 + (Real.sqrt (2 : ℝ) / r) • fderiv ℝ (e : E → E) 0 z)
  have hyS : y ∈ e.source := e.map_target hy
  have hD := isInvertible_of_close_identity _ (hClose y hyS)
  have hD0 := isInvertible_of_close_identity _ (hClose 0 he0)
  have hG := normalizedInverseSource_hasFDerivAt e r hr z hy (hf y) hD
  refine ⟨hG.differentiableAt, ?_, ?_⟩
  · rw [hG.fderiv]
    exact normalized_inverse_operator_isInvertible _ _ hD hD0
  · intro v
    rw [hG.fderiv]
    exact normalized_inverse_differential_bounds _ _ (hClose y hyS) (hClose 0 he0) v

theorem normalizedInverseSource_intertwines
    (e : OpenPartialHomeomorph E E) (he0 : (0 : E) ∈ e.source)
    (hf : Differentiable ℝ (e : E → E))
    (hClose : ∀ y ∈ e.source,
      ‖fderiv ℝ (e : E → E) y - ContinuousLinearMap.id ℝ E‖ ≤ 1 / 4)
    (r : ℝ) (hr : r ≠ 0) (J : E → E →L[ℝ] E)
    (hJ0 : ∀ v, J 0 v = Complex.I • v)
    (hForward : ∀ y ∈ e.source, ∀ v,
      fderiv ℝ (e : E → E) y (J (r • y) v) = Complex.I • fderiv ℝ (e : E → E) y v)
    (z : E)
    (hy : e 0 + (Real.sqrt (2 : ℝ) / r) • fderiv ℝ (e : E → E) 0 z ∈ e.target)
    (v : E) :
    fderiv ℝ (normalizedInverseSource e r) z (Complex.I • v) =
      J (normalizedInverseSource e r z) (fderiv ℝ (normalizedInverseSource e r) z v) := by
  let y := e.symm (e 0 + (Real.sqrt (2 : ℝ) / r) • fderiv ℝ (e : E → E) 0 z)
  have hyS : y ∈ e.source := e.map_target hy
  have hD := isInvertible_of_close_identity _ (hClose y hyS)
  have hG := normalizedInverseSource_hasFDerivAt e r hr z hy (hf y) hD
  rw [hG.fderiv]
  apply normalized_inverse_differential_intertwines _ _ _ hD
  · exact hForward y hyS
  · intro u
    simpa only [smul_zero, hJ0] using hForward 0 he0 u

end Yau.Blueprint.C02Proof
