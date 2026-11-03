import Yau.Proofs.P06HodgeDaviesTail

noncomputable section
open MeasureTheory Filter
open scoped Topology InnerProductSpace

namespace Yau.NodeProofs.P06Aux.Davies
open Yau Yau.LeafProofs Yau.LeafProofs.L03
variable {n k : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false

/-- The restriction norm is exactly the integral of the original
physical fibre norm over the set. -/
theorem indicator_realize_norm_sq (g : SmoothMetric M) (μ : Measure M.Carrier)
    (s : Set M.Carrier) (hs : MeasurableSet s)
    (A : RealForm M k) (hA : L2RealForm g.form μ A) :
    ‖indicator g μ s hs (realizeActualForm g μ A hA)‖ ^ 2 =
      ∫ x in s, formNormSq g.form A x ∂μ := by
  rw [indicator, realizeActualForm, multiplyL2FormHilbert_realize, realizeL2Form_norm_sq]
  calc
    _ = ∫ x, s.indicator (formNormSq g.form A) x ∂μ := by
      apply integral_congr_ae (Eventually.of_forall ?_)
      intro x
      simp only [multiplyL2FormLinear_toSection, L2FormSpace.toSection_ofSection,
        multiplyRealForm_normSq]
      by_cases hx : x ∈ s <;> simp [hx]
    _ = _ := integral_indicator hs

/-- Almost everywhere support of an actual form gives exactly the
Hilbert support condition used by the all-degree annular estimate. -/
theorem indicator_realize_eq_self (g : SmoothMetric M) (μ : Measure M.Carrier)
    (s : Set M.Carrier) (hs : MeasurableSet s)
    (A : RealForm M k) (hA : L2RealForm g.form μ A)
    (hf : ∀ᵐ x ∂μ, x ∉ s → A x = 0) :
    indicator g μ s hs (realizeActualForm g μ A hA) = realizeActualForm g μ A hA := by
  rw [indicator, realizeActualForm, multiplyL2FormHilbert_realize]
  apply (realizeL2Form_eq_iff_ae g μ _ _).mpr
  filter_upwards [hf] with x hx
  simp only [multiplyL2FormLinear_toSection, L2FormSpace.toSection_ofSection,
    multiplyRealForm]
  by_cases hxs : x ∈ s
  · simp [hxs]
  · simp [hxs, hx hxs]

/-- A concrete uniform Gaussian tail statement for raw original L²
forms, supported in the radius-R ball and measured outside radius 2R. -/
theorem exists_uniform_double_radius_heat_tail (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (M : ComplexManifold n) (g : SmoothMetric M)
      (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ) (k : ℕ)
      (o : M.Carrier) (R t : ℝ), 0 < R → 0 < t →
      ∀ (A : RealForm M k) (hA : L2RealForm g.form μ A),
      (∀ᵐ x ∂μ, x ∉ distBall g.form o R → A x = 0) →
      ‖indicator g μ (distBall g.form o (2 * R))ᶜ
        (L12Aux.measurableSet_distBall g o (2 * R)).compl
        (hodgeHeatHilbert g μ hμ k t (realizeActualForm g μ A hA))‖ ≤
      Real.exp (-(R ^ 2) / (C * t)) * ‖realizeActualForm g μ A hA‖ := by
  obtain ⟨B, hB, htail⟩ := exists_uniform_annular_heat_L2_tail n
  refine ⟨2 * B ^ 2, by nlinarith, ?_⟩
  intro M g μ hμ k o R t hR ht A hA hf
  have hi := indicator_realize_eq_self g μ (distBall g.form o R)
    (L12Aux.measurableSet_distBall g o R) A hA hf
  have he := htail M g μ hμ k o R (2 * R) hR (by linarith) t ht
    (realizeActualForm g μ A hA) hi
  have hsub : 2 * R - R = R := by ring
  simpa only [hsub, mul_assoc] using he

end Yau.NodeProofs.P06Aux.Davies
