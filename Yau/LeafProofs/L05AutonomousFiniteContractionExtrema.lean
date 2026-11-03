import Yau.LeafProofs.L05AutonomousFiniteContractionMean

open MeasureTheory Set
open scoped BigOperators

namespace Yau.LeafProofs.L05AutonomousAux

/-- The actual supremum of the range of a scalar field. -/
noncomputable def finiteFieldSup {X : Type*} (w : X → ℝ) (Q : Set X) : ℝ := sSup (w '' Q)

/-- The actual infimum of the range of a scalar field. -/
noncomputable def finiteFieldInf {X : Type*} (w : X → ℝ) (Q : Set X) : ℝ := sInf (w '' Q)

/-- All extrema used below are taken on nonempty, bounded ranges. -/
theorem finite_extrema_nested {X : Type*} (w : X → ℝ) {S Q : Set X}
    (hS : S.Nonempty) (hSQ : S ⊆ Q)
    (hU : BddAbove (w '' Q)) (hL : BddBelow (w '' Q)) :
    (w '' Q).Nonempty ∧ (w '' S).Nonempty ∧ BddAbove (w '' S) ∧ BddBelow (w '' S) ∧
    finiteFieldSup w S ≤ finiteFieldSup w Q ∧
    finiteFieldInf w Q ≤ finiteFieldInf w S ∧
    finiteFieldInf w S ≤ finiteFieldSup w S := by
  have hnS := hS.image w
  have hnQ := (hS.mono hSQ).image w
  have hi : w '' S ⊆ w '' Q := image_mono hSQ
  have huS := hU.mono hi
  have hlS := hL.mono hi
  refine ⟨hnQ, hnS, huS, hlS, csSup_le_csSup hU hnS hi,
    csInf_le_csInf hL hnS hi, ?_⟩
  rcases hnS with ⟨v, hv⟩
  exact (csInf_le hlS hv).trans (le_csSup huS hv)

/-- Boundedness on the support gives actual integrability, without an integral premise. -/
theorem finite_deficit_integrable {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (w : X → ℝ) (hw : Measurable w)
    {Q E : Set X} (hEQ : E ⊆ Q) (hμ : ∀ᵐ x ∂μ, x ∈ E)
    (hQ : Q.Nonempty) (hU : BddAbove (w '' Q)) (hL : BddBelow (w '' Q))
    {p : ℝ} (hp : 0 < p) :
    (∀ᵐ x ∂μ, max (finiteFieldSup w Q - w x) 0 = finiteFieldSup w Q - w x) ∧
    Integrable (fun x => (max (finiteFieldSup w Q - w x) 0) ^ p) μ := by
  have hM : ∀ x ∈ Q, w x ≤ finiteFieldSup w Q :=
    fun x hx => le_csSup hU (mem_image_of_mem w hx)
  rcases hL with ⟨b, hb⟩
  have hbM : b ≤ finiteFieldSup w Q := by
    rcases hQ with ⟨x, hx⟩
    exact (hb (mem_image_of_mem w hx)).trans (hM x hx)
  have heq : ∀ᵐ x ∂μ, max (finiteFieldSup w Q - w x) 0 = finiteFieldSup w Q - w x := by
    filter_upwards [hμ] with x hx
    exact max_eq_left (sub_nonneg.mpr (hM x (hEQ hx)))
  refine ⟨heq, (integrable_const ((finiteFieldSup w Q - b) ^ p)).mono' ?_ ?_⟩
  · exact (((measurable_const.sub hw).max measurable_const).pow_const p).aestronglyMeasurable
  · filter_upwards [hμ] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (le_max_right _ _) _)]
    apply Real.rpow_le_rpow (le_max_right _ _) _ hp.le
    apply max_le
    · linarith [hb (mem_image_of_mem w (hEQ hx))]
    · linarith

/-- A constant dominated on a probability space is bounded by the literal positive mean. -/
theorem finite_constant_le_mean {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] {p d K : ℝ} (hp : 0 < p)
    (hd : 0 ≤ d) (hK : 0 ≤ K) (g : X → ℝ)
    (hg : ∀ᵐ x ∂μ, 0 ≤ g x) (hI : Integrable (fun x => (g x) ^ p) μ)
    (hbound : ∀ᵐ x ∂μ, d ≤ K * g x) :
    d ≤ K * (∫ x, (g x) ^ p ∂μ) ^ (1 / p) := by
  have hpow : ∀ᵐ x ∂μ, d ^ p ≤ K ^ p * (g x) ^ p := by
    filter_upwards [hg, hbound] with x hx hb
    simpa [Real.mul_rpow hK hx] using Real.rpow_le_rpow hd hb hp.le
  have hle : d ^ p ≤ K ^ p * ∫ x, (g x) ^ p ∂μ := by
    simpa [integral_const_mul] using integral_mono_ae (integrable_const (d ^ p))
      (hI.const_mul (K ^ p)) hpow
  have hIp : 0 ≤ ∫ x, (g x) ^ p ∂μ :=
    integral_nonneg_of_ae (hg.mono fun x hx => Real.rpow_nonneg hx _)
  have h := Real.rpow_le_rpow (Real.rpow_nonneg hd p) hle (by positivity : 0 ≤ 1 / p)
  simpa only [Real.mul_rpow (Real.rpow_nonneg hK p) hIp, one_div,
    Real.rpow_rpow_inv hd hp.ne', Real.rpow_rpow_inv hK hp.ne'] using h

end Yau.LeafProofs.L05AutonomousAux
