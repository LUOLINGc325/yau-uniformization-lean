import Yau.Proofs.D06WeightedCore

/-! Exact norm equivalence and completeness of the weighted Hardy space. -/

open scoped ComplexOrder
open MeasureTheory

noncomputable section
namespace Yau.NodeProofs.D06Aux

variable {r : ℕ}
variable (L : HardyCircle → Matrix (Fin r) (Fin r) ℂ)
variable (hLp : ∀ i j, MemLp (fun t => L t i j) ⊤ hardyCircleMeasure)
variable (hHerm : ∀ t, (L t).IsHermitian)
variable (m : ℝ) (hm : 0 < m)
variable (hLower : ∀ t, (L t - (m : ℂ) • 1).PosSemidef)

theorem weighted_unwrap_norm_le (a : WeightedHardySeq r) :
    letI : NormedAddCommGroup (WeightedHardySeq r) :=
      weightedHardyNormed L hLp hHerm m hm hLower
    ‖weightedUnwrap a‖ ≤ (Real.sqrt m)⁻¹ * ‖a‖ := by
  letI : NormedAddCommGroup (WeightedHardySeq r) :=
    weightedHardyNormed L hLp hHerm m hm hLower
  have h := hardyWeightedInner_lower L hLp m hLower (weightedUnwrap a)
  have hw := weightedHardy_norm_sq L hLp hHerm m hm hLower a
  rw [← hw] at h
  have hprod : Real.sqrt m * ‖weightedUnwrap a‖ ≤ ‖a‖ := by
    apply (sq_le_sq₀ (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)) (norm_nonneg _)).mp
    rwa [mul_pow, Real.sq_sqrt hm.le]
  have hs := mul_le_mul_of_nonneg_left hprod (inv_nonneg.mpr (Real.sqrt_nonneg m))
  simpa only [← mul_assoc, inv_mul_cancel₀ (Real.sqrt_pos.mpr hm).ne', one_mul] using hs

theorem weighted_wrap_norm_le (M : ℝ) (hM : 0 ≤ M)
    (hUpper : ∀ t, ((M : ℂ) • 1 - L t).PosSemidef) (a : HardySeq r) :
    letI : NormedAddCommGroup (WeightedHardySeq r) :=
      weightedHardyNormed L hLp hHerm m hm hLower
    ‖weightedUnwrap.symm a‖ ≤ Real.sqrt M * ‖a‖ := by
  letI : NormedAddCommGroup (WeightedHardySeq r) :=
    weightedHardyNormed L hLp hHerm m hm hLower
  have h := hardyWeightedInner_upper L hLp M hUpper a
  have hw := weightedHardy_norm_sq L hLp hHerm m hm hLower (weightedUnwrap.symm a)
  simp only [LinearEquiv.apply_symm_apply] at hw
  rw [← hw] at h
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rwa [mul_pow, Real.sq_sqrt hM]

def weightedUnwrapCLM :
    letI : NormedAddCommGroup (WeightedHardySeq r) :=
      weightedHardyNormed L hLp hHerm m hm hLower
    WeightedHardySeq r →L[ℂ] HardySeq r :=
  letI : NormedAddCommGroup (WeightedHardySeq r) :=
    weightedHardyNormed L hLp hHerm m hm hLower
  letI : InnerProductSpace ℂ (WeightedHardySeq r) :=
    weightedHardyInnerProduct L hLp hHerm m hm hLower
  (weightedUnwrapLM (r := r)).mkContinuous ((Real.sqrt m)⁻¹) (fun a => by
    change ‖weightedUnwrap a‖ ≤ (Real.sqrt m)⁻¹ * ‖a‖
    exact weighted_unwrap_norm_le L hLp hHerm m hm hLower a)

def weightedWrapCLM (M : ℝ) (hM : 0 ≤ M)
    (hUpper : ∀ t, ((M : ℂ) • 1 - L t).PosSemidef) :
    letI : NormedAddCommGroup (WeightedHardySeq r) :=
      weightedHardyNormed L hLp hHerm m hm hLower
    HardySeq r →L[ℂ] WeightedHardySeq r :=
  letI : NormedAddCommGroup (WeightedHardySeq r) :=
    weightedHardyNormed L hLp hHerm m hm hLower
  letI : InnerProductSpace ℂ (WeightedHardySeq r) :=
    weightedHardyInnerProduct L hLp hHerm m hm hLower
  (weightedWrapLM (r := r)).mkContinuous (Real.sqrt M) (fun a => by
    change ‖weightedUnwrap.symm a‖ ≤ Real.sqrt M * ‖a‖
    exact weighted_wrap_norm_le L hLp hHerm m hm hLower M hM hUpper a)

theorem weightedWrap_unwrap (M : ℝ) (hM : 0 ≤ M)
    (hUpper : ∀ t, ((M : ℂ) • 1 - L t).PosSemidef) (a : WeightedHardySeq r) :
    letI : NormedAddCommGroup (WeightedHardySeq r) :=
      weightedHardyNormed L hLp hHerm m hm hLower
    weightedWrapCLM L hLp hHerm m hm hLower M hM hUpper
      (weightedUnwrapCLM L hLp hHerm m hm hLower a) = a := by
  letI : NormedAddCommGroup (WeightedHardySeq r) :=
    weightedHardyNormed L hLp hHerm m hm hLower
  change weightedUnwrap.symm (weightedUnwrap a) = a
  exact weightedUnwrap.symm_apply_apply a

@[instance_reducible]
def weightedHardyComplete (M : ℝ) (hM : 0 ≤ M)
    (hUpper : ∀ t, ((M : ℂ) • 1 - L t).PosSemidef) :
    letI : NormedAddCommGroup (WeightedHardySeq r) :=
      weightedHardyNormed L hLp hHerm m hm hLower
    CompleteSpace (WeightedHardySeq r) := by
  letI : NormedAddCommGroup (WeightedHardySeq r) :=
    weightedHardyNormed L hLp hHerm m hm hLower
  apply Metric.complete_of_cauchySeq_tendsto
  intro u hu
  let J := weightedUnwrapCLM L hLp hHerm m hm hLower
  let K := weightedWrapCLM L hLp hHerm m hm hLower M hM hUpper
  have hc : CauchySeq (fun n => J (u n)) := J.uniformContinuous.comp_cauchySeq hu
  obtain ⟨a, ha⟩ := cauchySeq_tendsto_of_complete hc
  refine ⟨K a, ?_⟩
  have hleft (v : WeightedHardySeq r) : K (J v) = v :=
    weightedWrap_unwrap L hLp hHerm m hm hLower M hM hUpper v
  simpa only [Function.comp_def, hleft] using
    (K.continuous.continuousAt.tendsto.comp ha)

end Yau.NodeProofs.D06Aux
