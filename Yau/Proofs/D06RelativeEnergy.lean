import Yau.Proofs.D06BoundarySourceInverse

/-! The original relative-factor energy identity at the measurable Hardy
boundary, prior to any Sobolev or closed-disc smoothness assumption. -/

open scoped ComplexOrder Matrix
open MeasureTheory

noncomputable section
namespace Yau.NodeProofs.D06Aux

open Yau.Blueprint
variable {r : ℕ}
variable (L : HardyCircle → Matrix (Fin r) (Fin r) ℂ)
variable (hLp : ∀ i j, MemLp (fun t => L t i j) ⊤ hardyCircleMeasure)
variable (hHerm : ∀ t, (L t).IsHermitian)
variable (m : ℝ) (hm : 0 < m)
variable (hLower : ∀ t, (L t - (m : ℂ) • 1).PosSemidef)
variable (M : ℝ) (hM : 0 ≤ M)
variable (hUpper : ∀ t, ((M : ℂ) • 1 - L t).PosSemidef)

theorem hardyRelativeTrace_memLp (θ : HardyCircle) (i j : Fin r) :
    MemLp (fun t => hardyRelativeTrace L hLp hHerm m hm hLower M hM hUpper θ t i j)
      ⊤ hardyCircleMeasure := by
  apply matrix_entries_memLp_mul
  · intro i j
    exact (hardyQTrace_memLp L hLp hHerm m hm hLower M hM hUpper i j).comp_measurePreserving
      (measurePreserving_add_right hardyCircleMeasure θ)
  · exact hardyPTrace_memLp L hLp hHerm m hm hLower M hM hUpper

def hardyTranslationEnergy (θ : HardyCircle) : ℝ :=
  ∫ t, frobSq (hardyRelativeTrace L hLp hHerm m hm hLower M hM hUpper θ t - 1)
    ∂hardyCircleMeasure

theorem hardyTranslationEnergy_nonneg (θ : HardyCircle) :
    0 ≤ hardyTranslationEnergy L hLp hHerm m hm hLower M hM hUpper θ :=
  integral_nonneg (fun _ => frobSq_nonneg _)

theorem hardyTranslationEnergy_mean (θ : HardyCircle) :
    hardyTranslationEnergy L hLp hHerm m hm hLower M hM hUpper θ =
      (∫ t, frobSq (hardyRelativeTrace L hLp hHerm m hm hLower M hM hUpper θ t)
        ∂hardyCircleMeasure) - r :=
  matrix_frobSq_sub_one_mean _
    (hardyRelativeTrace_memLp L hLp hHerm m hm hLower M hM hUpper θ)
    (hardyRelativeTrace_realTrace_mean L hLp hHerm m hm hLower M hM hUpper θ)

theorem hardyTranslationEnergy_trace (θ : HardyCircle) :
    hardyTranslationEnergy L hLp hHerm m hm hLower M hM hUpper θ =
      ∫ t, (Matrix.trace (L (t + θ) *
        hardySourceInverse L hLp hHerm m hm hLower M hM hUpper t - 1)).re ∂hardyCircleMeasure := by
  let X := hardySourceInverse L hLp hHerm m hm hLower M hM hUpper
  have hprod : ∀ i j, MemLp (fun t => (L (t + θ) * X t) i j) ⊤ hardyCircleMeasure :=
    matrix_entries_memLp_mul _ _ (fun i j => (hLp i j).comp_measurePreserving
      (measurePreserving_add_right hardyCircleMeasure θ))
      (hardySourceInverse_memLp L hLp hHerm m hm hLower M hM hUpper)
  have htr := matrix_realTrace_integrable (fun t => L (t + θ) * X t) hprod
  have hfactor := (measurePreserving_add_right hardyCircleMeasure θ).quasiMeasurePreserving.ae
    (hardyQTrace_factor L hLp hHerm m hm hLower M hM hUpper)
  have heq : (fun t => frobSq (hardyRelativeTrace L hLp hHerm m hm hLower M hM hUpper θ t)) =ᵐ[hardyCircleMeasure]
      fun t => (Matrix.trace (L (t + θ) * X t)).re := by
    filter_upwards [hfactor] with t ht
    rw [hardyRelativeTrace, frobSq_mul_eq_re_trace_gram, ← ht]
    rfl
  rw [hardyTranslationEnergy_mean, integral_congr_ae heq]
  have hfun : (fun t => (Matrix.trace (L (t + θ) * X t - 1)).re) =
      (fun t => (Matrix.trace (L (t + θ) * X t)).re) - (fun _ : HardyCircle => (r : ℝ)) := by
    funext t
    simp only [Matrix.trace_sub, Matrix.trace_one, Fintype.card_fin, Complex.sub_re,
      Complex.natCast_re, Pi.sub_apply]
  change _ = ∫ t, (Matrix.trace (L (t + θ) * X t - 1)).re ∂hardyCircleMeasure
  rw [hfun]
  have hs : (∫ t, ((fun t => (Matrix.trace (L (t + θ) * X t)).re) -
      (fun _ : HardyCircle => (r : ℝ))) t ∂hardyCircleMeasure) =
      (∫ t, (Matrix.trace (L (t + θ) * X t)).re ∂hardyCircleMeasure) -
        (∫ _ : HardyCircle, (r : ℝ) ∂hardyCircleMeasure) := integral_sub htr (integrable_const _)
  have hc : (∫ _ : HardyCircle, (r : ℝ) ∂hardyCircleMeasure) = r := by simp
  rw [hc] at hs
  exact hs.symm

end Yau.NodeProofs.D06Aux
