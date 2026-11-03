import Yau.Proofs.D06RelativeEnergy
import Yau.Proofs.D06CircleDifferences

/-! The original symmetric boundary energy estimate with the sharp m⁻²
constant, on the same original factors before boundary regularity. -/

open scoped ComplexOrder Matrix
open MeasureTheory

noncomputable section
namespace Yau.NodeProofs.D06Aux

open Yau.Blueprint
variable {r : ℕ}

theorem matrix_entries_memLp_sub_one (A : HardyCircle → Matrix (Fin r) (Fin r) ℂ)
    (hA : ∀ i j, MemLp (fun t => A t i j) ⊤ hardyCircleMeasure) (i j : Fin r) :
    MemLp (fun t => (A t - 1) i j) ⊤ hardyCircleMeasure :=
  (hA i j).sub (memLp_const _)

variable (L : HardyCircle → Matrix (Fin r) (Fin r) ℂ)
variable (hLp : ∀ i j, MemLp (fun t => L t i j) ⊤ hardyCircleMeasure)
variable (hHerm : ∀ t, (L t).IsHermitian)
variable (m : ℝ) (hm : 0 < m)
variable (hLower : ∀ t, (L t - (m : ℂ) • 1).PosSemidef)
variable (M : ℝ) (hM : 0 ≤ M)
variable (hUpper : ∀ t, ((M : ℂ) • 1 - L t).PosSemidef)

theorem hardyTranslationEnergy_symmetric (θ : HardyCircle) :
    hardyTranslationEnergy L hLp hHerm m hm hLower M hM hUpper θ +
      hardyTranslationEnergy L hLp hHerm m hm hLower M hM hUpper (-θ) ≤
        (m ^ 2)⁻¹ * circleDifference L θ := by
  let X := hardySourceInverse L hLp hHerm m hm hLower M hM hUpper
  let f : HardyCircle → ℝ := fun t => (Matrix.trace (L (t + θ) * X t - 1)).re
  let g : HardyCircle → ℝ := fun t => (Matrix.trace (L t * X (t + θ) - 1)).re
  have hX : ∀ i j, MemLp (fun t => X t i j) ⊤ hardyCircleMeasure :=
    hardySourceInverse_memLp L hLp hHerm m hm hLower M hM hUpper
  have hLθ : ∀ i j, MemLp (fun t => L (t + θ) i j) ⊤ hardyCircleMeasure := fun i j =>
    (hLp i j).comp_measurePreserving (measurePreserving_add_right hardyCircleMeasure θ)
  have hXθ : ∀ i j, MemLp (fun t => X (t + θ) i j) ⊤ hardyCircleMeasure := fun i j =>
    (hX i j).comp_measurePreserving (measurePreserving_add_right hardyCircleMeasure θ)
  have hf : Integrable f hardyCircleMeasure := matrix_realTrace_integrable _
    (matrix_entries_memLp_sub_one _ (matrix_entries_memLp_mul _ _ hLθ hX))
  have hg : Integrable g hardyCircleMeasure := matrix_realTrace_integrable _
    (matrix_entries_memLp_sub_one _ (matrix_entries_memLp_mul _ _ hLp hXθ))
  have hD : Integrable (fun t => frobSq (L (t + θ) - L t)) hardyCircleMeasure :=
    matrix_frobSq_integrable _ (fun i j => ((hLθ i j).sub (hLp i j)).mono_exponent le_top)
  have hp : hardyTranslationEnergy L hLp hHerm m hm hLower M hM hUpper θ = ∫ t, f t ∂hardyCircleMeasure :=
    hardyTranslationEnergy_trace L hLp hHerm m hm hLower M hM hUpper θ
  have hn : hardyTranslationEnergy L hLp hHerm m hm hLower M hM hUpper (-θ) = ∫ t, g t ∂hardyCircleMeasure := by
    rw [hardyTranslationEnergy_trace]
    calc
      _ = ∫ t, (Matrix.trace (L ((t + θ) + -θ) * X (t + θ) - 1)).re ∂hardyCircleMeasure :=
        (integral_add_right_eq_self (μ := hardyCircleMeasure)
          (fun t => (Matrix.trace (L (t + -θ) * X t - 1)).re) θ).symm
      _ = _ := by
        apply integral_congr_ae
        filter_upwards with t
        simp only [add_neg_cancel_right, g]
  have hInv := hardySourceInverse_inverse L hLp hHerm m hm hLower M hM hUpper
  have hBound := hardySourceInverse_bound L hLp hHerm m hm hLower M hM hUpper
  have hInvθ := (measurePreserving_add_right hardyCircleMeasure θ).quasiMeasurePreserving.ae hInv
  have hBoundθ := (measurePreserving_add_right hardyCircleMeasure θ).quasiMeasurePreserving.ae hBound
  have hpoint : (fun t => f t + g t) ≤ᵐ[hardyCircleMeasure]
      fun t => (m ^ 2)⁻¹ * frobSq (L (t + θ) - L t) := by
    filter_upwards [hInv, hInvθ, hBound, hBoundθ] with t hi hiθ hb hbθ
    exact re_trace_symmetric_relative_difference_le (L t) (L (t + θ)) (X t) (X (t + θ))
      m hm hi.1 hi.2 hiθ.1 hb hbθ
  calc
    _ = ∫ t, f t + g t ∂hardyCircleMeasure := by rw [hp, hn]; exact (integral_add hf hg).symm
    _ ≤ ∫ t, (m ^ 2)⁻¹ * frobSq (L (t + θ) - L t) ∂hardyCircleMeasure :=
      integral_mono_ae (hf.add hg) (hD.const_mul _) hpoint
    _ = _ := integral_const_mul _ _

end Yau.NodeProofs.D06Aux
