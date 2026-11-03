import Yau.Proofs.D06Energy
import Yau.Proofs.D06HardyFourier

/-! The trace energy identity for bounded measurable boundary matrices. It does
not require boundary continuity and is available for the first W¹ estimate. -/

open scoped Matrix
open MeasureTheory

noncomputable section
namespace Yau.NodeProofs.D06Aux

open Yau.Blueprint
variable {r : ℕ}

theorem matrix_entries_memLp_mul
    (A B : HardyCircle → Matrix (Fin r) (Fin r) ℂ)
    (hA : ∀ i j, MemLp (fun t => A t i j) ⊤ hardyCircleMeasure)
    (hB : ∀ i j, MemLp (fun t => B t i j) ⊤ hardyCircleMeasure) (i j : Fin r) :
    MemLp (fun t => (A t * B t) i j) ⊤ hardyCircleMeasure := by
  change MemLp (fun t => ∑ k : Fin r, A t i k * B t k j) ⊤ hardyCircleMeasure
  exact memLp_finsetSum _ (fun k _ => (hA i k).fun_mul (hB k j))

theorem matrix_frobSq_integrable (A : HardyCircle → Matrix (Fin r) (Fin r) ℂ)
    (hA : ∀ i j, MemLp (fun t => A t i j) 2 hardyCircleMeasure) :
    Integrable (fun t => frobSq (A t)) hardyCircleMeasure :=
  integrable_finsetSum _ (fun i _ => integrable_finsetSum _
    (fun j _ => (hA i j).integrable_norm_pow (by decide : 2 ≠ 0)))

theorem matrix_realTrace_integrable (A : HardyCircle → Matrix (Fin r) (Fin r) ℂ)
    (hA : ∀ i j, MemLp (fun t => A t i j) ⊤ hardyCircleMeasure) :
    Integrable (fun t => (Matrix.trace (A t)).re) hardyCircleMeasure := by
  simp only [Matrix.trace, Matrix.diag_apply, Complex.re_sum]
  apply integrable_finsetSum _
  intro i _
  have h : Integrable (fun t => A t i i) hardyCircleMeasure :=
    memLp_one_iff_integrable.mp ((hA i i).mono_exponent le_top)
  simpa only [RCLike.re_to_complex] using h.re

theorem matrix_frobSq_sub_one_mean
    (A : HardyCircle → Matrix (Fin r) (Fin r) ℂ)
    (hA : ∀ i j, MemLp (fun t => A t i j) ⊤ hardyCircleMeasure)
    (hmean : (∫ t, (Matrix.trace (A t)).re ∂hardyCircleMeasure) = r) :
    (∫ t, frobSq (A t - 1) ∂hardyCircleMeasure) =
      (∫ t, frobSq (A t) ∂hardyCircleMeasure) - r := by
  have hF := matrix_frobSq_integrable A (fun i j => (hA i j).mono_exponent le_top)
  have hTr := matrix_realTrace_integrable A hA
  have h2Tr : Integrable (fun t => 2 * (Matrix.trace (A t)).re) hardyCircleMeasure :=
    hTr.const_mul 2
  have hc : Integrable (fun _ : HardyCircle => (r : ℝ)) hardyCircleMeasure := integrable_const _
  calc
    _ = ∫ t, frobSq (A t) - 2 * (Matrix.trace (A t)).re + r ∂hardyCircleMeasure := by
      apply integral_congr_ae
      filter_upwards with t
      exact frobSq_sub_one (A t)
    _ = (∫ t, frobSq (A t) ∂hardyCircleMeasure) -
        2 * (∫ t, (Matrix.trace (A t)).re ∂hardyCircleMeasure) + r := by
      have hadd : (∫ t, frobSq (A t) - 2 * (Matrix.trace (A t)).re + (r : ℝ) ∂hardyCircleMeasure) =
          (∫ t, frobSq (A t) - 2 * (Matrix.trace (A t)).re ∂hardyCircleMeasure) +
            (∫ _ : HardyCircle, (r : ℝ) ∂hardyCircleMeasure) := integral_add (hF.sub h2Tr) hc
      have hsub : (∫ t, frobSq (A t) - 2 * (Matrix.trace (A t)).re ∂hardyCircleMeasure) =
          (∫ t, frobSq (A t) ∂hardyCircleMeasure) -
            (∫ t, 2 * (Matrix.trace (A t)).re ∂hardyCircleMeasure) := integral_sub hF h2Tr
      have hmul : (∫ t, 2 * (Matrix.trace (A t)).re ∂hardyCircleMeasure) =
          2 * (∫ t, (Matrix.trace (A t)).re ∂hardyCircleMeasure) := integral_const_mul _ _
      have hconst : (∫ _ : HardyCircle, (r : ℝ) ∂hardyCircleMeasure) = r := by simp
      linarith
    _ = _ := by rw [hmean]; ring

end Yau.NodeProofs.D06Aux
