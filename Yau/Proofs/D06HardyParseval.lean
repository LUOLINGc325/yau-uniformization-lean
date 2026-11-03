import Yau.Proofs.D06HardyFourier

/-! Parseval and the exact Euclidean vector norm for the actual Hardy traces. -/

open scoped lp
open MeasureTheory

noncomputable section
namespace Yau.NodeProofs.D06Aux

variable {r : ℕ}

theorem hardyTrace_integral_norm_sq (a : HardySeq r) (j : Fin r) :
    (∫ t, ‖hardyTraceLp a j t‖ ^ 2 ∂hardyCircleMeasure) =
      ∑' n : ℕ, ‖a (n, j)‖ ^ 2 := by
  have hF := hasSum_sq_fourierCoeff (T := 2 * Real.pi) (hardyTraceLp a j)
  simp_rw [hardyTrace_fourierCoeff] at hF
  change HasSum (fun n : ℤ => ‖hardyPad a j n‖ ^ 2)
    (∫ t, ‖hardyTraceLp a j t‖ ^ 2 ∂hardyCircleMeasure) at hF
  have hP : HasSum (fun n : ℤ => ‖hardyPad a j n‖ ^ 2) (‖hardyPad a j‖ ^ 2) := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      lp.hasSum_norm (p := 2) (E := fun _ : ℤ => ℂ)
        (by norm_num : 0 < (2 : ENNReal).toReal) (hardyPad a j)
  exact (hF.unique hP).trans (hardyPad_norm_sq a j)

theorem hardy_column_norm_sum (a : HardySeq r) :
    (∑ j : Fin r, ∑' n : ℕ, ‖a (n, j)‖ ^ 2) = ‖a‖ ^ 2 := by
  have hA : HasSum (fun k : ℕ × Fin r => ‖a k‖ ^ 2) (‖a‖ ^ 2) := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      lp.hasSum_norm (p := 2) (E := fun _ : ℕ × Fin r => ℂ)
        (by norm_num : 0 < (2 : ENNReal).toReal) a
  have hrows : HasSum (fun n : ℕ => ∑ j : Fin r, ‖a (n, j)‖ ^ 2) (‖a‖ ^ 2) :=
    hA.prod_fiberwise fun n => hasSum_fintype (fun j : Fin r => ‖a (n, j)‖ ^ 2)
  have hcols : HasSum (fun n : ℕ => ∑ j : Fin r, ‖a (n, j)‖ ^ 2)
      (∑ j : Fin r, ∑' n : ℕ, ‖a (n, j)‖ ^ 2) :=
    hasSum_sum fun j _ => (hardy_column_summable_norm_sq a j).hasSum
  exact hcols.unique hrows

theorem hardyTrace_norm_sq (a : HardySeq r) :
    (∑ j : Fin r, ∫ t, ‖hardyTraceLp a j t‖ ^ 2 ∂hardyCircleMeasure) = ‖a‖ ^ 2 := by
  simp only [hardyTrace_integral_norm_sq]
  exact hardy_column_norm_sum a

end Yau.NodeProofs.D06Aux
