import Yau.Proofs.V04SymplecticSubmeanTensor
import Yau.Proofs.V04SymplecticSubmeanWeightMean

open scoped Topology ContDiff Matrix
open MeasureTheory Set
noncomputable section
namespace Yau.Blueprint.V04Proof.SymplecticSubmeanAux
open Yau Yau.Blueprint Yau.Blueprint.V03Proof

/-- The full frozen symplectic submean for every given original factor.
The exact outer weight gives the required m^-4 and the bivector trace
identity gives the required one-half. Zero center and empty indices use
the same square-submean argument, without taking log of the tensor. -/
theorem symplecticSubmean_of_original_inputs {n q : ℕ} {X : KahlerManifold n}
    {d : VariationData X q} (hd : VariationSetup d) {k : ClockData X}
    (hk : ClockCutoffs d k) (a : ℕ) : SymplecticSubmean d k a := by
  intro j δ F E H Hinv hδ hF hE hfactor
  obtain ⟨hw, hwc, hwp⟩ := submeanWeight_pos_smooth hd hk (a := a) hF
  have hH (i l : CotangentIndex n) := (hfactor.1 i l).1
  have hZ := transformedTensor_contDiffOn hE hH
  have hmain := weighted_matrix_submean hw hwc hwp (transformedTensor E H) hZ
  rw [exp_average_log_submeanWeight hd hk hF] at hmain
  calc
    Real.exp (circleAverage (fun θ ↦ Real.log (clockWeight d k j a F θ))) *
        (outerCenter d j a F ^ 4)⁻¹ * bivectorCost ((H 0)ᴴ * H 0) (frameBivector (E 0)) =
      (1 / 2 : ℝ) * (Real.exp (circleAverage (fun θ ↦ Real.log (clockWeight d k j a F θ))) *
        (outerCenter d j a F ^ 4)⁻¹ * matrixFrobSq (transformedTensor E H 0)) := by
      rw [bivectorCost_gram_eq_half_frobSq]
      dsimp only [transformedTensor]
      ring
    _ ≤ (1 / 2 : ℝ) * circleAverage (fun θ ↦ submeanWeight d k j a F θ *
        matrixFrobSq (transformedTensor E H (circlePoint θ))) :=
      mul_le_mul_of_nonneg_left hmain (by norm_num)
    _ = circleAverage (fun θ ↦ discTime F (circlePoint θ) / F.s * clockWeight d k j a F θ *
        (wallPower d j a (F.f (circlePoint θ)) ^ 4)⁻¹ *
        bivectorCost ((H (circlePoint θ))ᴴ * H (circlePoint θ))
          (frameBivector (E (circlePoint θ)))) := by
      rw [← circleAverage_const_mul_value]
      apply congrArg circleAverage
      funext θ
      rw [bivectorCost_gram_eq_half_frobSq]
      dsimp only [submeanWeight, transformedTensor]
      ring

end Yau.Blueprint.V04Proof.SymplecticSubmeanAux
