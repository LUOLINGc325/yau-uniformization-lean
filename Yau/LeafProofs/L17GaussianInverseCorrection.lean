import Yau.LeafProofs.L17Neumann
import Yau.LeafProofs.L17ParabolicUniqueness

/-! Applying the actual convergent Neumann series to a parametrix residual. -/

noncomputable section
namespace Yau.LeafProofs.L17Aux

open L17NeumannAux

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

def correctedParametrix (P : X →L[ℝ] Y) (Q : Y →L[ℝ] X) : Y →L[ℝ] X :=
  Q.comp (neumannSeries (P.comp Q-ContinuousLinearMap.id ℝ Y))

theorem correctedParametrix_right_inverse [CompleteSpace Y]
    (P : X →L[ℝ] Y) (Q : Y →L[ℝ] X) (hE : ‖P.comp Q-ContinuousLinearMap.id ℝ Y‖ < 1) :
    P.comp (correctedParametrix P Q) = ContinuousLinearMap.id ℝ Y := by
  have hId : ContinuousLinearMap.id ℝ Y+(P.comp Q-ContinuousLinearMap.id ℝ Y) = P.comp Q := by abel
  have h := neumann_left_inverse hE
  rw [hId] at h
  simpa only [correctedParametrix,ContinuousLinearMap.comp_assoc] using h

theorem correctedParametrix_left_inverse [CompleteSpace Y]
    (P : X →L[ℝ] Y) (Q : Y →L[ℝ] X) (hE : ‖P.comp Q-ContinuousLinearMap.id ℝ Y‖ < 1)
    (hP : Function.Injective P) :
    (correctedParametrix P Q).comp P = ContinuousLinearMap.id ℝ X := by
  apply ContinuousLinearMap.ext
  intro x
  apply hP
  have h := congrArg (fun L : Y →L[ℝ] Y => L (P x)) (correctedParametrix_right_inverse P Q hE)
  simpa only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply] using h

theorem correctedParametrix_norm_le (P : X →L[ℝ] Y) (Q : Y →L[ℝ] X)
    (hE : ‖P.comp Q-ContinuousLinearMap.id ℝ Y‖ ≤ 1/4) :
    ‖correctedParametrix P Q‖ ≤ (4/3)*‖Q‖ := by
  apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
  exact (mul_le_mul_of_nonneg_left (neumann_norm_le_four_thirds hE) (norm_nonneg Q)).trans_eq (mul_comm _ _)

def correctedParametrixEquiv [CompleteSpace Y] (P : X →L[ℝ] Y) (Q : Y →L[ℝ] X)
    (hE : ‖P.comp Q-ContinuousLinearMap.id ℝ Y‖ < 1) (hP : Function.Injective P) : X ≃L[ℝ] Y :=
  ContinuousLinearEquiv.equivOfInverse' P (correctedParametrix P Q)
    (correctedParametrix_right_inverse P Q hE) (correctedParametrix_left_inverse P Q hE hP)

theorem correctedParametrixEquiv_symm_apply [CompleteSpace Y]
    (P : X →L[ℝ] Y) (Q : Y →L[ℝ] X) (hE : ‖P.comp Q-ContinuousLinearMap.id ℝ Y‖ < 1)
    (hP : Function.Injective P) (f : Y) :
    (correctedParametrixEquiv P Q hE hP).symm f = correctedParametrix P Q f := rfl

end Yau.LeafProofs.L17Aux
