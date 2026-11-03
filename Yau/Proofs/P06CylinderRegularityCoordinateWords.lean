import Yau.Proofs.P06CylinderRegularityMultilinear
import Yau.Proofs.P06HodgeRegularityWordCalculus
import Yau.LeafProofs.L16ParabolicCoordinates

/-! Literal coordinate words and Haar-volume transport for the genuine
space-time coordinate equivalence. -/
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
open MeasureTheory Filter
open scoped Topology ContDiff

namespace Yau.NodeProofs.P06Aux.CylinderReg
open Yau.Parabolic Yau.LeafProofs.L16Aux

theorem parabolicCoordinateEquiv_symm_single {n : ℕ}
    (i : Fin (Fintype.card (ParabolicJointIdx n))) :
    (parabolicCoordinateEquiv n).symm (Pi.single i 1) =
      parabolicJointVec ((parabolicJointIndexEquiv n).symm i) := by
  apply (parabolicCoordinateEquiv n).injective
  rw [(parabolicCoordinateEquiv n).apply_symm_apply, parabolicCoordinateEquiv_jointVec,
    (parabolicJointIndexEquiv n).apply_symm_apply]

theorem coordinateWordDerivative_parabolic {n : ℕ} {f : Point n → ℝ}
    (hf : ContDiff ℝ ∞ f) (w : List (Fin (Fintype.card (ParabolicJointIdx n)))) :
    coordinateWordDerivative (f ∘ (parabolicCoordinateEquiv n).symm) w =
      (regularityCoefficientWord parabolicJointVec
        (w.map (parabolicJointIndexEquiv n).symm) f) ∘ (parabolicCoordinateEquiv n).symm := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    simp only [coordinateWordDerivative, List.map_cons, regularityCoefficientWord]
    rw [ih]
    funext x
    have hWord := regularityCoefficientWord_contDiff parabolicJointVec hf
      (w.map (parabolicJointIndexEquiv n).symm)
    rw [fderiv_comp x (hWord.differentiable (by simp) _)
      (parabolicCoordinateEquiv n).symm.differentiableAt]
    rw [(parabolicCoordinateEquiv n).symm.fderiv]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      parabolicCoordinateEquiv_symm_single, Function.comp_apply, regularityDirection]

theorem coordinate_word_integral_transport {n : ℕ} {f : Point n → ℝ}
    (hf : ContDiff ℝ ∞ f) (w : List (Fin (Fintype.card (ParabolicJointIdx n)))) :
    ∃ c : ℝ, 0 < c ∧
      (∫ p, (regularityCoefficientWord parabolicJointVec
        (w.map (parabolicJointIndexEquiv n).symm) f p)^2) =
        c * ∫ x, (coordinateWordDerivative (f ∘ (parabolicCoordinateEquiv n).symm) w x)^2 := by
  obtain ⟨c,hc,hmap⟩ := parabolicCoordinateEquiv_map_volume n
  refine ⟨c,hc,?_⟩
  rw [parabolicCoordinateEquiv_integral hc hmap]
  simp only [coordinateWordDerivative_parabolic hf, Function.comp_apply]

end Yau.NodeProofs.P06Aux.CylinderReg
