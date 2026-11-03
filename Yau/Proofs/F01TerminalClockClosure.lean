import Yau.Proofs.F01ClosedTerminalJetContinuity
import Yau.Proofs.F01PartialChartJointSmooth

/-! Closing the actual terminal clock commutes with its positive
affine normalization. The open left profile remains the original one. -/
noncomputable section
open Set
open scoped ContDiff
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic
variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem close_terminal_face_affine_clock
    (f : Point n → F) (b : Space n → F) {κ : ℝ} (hκ : κ ≠ 0)
    (T : ℝ) (p : Point n) :
    closeTerminalTimeFace f b T (p.1, T + κ * p.2) =
      closeTerminalTimeFace (fun q => f (q.1, T + κ * q.2)) b 0 p := by
  have he : T + κ * p.2 = T ↔ p.2 = 0 := by
    constructor
    · intro hh
      have hz : κ * p.2 = 0 := by linarith
      exact (mul_eq_zero.mp hz).resolve_left hκ
    · intro hh
      simp only [hh, mul_zero, add_zero]
  simp only [closeTerminalTimeFace, he]

theorem close_terminal_face_smooth_on_open_left
    (f : Point n → F) (b : Space n → F) {κ : ℝ} (hκ : 0 < κ)
    (T : ℝ) {S : Set (Space n)} {l : ℝ}
    (hf : ContDiffOn ℝ ∞ (fun p : Point n => f (p.1, T + κ * p.2)) (S ×ˢ Ioo l 0)) :
    ContDiffOn ℝ ∞
      (fun p : Point n => closeTerminalTimeFace f b T (p.1, T + κ * p.2))
      (S ×ˢ Ioo l 0) := by
  apply hf.congr
  intro p hp
  have hh : T + κ * p.2 ≠ T := by
    have hn := mul_neg_of_pos_of_neg hκ hp.2.2
    linarith
  exact if_neg hh

end Yau.NodeProofs.F01Aux
