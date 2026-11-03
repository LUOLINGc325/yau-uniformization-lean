import Yau.Proofs.V02DiscDbar
import Yau.Proofs.V03ClosedDiscTower
import Yau.Proofs.V03HolomorphicDifferential

/-! Real smoothness on the closed disc and complex holomorphicity in its
interior imply the original complex C∞ regularity on the closed disc. -/

open scoped Topology ContDiff

noncomputable section
namespace Yau.Blueprint.V02Proof
open Yau Yau.LeafProofs

def realXJet (f : ℂ → ℂ) : ℕ → ℂ → ℂ
  | 0 => f
  | k + 1 => discEnergyPartial (realXJet f k) 1

theorem realXJet_contDiffOn {f : ℂ → ℂ}
    (hf : ContDiffOn ℝ ∞ f (Metric.closedBall (0 : ℂ) 1)) (k : ℕ) :
    ContDiffOn ℝ ∞ (realXJet f k) (Metric.closedBall (0 : ℂ) 1) := by
  induction k with
  | zero => exact hf
  | succ k hk => exact discEnergyPartial_contDiffOn hk 1

theorem realPartial_eq_complexDerivative {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (Metric.ball (0 : ℂ) 1))
    {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) 1) :
    discEnergyPartial f 1 z = fderiv ℂ f z 1 := by
  have hd := (hf z hz).differentiableAt (Metric.isOpen_ball.mem_nhds hz)
  rw [discEnergyPartial_eq_fderiv f 1 hz, hd.fderiv_restrictScalars (𝕜 := ℝ)]
  rfl

theorem realXJet_holomorphic {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (Metric.ball (0 : ℂ) 1)) (k : ℕ) :
    DifferentiableOn ℂ (realXJet f k) (Metric.ball (0 : ℂ) 1) := by
  induction k with
  | zero => exact hf
  | succ k hk =>
    have hd := V03Proof.complex_holomorphic_fderiv_apply_differentiableOn Metric.isOpen_ball hk (1 : ℂ)
    exact hd.congr (fun z hz => realPartial_eq_complexDerivative hk hz)

theorem real_closed_holomorphic_contDiffOn {f : ℂ → ℂ}
    (hreal : ContDiffOn ℝ ∞ f (Metric.closedBall (0 : ℂ) 1))
    (hhol : DifferentiableOn ℂ f (Metric.ball (0 : ℂ) 1)) :
    ContDiffOn ℂ ∞ f (Metric.closedBall (0 : ℂ) 1) := by
  apply V03Proof.contDiffOn_closedDisc_of_derivative_tower (realXJet f)
    (fun k => (realXJet_contDiffOn hreal k).continuousOn)
  intro k z hz
  have hk := realXJet_holomorphic hhol k
  have hd := (hk z hz).differentiableAt (Metric.isOpen_ball.mem_nhds hz)
  have he : realXJet f (k + 1) z = fderiv ℂ (realXJet f k) z 1 :=
    realPartial_eq_complexDerivative hk hz
  rw [he]
  exact hd.hasFDerivAt.hasDerivAt

end Yau.Blueprint.V02Proof
