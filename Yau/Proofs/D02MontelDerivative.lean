import Yau.Proofs.D02Montel

/-! The same bounded holomorphic extraction retains the bound and
converges together with its actual complex first derivative. -/

open scoped Topology
open Filter

noncomputable section
namespace Yau.NodeProofs.D02Aux

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H] [ProperSpace H]

theorem bounded_holomorphic_discs_subsequence_derivative
    (fs : ℕ → ℂ → H) (hf : ∀ j, DifferentiableOn ℂ (fs j) (Metric.ball 0 1))
    (B : ℝ) (hb : ∀ j z, z ∈ Metric.ball (0 : ℂ) 1 → ‖fs j z‖ ≤ B) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ f : ℂ → H,
      DifferentiableOn ℂ f (Metric.ball 0 1) ∧
      (∀ z ∈ Metric.ball (0 : ℂ) 1, ‖f z‖ ≤ B) ∧
      TendstoLocallyUniformlyOn (fun j => fs (φ j)) f atTop (Metric.ball 0 1) ∧
      TendstoLocallyUniformlyOn (fun j => deriv (fs (φ j))) (deriv f) atTop (Metric.ball 0 1) := by
  obtain ⟨φ, hφ, f, hf', hconv⟩ := bounded_holomorphic_discs_subsequence fs hf B hb
  refine ⟨φ, hφ, f, hf', ?_, hconv, ?_⟩
  · intro z hz
    exact le_of_tendsto (hconv.tendsto_at hz).norm (Eventually.of_forall fun j => hb (φ j) z hz)
  · exact hconv.deriv (Eventually.of_forall fun j => hf (φ j)) Metric.isOpen_ball

end Yau.NodeProofs.D02Aux
