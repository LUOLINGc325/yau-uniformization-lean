import Yau.Proofs.D06MatrixBootstrap
import Yau.Proofs.D06ClosedDiscJets
import Yau.Proofs.D06OriginalSourceInputs

/-! The source-defined fixed pair has all Sobolev orders and its own actual
Taylor sums are smooth on the exact closed unit disc. -/

open scoped ContDiff

noncomputable section
namespace Yau.NodeProofs.D06Aux
namespace BoundarySource

variable {r : ℕ} (s : BoundarySource r)

theorem pair_allSobolev : ∀ k : ℕ,
    (∀ i j, CircleSobolev k (s.hMatrix i j)) ∧ (∀ i j, CircleSobolev k (s.pMatrix i j)) :=
  circleMatrix_fixedPair_allSobolev s.lMatrix s.hMatrix s.pMatrix s.lMatrix_allSobolev
    (fun i j => (s.pair_firstSobolev i j).1) (fun i j => (s.pair_firstSobolev i j).2)
    s.hMatrix_hardy s.pMatrix_hardy s.pair_inverse_ae s.pair_gram_ae

theorem closed_smooth : ∀ i j,
    ContDiffOn ℝ ∞ (fun z => s.H z i j) (Metric.closedBall (0 : ℂ) 1) ∧
      ContDiffOn ℝ ∞ (fun z => s.Hinv z i j) (Metric.closedBall (0 : ℂ) 1) := by
  intro i j
  have hq : ∀ m : ℕ, Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ m * ‖s.qColumns j (n, i)‖) :=
    fun m => hardyEntry_weighted_summable (s.qColumns j) i (fun k => (s.pair_allSobolev k).1 i j) m
  have hp : ∀ m : ℕ, Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ m * ‖s.pColumns j (n, i)‖) :=
    fun m => hardyEntry_weighted_summable (s.pColumns j) i (fun k => (s.pair_allSobolev k).2 i j) m
  constructor
  · have h := Yau.Proofs.D06ClosedDiscJets.contDiffOn_tsum_mul (fun n => s.qColumns j (n, i)) hq
    have heq : (fun z => s.H z i j) = fun z => ∑' n : ℕ, z ^ n * s.qColumns j (n, i) :=
      funext (fun z => hardyEvalEntry_eq_tsum (s.qColumns j) i z)
    rw [heq]
    exact h
  · have h := Yau.Proofs.D06ClosedDiscJets.contDiffOn_tsum_mul (fun n => s.pColumns j (n, i)) hp
    have heq : (fun z => s.Hinv z i j) = fun z => ∑' n : ℕ, z ^ n * s.pColumns j (n, i) :=
      funext (fun z => hardyEvalEntry_eq_tsum (s.pColumns j) i z)
    rw [heq]
    exact h

end BoundarySource
end Yau.NodeProofs.D06Aux
