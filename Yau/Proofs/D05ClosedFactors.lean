import Yau.Proofs.D06OriginalRegularity
import Yau.Proofs.V03SmoothPowerSeries

/-! Complex smoothness on the closed disc of the original D06 Hardy pair.
The entries and coefficients here are the source-defined factors themselves. -/

open scoped ContDiff

noncomputable section
namespace Yau.NodeProofs.D06Aux.BoundarySource

variable {r : ℕ} (s : BoundarySource r)

private theorem coefficient_power_summable (a : HardySeq r) (i : Fin r)
    (ha : ∀ k : ℕ, CircleSobolev k (hardyTraceLp a i)) (k : ℕ) :
    Summable (fun ν : ℕ => (ν : ℝ) ^ k * ‖a (ν, i)‖) := by
  apply (hardyEntry_weighted_summable a i ha k).of_nonneg_of_le
    (fun _ => by positivity)
  intro ν
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast Nat.le_succ ν) k

theorem closed_complex_smooth : ∀ i j,
    ContDiffOn ℂ ∞ (fun z => s.H z i j) (Metric.closedBall (0 : ℂ) 1) ∧
      ContDiffOn ℂ ∞ (fun z => s.Hinv z i j) (Metric.closedBall (0 : ℂ) 1) := by
  intro i j
  constructor
  · have h := Yau.Blueprint.V03Proof.contDiffOn_powerSeries_closedDisc
      (b := fun ν => s.qColumns j (ν, i))
      (coefficient_power_summable (s.qColumns j) i
        (fun k => (s.pair_allSobolev k).1 i j))
    have heq : (fun z => s.H z i j) =
        fun z => ∑' ν : ℕ, s.qColumns j (ν, i) * z ^ ν := by
      funext z
      exact (hardyEvalEntry_eq_tsum (s.qColumns j) i z).trans
        (tsum_congr fun _ => mul_comm _ _)
    rw [heq]
    exact h
  · have h := Yau.Blueprint.V03Proof.contDiffOn_powerSeries_closedDisc
      (b := fun ν => s.pColumns j (ν, i))
      (coefficient_power_summable (s.pColumns j) i
        (fun k => (s.pair_allSobolev k).2 i j))
    have heq : (fun z => s.Hinv z i j) =
        fun z => ∑' ν : ℕ, s.pColumns j (ν, i) * z ^ ν := by
      funext z
      exact (hardyEvalEntry_eq_tsum (s.pColumns j) i z).trans
        (tsum_congr fun _ => mul_comm _ _)
    rw [heq]
    exact h

end Yau.NodeProofs.D06Aux.BoundarySource
