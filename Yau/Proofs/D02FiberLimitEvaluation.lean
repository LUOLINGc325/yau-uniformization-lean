import Yau.Proofs.D02CotangentEnclosure
import Yau.Proofs.D02MontelDerivative

open scoped Manifold Topology ContDiff
open Filter Set

noncomputable section
namespace Yau.NodeProofs.D02FiberLimitAux
open Yau Yau.Blueprint Yau.Blueprint.V03Proof Yau.NodeProofs.D02Aux

/-- The same finite tuple of actual intrinsic evaluations. Its Pi norm also
handles the empty tuple, without choosing independent scalar subsequences. -/
def evaluationVector {n m : ℕ} {M : ComplexManifold n}
    (V : Fin m → VectorField M) (y : CotangentPoint M) : Fin m → ℂ :=
  fun i ↦ fieldEvaluation (V i) y

/-- The original compact boundary box and scalar maximum principle bound the
whole family before the extraction. One vector Montel gives one extraction. -/
theorem evaluationVector_subsequence {n m : ℕ} {M : ComplexManifold n}
    (g : HermitianField M) (hg : MetricSmooth g) {K : Set M.Carrier} (hK : IsCompact K)
    (R : ℝ) (V : Fin m → VectorField M) (hV : ∀ i, IsHolomorphicField (V i))
    (fs : ℕ → ℂ → M.Carrier) (ξs : ℕ → ℂ → Covector n)
    (hf : ∀ j, IsCotangentDisc (fs j) (ξs j))
    (hboundary : ∀ j z, ‖z‖ = 1 → InCotangentCompact g K R (fs j z) (ξs j z)) :
    ∃ α : ℕ → ℕ, StrictMono α ∧ ∃ e : ℂ → (Fin m → ℂ),
      DifferentiableOn ℂ e (Metric.ball 0 1) ∧
      TendstoLocallyUniformlyOn
        (fun j z ↦ evaluationVector V (fs (α j) z, ξs (α j) z)) e atTop (Metric.ball 0 1) := by
  classical
  have hbox := cotangentBoxCompact n M g hg K R hK
  choose C hCpos hC using fun i ↦ fieldEvaluation_bound_on_compact hbox (hV i)
  let B : ℝ := ∑ i, C i
  have hB : 0 ≤ B := Finset.sum_nonneg (fun i _ ↦ hCpos i)
  have hdiff : ∀ j, DifferentiableOn ℂ
      (fun z ↦ evaluationVector V (fs j z, ξs j z)) (Metric.ball 0 1) := by
    intro j
    apply differentiableOn_pi.mpr
    intro i
    exact (cotangentDisc_fieldEvaluation_differentiableOn (f := fun z ↦ (fs j z, ξs j z))
      (hf j) (hV i)).mono Metric.ball_subset_closedBall
  have hbound : ∀ j z, z ∈ Metric.ball (0 : ℂ) 1 →
      ‖evaluationVector V (fs j z, ξs j z)‖ ≤ B := by
    intro j z hz
    apply (pi_norm_le_iff_of_nonneg hB).mpr
    intro i
    have hi : ‖fieldEvaluation (V i) (fs j z, ξs j z)‖ ≤ C i := by
      apply cotangentDisc_fieldEvaluation_norm_le (f := fun z ↦ (fs j z, ξs j z)) (hf j) (hV i)
        (fun w hw ↦ hC i (fs j w, ξs j w) (hboundary j w hw)) z
      exact (show ‖z‖ < 1 by simpa only [Metric.mem_ball, dist_zero_right] using hz).le
    exact hi.trans (Finset.single_le_sum (fun a _ ↦ hCpos a) (Finset.mem_univ i))
  exact bounded_holomorphic_discs_subsequence
    (fun j z ↦ evaluationVector V (fs j z, ξs j z)) hdiff B hbound

end Yau.NodeProofs.D02FiberLimitAux
