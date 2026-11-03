import Yau.Proofs.V02TestHessianBounds
import Yau.Proofs.V02DampingBoundaryLoss
import Yau.Proofs.V03SymbolBounds

/-! Uniform absolute bounds for the actual center and boundary quadratic
tests. These multiply the auxiliary damping losses, never the penalty. -/

open scoped Topology ContDiff Matrix
open Metric Set

noncomputable section
namespace Yau.Blueprint.V02Proof
open Yau Yau.Blueprint V03Proof

variable {n q : ℕ} {X : KahlerManifold n}

theorem test_quadratic_loss_bounds {d : VariationData X q} (hd : VariationSetup d)
    (j a : ℕ) (ha : 4 ≤ a) (L : ℝ) :
    ∃ M₀ M₁ : ℝ, 0 ≤ M₀ ∧ 0 ≤ M₁ ∧
      ∀ (F : VariationDisc X) (E : ℂ → CotangentMatrix n)
        (l : ℂ → CotangentIndex n → ℂ),
        AdmissibleVariationDisc d j F → NormalizedDiscFrame d.G F.f E →
        (∀ ζ ∈ closedBall (0 : ℂ) 1, ∑ i, ‖l ζ i‖ ^ 2 ≤ L ^ 2) →
        |outerCenter d j a F ^ 2 * quadValue (centerTestHessian d F E) (l 0)| ≤ M₀ ∧
        ∀ θ, |quadValue (boundarySymbol d j a F E (circlePoint θ))
          (l (circlePoint θ))| ≤ M₁ := by
  obtain ⟨M₀, hM₀, hcenter⟩ := centerTest_quadratic_uniform_bound hd L
  obtain ⟨B, hB, hsymbol⟩ := symbolBounds hd a ha j
  refine ⟨M₀, B * L ^ 2, hM₀, mul_nonneg hB (sq_nonneg _), fun F E l hF hE hl => ?_⟩
  constructor
  · rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
    have ht := outerCenter_pos_le_one hd hF a
    have hs : outerCenter d j a F ^ 2 ≤ 1 := by nlinarith
    exact (mul_le_mul_of_nonneg_right hs (abs_nonneg _)).trans
      (by simpa only [one_mul] using hcenter j F E l hF hE hl)
  · intro θ
    exact (abs_quadValue_le_rectOpNorm _ _).trans
      (mul_le_mul ((hsymbol F E hF hE).1 θ).2
        (hl _ (circlePoint_mem_closedBall θ))
        (Finset.sum_nonneg (fun i _ => sq_nonneg _)) hB)

end Yau.Blueprint.V02Proof
