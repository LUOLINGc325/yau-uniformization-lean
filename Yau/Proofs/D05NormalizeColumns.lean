import Yau.Proofs.D05BoundaryGram
import Yau.Proofs.D06OriginalBoundaryBridge

/-! Normalize the actual ambient columns using precisely Hinv=P of the
original D06 BoundarySource. All identities hold on the closed disc. -/

open scoped Topology ContDiff Matrix
noncomputable section
namespace Yau.Blueprint.D05Proof
open Yau V03Proof

theorem normalize_ambient_columns {q r : ℕ} {ρ : ℝ} (hρ : 1 < ρ)
    (V : ℂ → Matrix (Fin q) (Fin r) ℂ)
    (hV : ∀ a j, ContDiffOn ℂ ∞ (fun z => V z a j) (Metric.ball 0 ρ))
    (hi : ∀ z ∈ Metric.ball (0 : ℂ) ρ, Function.Injective (V z).mulVec) :
    ∃ W : ℂ → Matrix (Fin q) (Fin r) ℂ,
      (∀ a j, ContDiffOn ℂ ∞ (fun z => W z a j) (Metric.closedBall 0 1)) ∧
      (∀ z ∈ Metric.closedBall (0 : ℂ) 1, Function.Injective (W z).mulVec ∧
        LinearMap.range (Matrix.toEuclideanLin (W z)) =
          LinearMap.range (Matrix.toEuclideanLin (V z))) ∧
      ∀ θ, Matrix.conjTranspose (W (circlePoint θ)) * W (circlePoint θ) = 1 := by
  obtain ⟨s, hs⟩ := boundary_gram_source hρ V hV hi
  have hD : Metric.closedBall (0 : ℂ) 1 ⊆ Metric.ball 0 ρ := by
    intro z hz
    exact (Metric.closedBall_subset_ball hρ) hz
  have hH : ContinuousOn s.H (Metric.closedBall (0 : ℂ) 1) :=
    continuousOn_pi.mpr fun i => continuousOn_pi.mpr fun j =>
      (s.closed_complex_smooth i j).1.continuousOn
  have hP : ContinuousOn s.Hinv (Metric.closedBall (0 : ℂ) 1) :=
    continuousOn_pi.mpr fun i => continuousOn_pi.mpr fun j =>
      (s.closed_complex_smooth i j).2.continuousOn
  have hHP := s.closed_inverse hH hP
  let W : ℂ → Matrix (Fin q) (Fin r) ℂ := fun z => V z * s.Hinv z
  refine ⟨W, matrix_mul_contDiffOn (fun a j => (hV a j).mono hD)
    (fun i j => (s.closed_complex_smooth i j).2), ?_, ?_⟩
  · intro z hz
    have hPi : Function.Injective (s.Hinv z).mulVec := by
      intro u v huv
      have h := congrArg (fun w => s.H z *ᵥ w) huv
      simpa only [Matrix.mulVec_mulVec, (hHP z hz).1, Matrix.one_mulVec] using h
    have hWi : Function.Injective (W z).mulVec := by
      intro u v huv
      apply hPi
      apply hi z (hD hz)
      simpa only [W, Matrix.mulVec_mulVec] using huv
    refine ⟨hWi, le_antisymm (matrix_range_mul_le _ _) ?_⟩
    have heq : W z * s.H z = V z := by
      dsimp only [W]
      rw [Matrix.mul_assoc, (hHP z hz).2, Matrix.mul_one]
    have hle := matrix_range_mul_le (W z) (s.H z)
    rw [heq] at hle
    exact hle
  · intro θ
    have hz := circlePoint_mem_closedBall θ
    have hfactor : Matrix.conjTranspose (V (circlePoint θ)) * V (circlePoint θ) =
        Matrix.conjTranspose (s.H (circlePoint θ)) * s.H (circlePoint θ) :=
      (hs θ).symm.trans (s.boundary_factor hH θ)
    change Matrix.conjTranspose (V (circlePoint θ) * s.Hinv (circlePoint θ)) *
      (V (circlePoint θ) * s.Hinv (circlePoint θ)) = 1
    calc
      _ = Matrix.conjTranspose (s.Hinv (circlePoint θ)) *
          (Matrix.conjTranspose (V (circlePoint θ)) * V (circlePoint θ)) *
            s.Hinv (circlePoint θ) := by simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Matrix.conjTranspose (s.H (circlePoint θ) * s.Hinv (circlePoint θ)) *
          (s.H (circlePoint θ) * s.Hinv (circlePoint θ)) := by
        rw [hfactor]
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = 1 := by rw [(hHP _ hz).1]; simp

end Yau.Blueprint.D05Proof
