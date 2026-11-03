import Yau.Proofs.V02FlowEuclideanCore
import Mathlib.Analysis.Calculus.MeanValue

/-! Natural local existence with a radius chosen before initial points and jet orders. -/

open scoped Topology ContDiff NNReal
open Metric

noncomputable section
namespace Yau.Blueprint.V02FlowProof
open V03Proof

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [FiniteDimensional ℂ V] [CompleteSpace V]

theorem exists_local_holomorphic_flow {Ω : Set V} {W : V → V} {a : V}
    (hΩ : IsOpen Ω) (hW : DifferentiableOn ℂ W Ω) (ha : a ∈ Ω) :
    ∃ d R : ℝ, 0 < d ∧ 0 < R ∧ closedBall a (3 * d) ⊆ Ω ∧
      ∃ Φ : ℂ × V → V,
        (∀ x, Φ (0, x) = x) ∧
        ContDiffOn ℂ ∞ Φ (ball (0 : ℂ) R ×ˢ ball a d) ∧
        (∀ t ∈ ball (0 : ℂ) R, ∀ x ∈ ball a d,
          Φ (t, x) ∈ ball a (2 * d) ∧
          HasDerivAt (fun z : ℂ => Φ (z, x)) (W (Φ (t, x))) t) ∧
        (∀ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧
          ∀ p ∈ closedBall (0 : ℂ) (R / 2) ×ˢ closedBall a (d / 2),
            ‖iteratedFDeriv ℝ m Φ p‖ ≤ C) := by
  let := FiniteDimensional.proper ℂ V
  obtain ⟨ε, hε, hεΩ⟩ := Metric.isOpen_iff.mp hΩ a ha
  let d := ε / 4
  have hd : 0 < d := by dsimp [d]; positivity
  have hball3 : closedBall a (3 * d) ⊆ Ω := by
    intro z hz
    exact hεΩ (mem_ball.mpr (lt_of_le_of_lt (mem_closedBall.mp hz)
      (by dsimp [d]; linarith)))
  have hball : closedBall a (2 * d) ⊆ Ω :=
    (closedBall_subset_closedBall (by linarith)).trans hball3
  have hcompact := isCompact_closedBall a (2 * d)
  obtain ⟨M₀, hM₀⟩ := (hcompact.image_of_continuousOn
    (hW.continuousOn.mono hball)).isBounded.exists_norm_le
  let M := max M₀ 0
  have hM : 0 ≤ M := le_max_right _ _
  have hbound : ∀ z ∈ closedBall a (2 * d), ‖W z‖ ≤ M :=
    fun z hz => (hM₀ _ ⟨z, hz, rfl⟩).trans (le_max_left _ _)
  obtain ⟨L₀, hL₀⟩ := (hcompact.image_of_continuousOn
    ((complex_holomorphic_continuousOn_fderiv hΩ hW).mono hball)).isBounded.exists_norm_le
  let L : ℝ≥0 := ⟨max L₀ 0, le_max_right _ _⟩
  have hLip : LipschitzOnWith L W (closedBall a (2 * d)) :=
    Convex.lipschitzOnWith_of_nnnorm_fderiv_le
      (fun z hz => (hW z (hball hz)).differentiableAt (hΩ.mem_nhds (hball hz)))
      (fun z hz => by
        change ‖fderiv ℂ W z‖ ≤ max L₀ 0
        exact (hL₀ _ ⟨z, hz, rfl⟩).trans (le_max_left _ _))
      (convex_closedBall a (2 * d))
  let R := min (d / (2 * (M + 1))) (1 / (2 * ((L : ℝ) + 1)))
  have hR : 0 < R := lt_min (by positivity) (by positivity)
  have hRM : R * M ≤ d / 2 := by
    have h := (le_div_iff₀ (by positivity : 0 < 2 * (M + 1))).mp
      (min_le_left (d / (2 * (M + 1))) (1 / (2 * ((L : ℝ) + 1))))
    change R * (2 * (M + 1)) ≤ d at h
    nlinarith
  have hRL : R * L ≤ 1 / 2 := by
    have h := (le_div_iff₀ (by positivity : 0 < 2 * ((L : ℝ) + 1))).mp
      (min_le_right (d / (2 * (M + 1))) (1 / (2 * ((L : ℝ) + 1))))
    change R * (2 * ((L : ℝ) + 1)) ≤ 1 at h
    nlinarith
  obtain ⟨Φ, hzero, hsmooth, _, _, hode⟩ := exists_quantitative_holomorphic_flow
    hΩ hW hd hR hM hball hbound hLip hRM hRL
  refine ⟨d, R, hd, hR, hball3, Φ, hzero, hsmooth, hode, fun m => ?_⟩
  apply compact_iteratedFDeriv_bound (f := Φ)
    (O := ball (0 : ℂ) R ×ˢ ball a d)
    (K := closedBall (0 : ℂ) (R / 2) ×ˢ closedBall a (d / 2))
    (isOpen_ball.prod isOpen_ball)
    ((isCompact_closedBall (0 : ℂ) (R / 2)).prod (isCompact_closedBall a (d / 2)))
    (fun p hp => ⟨mem_ball.mpr ((mem_closedBall.mp hp.1).trans_lt (by linarith)),
      mem_ball.mpr ((mem_closedBall.mp hp.2).trans_lt (by linarith))⟩)
    (hsmooth.restrict_scalars ℝ) m

end Yau.Blueprint.V02FlowProof
