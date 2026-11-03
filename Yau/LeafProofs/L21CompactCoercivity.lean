import Yau.LeafProofs.L21ScaledCoreEnergy

/-! Actual compact coercivity for the concrete degenerate weighted
complex. Both dimension-dependent constants precede the smooth graph. -/

open scoped ContDiff
noncomputable section
namespace Yau.LeafProofs.L21Aux

theorem exists_compact_degenerate_coercivity (n : ℕ) :
    ∃ ε K : ℝ, 0 < ε ∧ 0 < K ∧
    ∀ (A : X n → Matrix (Fin n) (Fin n) ℂ),
      MatrixSmoothOn A (Metric.ball (0 : X n) 2) →
      JetBound 1 ε A (Metric.ball 0 2) → JetBound 2 1 A (Metric.ball 0 2) →
      ∀ v : Fin n → CompactTest (Metric.ball (0 : X n) 1),
        (∑ j, weightedScalarEnergy (boundaryWeight K) (v j)) ≤
          weightedScalarEnergy (boundaryWeight K) (fun x =>
            ∑ j, weightedDStar A (boundaryWeight K) j (fun y => (rho y : ℂ) * v j y) x) +
          (∑ i, ∑ j, weightedScalarEnergy (boundaryWeight K)
            (fun x => degenerateS A (fun y k => v k y) x i j)) := by
  obtain ⟨ε, C0, hε, hC0, hCoercive⟩ := exists_uniform_unscaled_coercivity n
  let K : ℝ := 4 * (C0 + scaledCoreRemainder n + 1)
  have hCScaled := scaledCoreRemainder_nonneg n
  have hK : 0 < K := by dsimp [K]; positivity
  have hKlarge : 4 * C0 ≤ K := by dsimp [K]; linarith
  have hKvalue : K / 4 = C0 + scaledCoreRemainder n + 1 := by dsimp [K]; ring
  refine ⟨ε, K, hε, hK, ?_⟩
  intro A hA hSmall hJet v
  have hB : Metric.ball (0 : X n) 1 ⊆ Metric.ball (0 : X n) 2 :=
    Metric.ball_subset_ball (by norm_num)
  have hA1 : MatrixSmoothOn A (Metric.ball (0 : X n) 1) := fun i j => (hA i j).mono hB
  have hSmall1 : JetBound 1 ε A (Metric.ball 0 1) := fun m hm x hx i j => hSmall m hm x (hB hx) i j
  have hJet1 : JetBound 2 1 A (Metric.ball 0 1) := fun m hm x hx i j => hJet m hm x (hB hx) i j
  have hJet0 : JetBound 0 1 A (Metric.ball 0 1) := fun m hm x hx i j => hJet1 m (by omega) x hx i j
  have hLow := hCoercive A hA1 hSmall1 hJet1 K hKlarge
    (fun i => testRhoMul Metric.isOpen_ball (v i))
  simp only [testRhoInverse_testRhoMul] at hLow
  have hUp := compactFormQ_scaled_upper hA1 hJet0 (contDiffOn_boundaryWeight K) v
  rw [hKvalue] at hLow
  have hE := coreScalarEnergy_nonneg (boundaryWeight K) v
  have hC0E := mul_nonneg hC0.le hE
  change coreScalarEnergy (boundaryWeight K) v ≤ _
  linarith

end Yau.LeafProofs.L21Aux
