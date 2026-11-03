import Yau.Proofs.F01CoefficientExtensions
import Yau.Proofs.F01MatrixSandwichMono

/-! Uniform positive matrix bounds for the ACTUAL rescaled conformal
coefficients. The constant precedes all centers, scales, and coordinates. -/
open Set Metric Matrix
open scoped ContDiff ComplexOrder Matrix.Norms.Frobenius
noncomputable section
namespace Yau.NodeProofs.F01Aux
variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype ι] [DecidableEq ι]

theorem actual_coefficient_matrix_bounds (b : E) {r c L M : ℝ}
    (hr : 0 < r) (hc : 0 < c) (hcr : c ≤ r / 12) (hL : 0 < L) (hM : 0 ≤ M)
    {u : E → ℝ} {G : E → Matrix ι ι ℂ}
    (hu : ContDiffOn ℝ ∞ u (ball b (4 * r)))
    (hG : ContDiffOn ℝ ∞ G (ball b (4 * r)))
    (hpos : ∀ y ∈ ball b (4 * r), (G y).PosDef)
    (hD : ∀ y ∈ ball b (4 * r), ‖fderiv ℝ u y‖ ≤ M)
    (hbudget : 2 * c * M / L ≤ 1 / 2) :
    ∃ D : ℝ, 0 < D ∧ ∀ z₀ δ z,
      z₀ ∈ closedBall b r → 0 < δ → δ ≤ 1 → 1 - u z₀ / L = δ → z ∈ ball (0 : E) 1 →
      (interiorExtension u G L c (z₀, δ, z) - ((D⁻¹ : ℝ) : ℂ) • 1).PosSemidef ∧
      ((D : ℂ) • 1 - interiorExtension u G L c (z₀, δ, z)).PosSemidef := by
  let K := closedBall b r ×ˢ (Icc (0 : ℝ) 1 ×ˢ closedBall (0 : E) 2)
  have hK : IsCompact K := compact_parameters_isCompact b r
  have hseg : ∀ θ ∈ K, ∀ t ∈ Icc (0 : ℝ) 1,
      segmentEvaluation c (θ, t) ∈ ball b (4 * r) :=
    fun θ hθ t ht => bufferParameters_segment_mem b hr hc.le hcr
      (compact_parameters_subset_buffer b hr hθ) ht
  have hmap : ∀ θ ∈ K, scaledEvaluation c θ ∈ ball b (4 * r) := by
    intro θ hθ
    simpa only [segmentEvaluation, scaledEvaluation, one_mul] using hseg θ hθ 1 ⟨by norm_num, le_rfl⟩
  have hR (θ : BoundaryParameters E) (hθ : θ ∈ K) :
      1 / 2 ≤ boundaryRatio u L c θ.1 θ.2.1 θ.2.2 ∧
      boundaryRatio u L c θ.1 θ.2.1 θ.2.2 ≤ 3 / 2 := by
    have hn : ‖θ.2.2‖ ≤ 2 := by simpa only [mem_closedBall, dist_zero_right] using hθ.2.2
    exact boundaryRatio_bounds_of_integral_budget u L c θ.1 θ.2.1 θ.2.2
      (boundaryRatio_budget_of_derivative_bound u θ.1 θ.2.2 (δ := θ.2.1) hL hc.le hM hn
        (fun t ht => hD _ (hseg θ hθ t ht)) hbudget)
  obtain ⟨VB, hVB, hKB, hfB⟩ := boundaryExtension_smooth_neighborhood b hr hc.le hcr hL hM hu hG hD hbudget
  have hposB : ∀ θ ∈ K, (boundaryExtension u G L c θ).PosDef := by
    intro θ hθ
    change ((c ^ 2 / (boundaryRatio u L c θ.1 θ.2.1 θ.2.2) ^ 2) • G (scaledEvaluation c θ)).PosDef
    apply (hpos _ (hmap θ hθ)).smul
    exact div_pos (sq_pos_of_pos hc) (sq_pos_of_pos (by linarith [(hR θ hθ).1]))
  obtain ⟨DB, hDB, hboundB⟩ := compact_posDef_matrix_sandwich hK
    (hfB.continuousOn.mono hKB) hposB
  obtain ⟨VI, hVI, hKI, hfI⟩ := interiorExtension_smooth_neighborhood b hr hc.le hcr hL hM hu hG hD hbudget
  have hIK : interiorParameters u L b r ⊆ K := by
    intro θ hθ
    exact ⟨hθ.1.1, ⟨by linarith [hθ.1.2.1.1], hθ.1.2.1.2⟩, hθ.1.2.2⟩
  have hposI : ∀ θ ∈ interiorParameters u L b r, (interiorExtension u G L c θ).PosDef := by
    intro θ hθ
    change (((c * θ.2.1) ^ 2 * Real.exp (conformalProfile (u (scaledEvaluation c θ) / L))) •
      G (scaledEvaluation c θ)).PosDef
    apply (hpos _ (hmap θ (hIK hθ))).smul
    exact mul_pos (sq_pos_of_pos (mul_pos hc (by linarith [hθ.1.2.1.1]))) (Real.exp_pos _)
  obtain ⟨DI, hDI, hboundI⟩ := compact_posDef_matrix_sandwich
    (interiorParameters_isCompact b hr hu.continuousOn L) (hfI.continuousOn.mono hKI) hposI
  let D := max DB DI + 1
  have hDpos : 0 < D := by dsimp [D]; linarith [le_max_left DB DI]
  have hDBD : DB ≤ D := by dsimp [D]; linarith [le_max_left DB DI]
  have hDID : DI ≤ D := by dsimp [D]; linarith [le_max_right DB DI]
  refine ⟨D, hDpos, ?_⟩
  intro z₀ δ z hz₀ hδ hδ1 hbase hz
  have hz2 : z ∈ closedBall (0 : E) 2 :=
    mem_closedBall.mpr ((mem_ball.mp hz).le.trans (by norm_num))
  have hθK : (z₀, δ, z) ∈ K := ⟨hz₀, ⟨hδ.le, hδ1⟩, hz2⟩
  by_cases hsmall : δ ≤ 1 / 8
  · have heq := boundaryExtension_eq_interiorExtension isOpen_ball hu G hL.ne' hδ hsmall
      z₀ z hbase (fun t ht => hseg _ hθK t ht)
      (by linarith [(hR _ hθK).1]) (hR _ hθK).2
    rw [← heq]
    exact matrix_sandwich_mono hDB hDpos hDBD (hboundB _ hθK)
  · have hθI : (z₀, δ, z) ∈ interiorParameters u L b r :=
      ⟨⟨hz₀, ⟨(lt_of_not_ge hsmall).le, hδ1⟩, hz2⟩, hbase⟩
    exact matrix_sandwich_mono hDI hDpos hDID (hboundI _ hθI)

end Yau.NodeProofs.F01Aux
