import Yau.Proofs.V02FlowEuclidean

/-! Finite families share genuine compact field bounds and one time radius. -/

open scoped Topology ContDiff NNReal
open Metric

noncomputable section
namespace Yau.Blueprint.V02FlowProof
open V03Proof

variable {V ι : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [FiniteDimensional ℂ V] [CompleteSpace V] [Fintype ι]

theorem finite_holomorphic_family_bounds
    (Ω : ι → Set V) (W : ι → V → V) (a : ι → V) (d : ℝ)
    (hΩ : ∀ i, IsOpen (Ω i)) (hW : ∀ i, DifferentiableOn ℂ (W i) (Ω i))
    (hball : ∀ i, closedBall (a i) d ⊆ Ω i) :
    ∃ (M : ℝ) (L : ℝ≥0), 0 ≤ M ∧ ∀ i,
      (∀ z ∈ closedBall (a i) d, ‖W i z‖ ≤ M) ∧
      LipschitzOnWith L (W i) (closedBall (a i) d) := by
  classical
  let := FiniteDimensional.proper ℂ V
  have hlocal : ∀ i, ∃ (M : ℝ) (L : ℝ≥0), 0 ≤ M ∧
      (∀ z ∈ closedBall (a i) d, ‖W i z‖ ≤ M) ∧
      LipschitzOnWith L (W i) (closedBall (a i) d) := by
    intro i
    have hK := isCompact_closedBall (a i) d
    obtain ⟨M, hM⟩ := (hK.image_of_continuousOn
      ((hW i).continuousOn.mono (hball i))).isBounded.exists_norm_le
    obtain ⟨L, hL⟩ := (hK.image_of_continuousOn
      ((complex_holomorphic_continuousOn_fderiv (hΩ i) (hW i)).mono (hball i))).isBounded.exists_norm_le
    refine ⟨max M 0, ⟨max L 0, le_max_right _ _⟩, le_max_right _ _,
      fun z hz => (hM _ ⟨z, hz, rfl⟩).trans (le_max_left _ _), ?_⟩
    apply Convex.lipschitzOnWith_of_nnnorm_fderiv_le
      (fun z hz => (hW i z (hball i hz)).differentiableAt ((hΩ i).mem_nhds (hball i hz)))
      (fun z hz => ?_) (convex_closedBall (a i) d)
    change ‖fderiv ℂ (W i) z‖ ≤ max L 0
    exact (hL _ ⟨z, hz, rfl⟩).trans (le_max_left _ _)
  choose M L hM hbound hLip using hlocal
  refine ⟨∑ i, M i, ∑ i, L i, Finset.sum_nonneg (fun i _ => hM i), fun i => ⟨?_, ?_⟩⟩
  · intro z hz
    exact (hbound i z hz).trans
      (Finset.single_le_sum (fun j _ => hM j) (Finset.mem_univ i))
  · exact (hLip i).weaken
      (Finset.single_le_sum (fun j _ => (show (0 : ℝ≥0) ≤ L j from bot_le)) (Finset.mem_univ i))

theorem exists_finite_uniform_holomorphic_flows
    (Ω : ι → Set V) (W : ι → V → V) (a : ι → V) {δ : ℝ} (hδ : 0 < δ)
    (hΩ : ∀ i, IsOpen (Ω i)) (hW : ∀ i, DifferentiableOn ℂ (W i) (Ω i))
    (hball : ∀ i, closedBall (a i) (8 * δ) ⊆ Ω i) :
    ∃ (R M : ℝ) (Φ : ι → ℂ × V → V), 0 < R ∧ 0 ≤ M ∧ R * M ≤ δ / 4 ∧
      ∀ i, (∀ x, Φ i (0, x) = x) ∧
        ContDiffOn ℂ ∞ (Φ i) (ball (0 : ℂ) R ×ˢ ball (a i) (4 * δ)) ∧
        ContinuousOn (Φ i) (closedBall (0 : ℂ) R ×ˢ closedBall (a i) (4 * δ)) ∧
        (∀ p ∈ closedBall (0 : ℂ) R ×ˢ closedBall (a i) (4 * δ),
          ‖Φ i p - p.2‖ ≤ ‖p.1‖ * M) ∧
        (∀ t ∈ ball (0 : ℂ) R, ∀ x ∈ ball (a i) (4 * δ),
          Φ i (t, x) ∈ ball (a i) (8 * δ) ∧
          HasDerivAt (fun z : ℂ => Φ i (z, x)) (W i (Φ i (t, x))) t) := by
  obtain ⟨M, L, hM, hbounds⟩ := finite_holomorphic_family_bounds Ω W a (8 * δ) hΩ hW hball
  let R := min (δ / (4 * (M + 1))) (1 / (2 * ((L : ℝ) + 1)))
  have hR : 0 < R := lt_min (by positivity) (by positivity)
  have hRM : R * M ≤ δ / 4 := by
    have h := (le_div_iff₀ (by positivity : 0 < 4 * (M + 1))).mp
      (min_le_left (δ / (4 * (M + 1))) (1 / (2 * ((L : ℝ) + 1))))
    change R * (4 * (M + 1)) ≤ δ at h
    nlinarith
  have hRL : R * L ≤ 1 / 2 := by
    have h := (le_div_iff₀ (by positivity : 0 < 2 * ((L : ℝ) + 1))).mp
      (min_le_right (δ / (4 * (M + 1))) (1 / (2 * ((L : ℝ) + 1))))
    change R * (2 * ((L : ℝ) + 1)) ≤ 1 at h
    nlinarith
  have hscale : 2 * (4 * δ) = 8 * δ := by ring
  have hflows := fun i => exists_quantitative_holomorphic_flow
    (a := a i) (d := 4 * δ) (R := R) (M := M) (L := L) (hΩ i) (hW i)
    (by positivity : 0 < 4 * δ) hR hM
    (by simpa only [hscale] using hball i)
    (by simpa only [hscale] using (hbounds i).1)
    (by simpa only [hscale] using (hbounds i).2)
    (hRM.trans (by linarith : δ / 4 ≤ 4 * δ / 2)) hRL
  choose Φ hΦ using hflows
  refine ⟨R, M, Φ, hR, hM, hRM, fun i => ?_⟩
  simpa only [picardOpenDomain, picardClosedDomain, show 2 * (4 * δ) = 8 * δ by ring] using hΦ i

end Yau.Blueprint.V02FlowProof
