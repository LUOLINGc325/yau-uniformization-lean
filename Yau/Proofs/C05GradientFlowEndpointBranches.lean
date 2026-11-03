import Yau.LeafProofs.L12ShortBranches

/-! Two actual short endpoint branches about one fixed geodesic. -/
noncomputable section
open Filter
open scoped Topology Manifold ContDiff
namespace Yau.Proofs.C05GradientFlowAux
open Yau Yau.LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5
set_option maxHeartbeats 1200000

theorem exists_geodesic_two_short_endpoint_branches (g : SmoothMetric M)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) :
    letI := manifold_realSmooth M
    letI := manifold_realPhase M
    ∃ s d : ℝ, 0 < s ∧ 0 < d ∧ s + d < 1 ∧
      ∃ U₀ U₁ : Set (M.Carrier × M.Carrier), IsOpen U₀ ∧ IsOpen U₁ ∧
      (p.proj, (realGeodesicFlow g p s).proj) ∈ U₀ ∧
      ((realGeodesicFlow g p (1 - d)).proj, (realGeodesicFlow g p 1).proj) ∈ U₁ ∧
      ∃ P₀ P₁ : M.Carrier × M.Carrier → TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier,
        ContMDiffOn (𝓘(ℝ, ComplexVector n).prod 𝓘(ℝ, ComplexVector n))
          (realPhaseModel n) 1 P₀ U₀ ∧
        ContMDiffOn (𝓘(ℝ, ComplexVector n).prod 𝓘(ℝ, ComplexVector n))
          (realPhaseModel n) 1 P₁ U₁ ∧
        P₀ (p.proj, (realGeodesicFlow g p s).proj) = p ∧
        P₁ ((realGeodesicFlow g p (1 - d)).proj, (realGeodesicFlow g p 1).proj) =
          realGeodesicFlow g p (1 - d) ∧
        (∀ z ∈ U₀, (P₀ z).proj = z.1 ∧ (realGeodesicFlow g (P₀ z) s).proj = z.2) ∧
        (∀ z ∈ U₁, (P₁ z).proj = z.1 ∧ (realGeodesicFlow g (P₁ z) d).proj = z.2) := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  have hpos : ∀ᶠ s in 𝓝[>] (0 : ℝ), 0 < s := self_mem_nhdsWithin
  have hsmall : ∀ᶠ s in 𝓝[>] (0 : ℝ), s < 1 / 4 :=
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 4)).filter_mono nhdsWithin_le_nhds
  obtain ⟨s, hs, hs4, hsdet⟩ :=
    (hpos.and (hsmall.and (realGeodesicJacobiMatrix_det_pos_near_zero g p))).exists
  let qR := realPhaseScale (-1) (realGeodesicFlow g p 1)
  obtain ⟨d, hd, hd4, hddet⟩ :=
    (hpos.and (hsmall.and (realGeodesicJacobiMatrix_det_pos_near_zero g qR))).exists
  let q := realGeodesicFlow g p (1 - d)
  have hterminal : realGeodesicFlow g q d = realGeodesicFlow g p 1 := by
    dsimp only [q]
    rw [← realGeodesicFlow_add]
    congr 1
    ring
  have hreverse : realSegmentReverse g d q = qR := by
    dsimp only [realSegmentReverse, qR]
    rw [hterminal]
  obtain ⟨U₀, hU₀, hpU₀, P₀, hP₀, hP₀p, hends₀, _⟩ :=
    exists_realGeodesic_endpointBranch g p s (ne_of_gt hsdet)
  obtain ⟨U₁, hU₁, hqU₁, P₁, hP₁, hP₁q, hends₁, _⟩ :=
    exists_realGeodesic_endpointBranch_reversed g q d
      (by rw [hreverse]; exact ne_of_gt hddet)
  have heq : realGeodesicEndpointMap g d q =
      ((realGeodesicFlow g p (1 - d)).proj, (realGeodesicFlow g p 1).proj) := by
    simp only [realGeodesicEndpointMap, hterminal, q]
  rw [heq] at hqU₁ hP₁q
  exact ⟨s, d, hs, hd, by linarith, U₀, U₁, hU₀, hU₁, hpU₀, hqU₁,
    P₀, P₁, hP₀, hP₁, hP₀p, hP₁q, hends₀, hends₁⟩

end Yau.Proofs.C05GradientFlowAux
