import Yau.Proofs.D03ClosureSubmodule

open scoped Manifold Topology ContDiff ENNReal
open MeasureTheory Set Filter Metric Bundle

noncomputable section

namespace Yau.Proofs.D03Aux
open Yau Yau.Blueprint Yau.Blueprint.BundlePresentation

variable {M : ComplexManifold 1} {r q : ℕ}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

/-- Actual germ membership and original fibrewise injectivity recover the exact original integral. -/
theorem extra_integrability_of_imageGerm_mem (c : DiscCoordinate M) (hc : IsDiscCoordinate c)
    (k : BundleDbar.Metric E) (hk : BundleDbar.SmoothMetric (r := r) E k)
    (A : MapToTrivial E q) (hA : PointwiseInjective E A) (s : Section E)
    (F : ℂ → ComplexVector q) (hF0 : AnalyticAt ℂ F 0) (R : ℝ) (hR : 0 < R)
    (hImage : ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ < R → F z = A (c.symm z) (s (c.symm z)))
    (hmem : vectorGerm F hF0 ∈ extraImageGerms E c hc k hk A) :
    ∃ ρ σ : ℝ, 0 < ρ ∧ ρ < 1 ∧ 0 < σ ∧ weightedSectionIntegral E c k s ρ σ < ⊤ := by
  change extraImageGermCarrier (r := r) E c k A (vectorGerm F hF0) at hmem
  rcases hmem with ⟨ρ, ε, hρ, hρ1, hε, b, hb, hbI, G, hG0, hG, hGF, hGb⟩
  have he := (vectorGerm_eq_iff G F hG0 hF0).1 hGF
  obtain ⟨δ, hδ, hδball⟩ := Metric.mem_nhds_iff.mp he
  let m := min ρ (min δ R)
  let τ := m / 2
  have hm : 0 < m := lt_min hρ (lt_min hδ hR)
  have hτ : 0 < τ := half_pos hm
  have hτm : τ < m := half_lt_self hm
  have hτρ : τ < ρ := hτm.trans_le (min_le_left ρ (min δ R))
  have hτδ : τ < δ := hτm.trans_le ((min_le_right ρ (min δ R)).trans (min_le_left δ R))
  have hτR : τ < R := hτm.trans_le ((min_le_right ρ (min δ R)).trans (min_le_right δ R))
  have hsb (x : M.Carrier) (hx : x ∈ discSectionDomain c τ) : s x = b x := by
    apply hA x
    have hf := hImage (c x) hx.1 (hx.2.trans hτR)
    have hg := hGb (c x) hx.1 (hx.2.trans hτρ)
    have heq := hδball (show c x ∈ ball (0 : ℂ) δ from by
      rw [mem_ball_zero_iff]
      exact hx.2.trans hτδ)
    rw [B01Aux.disc_left_inv c hc] at hf hg
    exact hf.symm.trans (heq.symm.trans hg)
  have hI : weightedSectionIntegral E c k s τ ε = weightedSectionIntegral E c k b τ ε := by
    unfold weightedSectionIntegral
    apply setLIntegral_congr_fun (discSectionDomain_isOpen c hc τ).measurableSet
    intro x hx
    change ENNReal.ofReal (hermitianNormSq (k x) (s x) * ‖c x‖ ^ (-ε)) =
      ENNReal.ofReal (hermitianNormSq (k x) (b x) * ‖c x‖ ^ (-ε))
    rw [hsb x hx]
  refine ⟨τ, ε, hτ, hτρ.trans hρ1, hε, ?_⟩
  rw [hI]
  exact (closure_weighted_radius_mono E c k b hτρ.le ε).trans_lt hbI

end Yau.Proofs.D03Aux
