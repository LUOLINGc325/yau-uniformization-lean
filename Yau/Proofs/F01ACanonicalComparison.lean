import Yau.Proofs.F01ACanonicalGrowthShift
import Yau.Proofs.F01ASmoothComparison

/-! The smooth comparison passes to a fixed canonical section. The input
comparison concerns the same U/P for every weight and every time horizon. -/
noncomputable section
open Filter
open scoped Topology

namespace Yau.NodeProofs.F01Aux
open Yau Yau.Blueprint Yau.Proofs.P04Aux
variable {n : ℕ}
set_option backward.isDefEq.respectTransparency false

theorem canonical_comparison_of_smooth_comparison
    (X : KahlerManifold n) (o : Pt X) (u : Pt X → ℝ) (U P : STF X) (η : ℝ)
    (hcomparison : SmoothRicciWeightComparison X u U P η)
    (Ξ : Pt X → ℝ) (hΞ : SmoothFn Ξ)
    (hRic : ∀ x, HermLE (ricci X.metric.form x) (levi Ξ x))
    (hΞgrowth : ∃ cΞ : ℝ, ∀ x, Ξ x ≤ cΞ * (1 + distFrom X.metric.form o x ^ ((3 : ℝ) / 2)))
    {K : ℝ} (hK : 0 < K) (hcompare : ∀ x, 1 + distFrom X.metric.form o x ≤ K * u x)
    (S : CanonicalSection X.manifold) (hS : IsHolomorphicCanonical S)
    (hgrowth : ∃ c : ℝ, ∀ x, Real.log (canonicalNormSq X.metric.form S x) ≤
      c * (1 + distFrom X.metric.form o x)) :
    ∃ a : ℝ, 0 < a ∧
      (∀ ε : ℝ, 0 < ε → ∀ x, Real.log (canonicalNormSq X.metric.form S x) -
        ε * u x ^ 2 - a * (1 + ε⁻¹) ≤ 0) ∧
      ∀ D : ℝ, 0 < D → ∀ ε : ℝ, 0 < ε → ε ≤ η / (D + 1) →
      ∀ x t, t ∈ Set.Icc 0 (D / 2) → 0 < canonicalNormSq X.metric.form S x →
        0 ≤ (D - t) * P x t + U x t -
          D * (Real.log (canonicalNormSq X.metric.form S x) - ε * u x ^ 2 -
            a * (1 + ε⁻¹)) + (n : ℝ) * t := by
  obtain ⟨c, hcgrowth⟩ := hgrowth
  obtain ⟨cΞ, hcΞgrowth⟩ := hΞgrowth
  have hc : 0 ≤ max c 0 := le_max_right _ _
  have hcΞ : 0 ≤ max cΞ 0 := le_max_right _ _
  have hd (x : Pt X) : 0 ≤ distFrom X.metric.form o x :=
    X.metric.induced_distance_nonneg o x
  have hcgrowth' (x : Pt X) : Real.log (canonicalNormSq X.metric.form S x) ≤
      max c 0 * (1 + distFrom X.metric.form o x) :=
    (hcgrowth x).trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (add_nonneg zero_le_one (hd x)))
  have hcΞgrowth' (x : Pt X) : Ξ x ≤
      max cΞ 0 * (1 + distFrom X.metric.form o x ^ ((3 : ℝ) / 2)) :=
    (hcΞgrowth x).trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (add_nonneg zero_le_one (Real.rpow_nonneg (hd x) _)))
  refine ⟨canonicalRegularizerShiftCoefficient (max c 0) K,
    canonicalRegularizerShiftCoefficient_pos _ _, ?_, ?_⟩
  · intro ε hε x
    exact canonical_log_uniform_shift X.metric S o u hc hε hcompare hcgrowth' x
  · intro D hD ε hε hεadm x t ht hqx
    let δmax := Real.exp (canonicalGrowthShift (max c 0) K ε -
      majorantGrowthShift (max cΞ 0) K ε)
    have hδmax : 0 < δmax := Real.exp_pos _
    apply canonical_comparison_limit X.metric S Ξ
      (canonicalRegularizerDeltaSeq_tendsto δmax) x hqx.ne'
    intro j
    have hδ := canonicalRegularizerDeltaSeq_pos hδmax j
    have hδsmall := canonicalRegularizerDeltaSeq_le hδmax.le j
    exact hcomparison D hD (canonicalRegularizer X.metric S Ξ
      (canonicalRegularizerDeltaSeq δmax j))
      (canonicalRegularizer_smooth X.metric S hS Ξ hΞ hδ)
      (canonicalRegularizer_levi_lower X.metric S hS Ξ hΞ hRic hδ)
      ε hε hεadm (canonicalRegularizerShiftCoefficient (max c 0) K * (1 + ε⁻¹))
      (canonical_regularizer_uniform_shift X.metric S Ξ u o hc hcΞ hK hε
        hcompare hcgrowth' hcΞgrowth' hδ hδsmall) x t ht

theorem canonical_rho_bound_of_smooth_comparison
    (X : KahlerManifold n) (o : Pt X) (u : Pt X → ℝ) (U P : STF X) (η : ℝ)
    (hcomparison : SmoothRicciWeightComparison X u U P η)
    (Ξ : Pt X → ℝ) (hΞ : SmoothFn Ξ)
    (hRic : ∀ x, HermLE (ricci X.metric.form x) (levi Ξ x))
    (hΞgrowth : ∃ cΞ : ℝ, ∀ x, Ξ x ≤ cΞ * (1 + distFrom X.metric.form o x ^ ((3 : ℝ) / 2)))
    {K : ℝ} (hK : 0 < K) (hcompare : ∀ x, 1 + distFrom X.metric.form o x ≤ K * u x)
    (hU : ∀ x t, 0 ≤ t → U x t ≤ 0) : CanonicalRhoPointBound X o u P η := by
  intro S hS hgrowth
  obtain ⟨a, ha, hsign, hsingular⟩ := canonical_comparison_of_smooth_comparison
    X o u U P η hcomparison Ξ hΞ hRic hΞgrowth hK hcompare S hS hgrowth
  refine ⟨a, ha, ?_⟩
  intro D hD ε hε hεadm x t ht hqx
  have hp := rho_bound_of_canonical_comparison hD ht (Nat.cast_nonneg n)
    (hU x t ht.1) (hsign ε hε x) (hsingular D hD ε hε hεadm x t ht hqx)
  have habs := neg_le_abs (Real.log (canonicalNormSq X.metric.form S x))
  linarith

end Yau.NodeProofs.F01Aux
