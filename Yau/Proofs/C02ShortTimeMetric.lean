import Yau.Proofs.C02CompactCurvature
import Yau.Proofs.C02FlowTangentComparison
import Yau.Proofs.C02SmallTimeExponential

/-! A single short duration works on every late compact-centred cylinder.
The curvature control is obtained on the same original flow, and metric
monotonicity is used in its correct direction. -/

noncomputable section
open Set
namespace Yau.Blueprint.C02Proof
variable {n : ℕ} {X : KahlerManifold n}

theorem exists_uniform_short_time_metric_comparison
    (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hloc : LocalizedFlow X o h U P ρ) (hC01 : HarnackCompleteness X o h)
    (K : Set (Pt X)) (hK : IsCompact K) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ a : ℝ, 1 ≤ a → ∀ p ∈ K,
      ∀ b ∈ Icc a (a + δ), ∀ x : Pt X, distFrom (h a) p x ≤ 2 →
      ∀ v : TangentVector X.manifold x,
        hermitianNormSq (h a x) v ≤ (3 / 2 : ℝ) ^ 2 * hermitianNormSq (h b x) v := by
  obtain ⟨B, hB, hCurv⟩ := curvatureJetNorm_zero_bound_on_compact_centered_balls
    o h U P ρ hloc hC01 K hK 2 (by norm_num)
  obtain ⟨δ, hδ, hδone, hExp⟩ := exists_uniform_small_time_exponential
    ((2 * n : ℕ) * B) (mul_nonneg (Nat.cast_nonneg _) hB.le)
  refine ⟨δ, hδ, hδone, ?_⟩
  intro a ha p hp b hb x hx v
  have ha0 : 0 ≤ a := (by norm_num : (0 : ℝ) ≤ 1).trans ha
  have hCylinder (t : ℝ) (ht : t ∈ Icc a b) : curvatureJetNorm (h t) 0 x ≤ B := by
    have ht0 := ha0.trans ht.1
    have hDist : distFrom (h t) p x ≤ distFrom (h a) p x := by
      exact inducedDistance_le_of_gMat_order (h t) (h a)
        (metricFamilySmooth_slice hloc.1.2.1 ht0)
        (metricFamilySmooth_slice hloc.1.2.1 ha0)
        (fun y => hC01.2.2.2.2.2.1 y a t ha0 ht.1) p x
    exact hCurv t (ha.trans ht.1) p hp x (hDist.trans hx)
  have hCompare := kahlerRicciFlow_tangentNormSq_comparison
    X.metric.form h hloc.1 a b B ha0 hb.1 x v hCylinder
  have hBound := hExp (b - a) ⟨sub_nonneg.mpr hb.1, by linarith [hb.2]⟩
  exact hCompare.trans (mul_le_mul_of_nonneg_right hBound (hermitianNormSq_nonneg _ _))

end Yau.Blueprint.C02Proof
