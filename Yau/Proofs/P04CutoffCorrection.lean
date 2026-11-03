import Yau.Proofs.P04CanonicalCutoff
import Yau.Proofs.P04DbarDifference
import Yau.Proofs.P04HolomorphicRecovery

noncomputable section
open Set Filter MeasureTheory Bundle
open scoped Topology Manifold ContDiff ENNReal

namespace Yau.Proofs.P04Aux
open Yau Yau.LeafProofs BundleDbar
variable {n : ℕ} {M : ComplexManifold n}

theorem cutoffDbar_weightedL2 (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (Φ : M.Carrier → ℝ) (hΦ : SmoothFn Φ)
    (p : M.Carrier) {χ : ComplexVector n → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ chartTarget p) :
    WeightedL2 (r := 1) (CanonicalCoefficients M) g.form flatMetric μ Φ (cutoffDbar p χ) :=
  L14Aux.smooth_compact_weightedL2_one (CanonicalCoefficients M) g μ hμ flatMetric
    flatMetric_smooth Φ hΦ _ (cutoffDbar_smooth p hχ hc hs) (cutoffDbar_compact p hc hs)

/-- For a genuine finite-weight dbar correction, subtraction and the genuine
CR producer recover an actual global holomorphic canonical section. -/
theorem canonical_cutoff_correction_holomorphic (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (Φ : M.Carrier → ℝ) (hΦ : SmoothFn Φ)
    (p : M.Carrier) {χ : ComplexVector n → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ chartTarget p)
    (u : NQForm (CanonicalCoefficients M) 0)
    (hu : WeightedL2 (r := 1) (CanonicalCoefficients M) g.form flatMetric μ Φ u)
    (hd : WeakDbar (r := 1) (CanonicalCoefficients M) u (cutoffDbar p χ)) :
    ∃ S : CanonicalSection M, IsHolomorphicCanonical S ∧
      (∀ᵐ x ∂μ, u x=(cutoffTop p χ-canonicalToTop S) x) ∧
      (∫⁻ x, ENNReal.ofReal (canonicalNormSq g.form S x*Real.exp (-Φ x)) ∂μ) < ⊤ := by
  let s : L14Aux.WeightedTopSection (CanonicalCoefficients M) g μ hμ flatMetric flatMetric_smooth Φ hΦ :=
    ⟨cutoffTop p χ,cutoffTop_weightedL2 g μ hμ Φ hΦ p hχ hc hs⟩
  let v : L14Aux.WeightedTopSection (CanonicalCoefficients M) g μ hμ flatMetric flatMetric_smooth Φ hΦ := ⟨u,hu⟩
  let f : L14Aux.WeightedOneSection (CanonicalCoefficients M) g μ hμ flatMetric flatMetric_smooth Φ hΦ :=
    ⟨cutoffDbar p χ,cutoffDbar_weightedL2 g μ hμ Φ hΦ p hχ hc hs⟩
  have hw := canonicalDbar_difference g μ hμ Φ hΦ s v f (cutoff_weakDbar p hχ hc hs) hd
  obtain ⟨S,hS,hae,hfinite⟩ := canonical_holomorphic_weighted_representative g μ hμ Φ
    (s-v).1 (s-v).2 hw
  refine ⟨S,hS,?_,hfinite⟩
  filter_upwards [hae] with x hx
  change (cutoffTop p χ-u) x=canonicalToTop S x at hx
  have hx' : (cutoffTop p χ x).1-(u x).1=(canonicalToTop S x).1 := by
    simpa only [L14Aux.nqForm_sub_apply] using congrArg Subtype.val hx
  apply Subtype.ext
  rw [L14Aux.nqForm_sub_apply]
  apply eq_sub_iff_add_eq.mpr
  simpa only [add_comm] using (sub_eq_iff_eq_add.mp hx').symm

end Yau.Proofs.P04Aux
