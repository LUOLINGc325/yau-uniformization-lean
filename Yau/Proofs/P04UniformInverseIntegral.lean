import Yau.Proofs.P04CompactInverseBound
import Yau.Proofs.P04PoleDensityBound
import Yau.Proofs.P04PoleCurvatureEnergy

noncomputable section
open Set Filter MeasureTheory
open scoped Topology Manifold ContDiff Matrix ComplexOrder ENNReal

namespace Yau.Proofs.P04Aux
open Yau Yau.LeafProofs BundleDbar
variable {n : ℕ} {M : ComplexManifold n}

/-- The inverse-curvature integral of the ACTUAL compact source has one
finite bound for every regularization. Only compact local bounds are used. -/
theorem exists_uniform_pole_inverse_integral_bound (g : SmoothMetric M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ) (p : M.Carrier)
    {χ : ComplexVector n → ℝ} (hχ : ContDiff ℝ ∞ χ) (c k : ℝ)
    {ψ : M.Carrier → ℝ} (hψ : IsSmoothStrictPsh ψ) {ρ : ℝ} (hρ : 0 < ρ)
    (hs : poleAnnulus (chartPt p p) ρ ⊆ chartTarget p)
    (f : NQForm (CanonicalCoefficients M) 1) (hf : SmoothForm (r := 1) (CanonicalCoefficients M) f)
    (hK : IsCompact (closure {x | f x ≠ (0 : NQForm (CanonicalCoefficients M) 1) x}))
    (hsupport : ∀ x ∈ closure {x | f x ≠ (0 : NQForm (CanonicalCoefficients M) 1) x},
      x ∈ (extChartAt (ComplexModel n) p).source ∧ chartPt p x ∈ poleAnnulus (chartPt p p) ρ)
    (hN : ∀ ε : ℝ, 0 < ε → ε ≤ ρ → WeightedNakanoNonnegative (r := 1)
      (CanonicalCoefficients M) flatMetric (regularizedPoleWeight p χ c k ψ ε))
    (horder : ∀ ε : ℝ, 0 < ε → ε ≤ ρ → ∀ x,
      (levi (regularizedPoleWeight p χ c k ψ ε) x-levi ψ x).PosSemidef) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ρ →
      inverseCurvatureIntegral (r := 1) (CanonicalCoefficients M) g.form flatMetric μ
        (regularizedPoleWeight p χ c k ψ ε) f ≤ ENNReal.ofReal B := by
  classical
  let K := closure {x | f x ≠ (0 : NQForm (CanonicalCoefficients M) 1) x}
  letI : IsLocallyFiniteMeasure μ := L18Aux.riemannianVolume_locallyFinite g μ hμ
  have hμK : μ K < ⊤ := hK.measure_lt_top
  obtain ⟨C,hC,hCbound⟩ := compact_flat_inverseCurvature_bound g p hψ f hf
    (poleAnnulus_isCompact (chartPt p p) ρ) hs
  obtain ⟨D,hD,hDbound⟩ := pole_annulus_density_uniform_bound p hχ c k hψ.1 hρ hs
  let B := (C*D)*(μ K).toReal
  refine ⟨B,mul_nonneg (mul_nonneg hC hD) ENNReal.toReal_nonneg,fun ε hε hερ => ?_⟩
  have hpoint (x : M.Carrier) :
      inverseCurvatureNormSq (r := 1) (CanonicalCoefficients M) g.form flatMetric
          (regularizedPoleWeight p χ c k ψ ε) f x *
        ENNReal.ofReal (Real.exp (-regularizedPoleWeight p χ c k ψ ε x)) ≤
      K.indicator (fun _ => ENNReal.ofReal (C*D)) x := by
    by_cases hx : x ∈ K
    · obtain ⟨hxs,hxz⟩ := hsupport x hx
      have hi : chartInv p (chartPt p x)=x := (extChartAt (ComplexModel n) p).left_inv hxs
      have hinverse : inverseCurvatureNormSq (r := 1) (CanonicalCoefficients M) g.form flatMetric
          (regularizedPoleWeight p χ c k ψ ε) f x ≤ ENNReal.ofReal C := by
        apply (flat_inverseCurvatureNormSq_antitone g.form _ ψ f x (horder ε hε hερ x)).trans
        simpa only [hi] using hCbound (chartPt p x) hxz
      have hdensity : Real.exp (-regularizedPoleWeight p χ c k ψ ε x) ≤ D := by
        have H := regularizedPoleWeight_inChart p χ c k ψ ε (hs hxz)
        change regularizedPoleWeight p χ c k ψ ε (chartInv p (chartPt p x))=_ at H
        rw [hi] at H
        rw [H]
        exact hDbound ε ⟨hε.le,hερ⟩ (chartPt p x) hxz
      rw [Set.indicator_of_mem hx,ENNReal.ofReal_mul hC]
      exact mul_le_mul' hinverse (ENNReal.ofReal_le_ofReal hdensity)
    · have hfzero : f x=(0 : NQForm (CanonicalCoefficients M) 1) x := by
        by_contra hne
        exact hx (subset_closure hne)
      rw [flat_inverseCurvatureNormSq_zero g.form _ (hN ε hε hερ) f x hfzero,
        zero_mul,Set.indicator_of_notMem hx]
  calc
    _ ≤ ∫⁻ x, K.indicator (fun _ => ENNReal.ofReal (C*D)) x ∂μ := lintegral_mono hpoint
    _ = ENNReal.ofReal (C*D)*μ K := lintegral_indicator_const hK.isClosed.measurableSet _
    _ = ENNReal.ofReal B := by
      rw [ENNReal.ofReal_mul (mul_nonneg hC hD),ENNReal.ofReal_toReal hμK.ne]

end Yau.Proofs.P04Aux
