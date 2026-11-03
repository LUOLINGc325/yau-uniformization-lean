import Yau.Proofs.P04WeightedPoleNorm
import Yau.LeafProofs.L14TopChartApprox

noncomputable section
open Set Filter MeasureTheory Bundle
open scoped Topology Manifold ContDiff ENNReal

namespace Yau.Proofs.P04Aux
open Yau Yau.LeafProofs BundleDbar
variable {n : ℕ} {M : ComplexManifold n}

/-- The actual bounded multiplier on the common weighted Hilbert space
implements exactly the change to the genuine regularized weight. -/
theorem poleHilbertMultiplier_normSq (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (Φ : M.Carrier → ℝ) (hΦ : SmoothFn Φ)
    (P : M.Carrier → ℝ) (hP : SmoothFn P) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ x, Real.exp (-P x/2)^2 ≤ C ^ 2)
    (v : L14Aux.WeightedTopHilbert (CanonicalCoefficients M) g μ hμ flatMetric flatMetric_smooth Φ hΦ) :
    ENNReal.ofReal (‖L14Aux.weightedTopMultiplier (CanonicalCoefficients M) g μ hμ flatMetric
      flatMetric_smooth Φ hΦ (fun x => Real.exp (-P x/2)) (poleMultiplier_smooth hP) C hC hbound v‖^2) =
      weightedNormSq (r := 1) (CanonicalCoefficients M) g.form flatMetric μ (fun x => Φ x+P x)
        (L14Aux.weightedTopHilbertRepresentative (CanonicalCoefficients M) g μ hμ flatMetric
          flatMetric_smooth Φ hΦ v).1 := by
  let U := L14Aux.weightedTopHilbertRepresentative (CanonicalCoefficients M) g μ hμ flatMetric
    flatMetric_smooth Φ hΦ v
  have hrealize : L14Aux.realizeWeightedTopSection (CanonicalCoefficients M) g μ hμ flatMetric
      flatMetric_smooth Φ hΦ U=v :=
    L14Aux.weightedTopHilbertRepresentative_realize (CanonicalCoefficients M) g μ hμ flatMetric
      flatMetric_smooth Φ hΦ v
  have hT := L14Aux.weightedTopMultiplier_realize (CanonicalCoefficients M) g μ hμ flatMetric
    flatMetric_smooth Φ hΦ (fun x => Real.exp (-P x/2)) (poleMultiplier_smooth hP) C hC hbound U
  rw [hrealize] at hT
  rw [hT,L14Aux.realizeWeightedTopSection,UniformSpace.Completion.norm_coe,
    ← L14Aux.weightedTopSection_normSq_eq_ofReal]
  exact weightedNormSq_poleMultiplier g.form μ P Φ U.1

theorem exists_poleHilbertMultiplier (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (Φ : M.Carrier → ℝ) (hΦ : SmoothFn Φ)
    (P : M.Carrier → ℝ) (hP : SmoothFn P) (hc : HasCompactSupport P) :
    ∃ T : L14Aux.WeightedTopHilbert (CanonicalCoefficients M) g μ hμ flatMetric flatMetric_smooth Φ hΦ →L[ℂ]
        L14Aux.WeightedTopHilbert (CanonicalCoefficients M) g μ hμ flatMetric flatMetric_smooth Φ hΦ,
      ∀ v, ENNReal.ofReal (‖T v‖^2) =
        weightedNormSq (r := 1) (CanonicalCoefficients M) g.form flatMetric μ (fun x => Φ x+P x)
          (L14Aux.weightedTopHilbertRepresentative (CanonicalCoefficients M) g μ hμ flatMetric
            flatMetric_smooth Φ hΦ v).1 := by
  obtain ⟨C,hC,hbound⟩ := exists_bound_poleMultiplier hP hc
  have hsquare (x : M.Carrier) : Real.exp (-P x/2)^2 ≤ C ^ 2 := by
    have H := hbound x
    exact sq_le_sq.mpr (by simpa only [abs_of_pos hC] using H)
  exact ⟨L14Aux.weightedTopMultiplier (CanonicalCoefficients M) g μ hμ flatMetric flatMetric_smooth
    Φ hΦ (fun x => Real.exp (-P x/2)) (poleMultiplier_smooth hP) C hC.le hsquare,
    poleHilbertMultiplier_normSq g μ hμ Φ hΦ P hP C hC.le hsquare⟩

end Yau.Proofs.P04Aux
