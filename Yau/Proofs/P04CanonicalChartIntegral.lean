import Yau.Proofs.P04LocalCanonicalRepresentative

noncomputable section
open Set MeasureTheory Bundle
open scoped Topology Manifold ContDiff ENNReal

namespace Yau.Proofs.P04Aux
open Yau Yau.LeafProofs
variable {n : ℕ} {M : ComplexManifold n}

theorem flat_chartTopCoefficientNormSq
    (u : BundleDbar.NQForm (CanonicalCoefficients M) 0) (a : M.Carrier) (z : ComplexVector n) :
    L14Aux.chartTopCoefficientNormSq (r := 1) (CanonicalCoefficients M) flatMetric u a z =
      ‖BundleDbar.coefficients (r := 1) (CanonicalCoefficients M) u a z Fin.elim0 0‖^2 := by
  simp only [L14Aux.chartTopCoefficientNormSq,flat_metricMatrix,Fintype.sum_unique,
    Matrix.one_apply,ite_true,mul_one]
  have hd : (default : Fin 1)=0 := Subsingleton.elim _ _
  rw [hd,← Complex.normSq_eq_norm_sq]
  simp [Complex.normSq_apply,Complex.mul_re,Complex.star_def,pow_two]

/-- Exact cancellation of the ACTUAL canonical density against the ACTUAL
Riemannian measure, retaining the factor 2^n. -/
theorem flat_weighted_top_chart_integral (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (φ : M.Carrier → ℝ) (hφ : SmoothFn φ)
    (u : BundleDbar.NQForm (CanonicalCoefficients M) 0)
    (hu : BundleDbar.LocallyL2 (r := 1) (CanonicalCoefficients M) u) (a : M.Carrier) :
    (∫⁻ x in (extChartAt (ComplexModel n) a).source,
      ENNReal.ofReal (BundleDbar.formNormSq (r := 1) (CanonicalCoefficients M) g.form flatMetric u x*
        Real.exp (-φ x)) ∂μ) =
      ENNReal.ofReal ((2 : ℝ)^n)*∫⁻ z in chartTarget a,
        ENNReal.ofReal (‖BundleDbar.coefficients (r := 1) (CanonicalCoefficients M) u a z Fin.elim0 0‖^2*
          Real.exp (-inChart a φ z)) ∂lebesgueC n := by
  have H := L14Aux.weighted_top_chart_integral (CanonicalCoefficients M) g μ hμ flatMetric
    flatMetric_smooth φ hφ u hu a
  simpa only [coefficient_bundleChartSource,coefficient_localDomain,flat_chartTopCoefficientNormSq,
    inChart] using H

theorem flat_weighted_top_chart_le (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (φ : M.Carrier → ℝ) (hφ : SmoothFn φ)
    (u : BundleDbar.NQForm (CanonicalCoefficients M) 0)
    (hu : BundleDbar.LocallyL2 (r := 1) (CanonicalCoefficients M) u) (a : M.Carrier) :
    (∫⁻ z in chartTarget a,
      ENNReal.ofReal (‖BundleDbar.coefficients (r := 1) (CanonicalCoefficients M) u a z Fin.elim0 0‖^2*
        Real.exp (-inChart a φ z)) ∂lebesgueC n) ≤
      BundleDbar.weightedNormSq (r := 1) (CanonicalCoefficients M) g.form flatMetric μ φ u := by
  have hTwo : (1 : ℝ≥0∞) ≤ ENNReal.ofReal ((2 : ℝ)^n) := by
    exact_mod_cast one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2) (n := n)
  calc
    _ ≤ ENNReal.ofReal ((2 : ℝ)^n)*∫⁻ z in chartTarget a,
        ENNReal.ofReal (‖BundleDbar.coefficients (r := 1) (CanonicalCoefficients M) u a z Fin.elim0 0‖^2*
          Real.exp (-inChart a φ z)) ∂lebesgueC n := by
      simpa only [one_mul] using mul_le_mul_left hTwo
        (∫⁻ z in chartTarget a, ENNReal.ofReal
          (‖BundleDbar.coefficients (r := 1) (CanonicalCoefficients M) u a z Fin.elim0 0‖^2*
            Real.exp (-inChart a φ z)) ∂lebesgueC n)
    _ = _ := (flat_weighted_top_chart_integral g μ hμ φ hφ u hu a).symm
    _ ≤ _ := setLIntegral_le_lintegral _ _

end Yau.Proofs.P04Aux
