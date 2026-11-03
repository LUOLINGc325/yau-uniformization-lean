import Yau.Proofs.P06ExteriorHeatCutoff
import Yau.Proofs.P06ScalarUniquenessVolume
import Yau.Proofs.P06CutoffTailProjection

noncomputable section
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace ComplexOrder Matrix

namespace Yau.NodeProofs.P06Aux.ExteriorHeat
open Yau Yau.Blueprint Yau.LeafProofs L03
variable {n k : ℕ} {M : ComplexManifold n}

theorem cutoff_multiply_smooth (g : SmoothMetric M) (o : M.Carrier)
    (χ : ℕ → M.Carrier → ℝ) (hχ : MetricCutoffFamily g.form o χ)
    (A : RealForm M k) (hA : SmoothRealForm A) (j : ℕ) (hj : 1 ≤ j) :
    SmoothRealForm (multiplyRealForm (χ j) A) := by
  obtain ⟨c,hc,hcut⟩ := hχ
  exact smoothRealForm_multiply (χ j) A (hcut j hj).1 hA

theorem cutoff_multiply_compact (g : SmoothMetric M) (o : M.Carrier)
    (χ : ℕ → M.Carrier → ℝ) (hχ : MetricCutoffFamily g.form o χ)
    (A : RealForm M k) (j : ℕ) (hj : 1 ≤ j) :
    CompactlySupportedRealForm (multiplyRealForm (χ j) A) := by
  obtain ⟨c,hc,hcut⟩ := hχ
  exact compactlySupportedRealForm_multiply_scalar (χ j) (hcut j hj).2.1 A

def cutoffVector (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (o : M.Carrier)
    (χ : ℕ → M.Carrier → ℝ) (hχ : MetricCutoffFamily g.form o χ)
    (A : RealForm M k) (hA : SmoothRealForm A) (j : ℕ) (hj : 1 ≤ j) : L2FormHilbert g μ k :=
  realizeActualForm g μ (multiplyRealForm (χ j) A)
    (smooth_compactlySupported_l2RealForm g μ hμ _ (cutoff_multiply_smooth g o χ hχ A hA j hj)
      (cutoff_multiply_compact g o χ hχ A j hj))

def cutoffExteriorVector (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (o : M.Carrier)
    (χ : ℕ → M.Carrier → ℝ) (hχ : MetricCutoffFamily g.form o χ)
    (A : RealForm M k) (hA : SmoothRealForm A) (j : ℕ) (hj : 1 ≤ j) : L2FormHilbert g μ (k+1) :=
  realizeActualForm g μ (exteriorRealForm (multiplyRealForm (χ j) A))
    (exteriorRealForm_l2 g μ hμ _ (cutoff_multiply_smooth g o χ hχ A hA j hj)
      (cutoff_multiply_compact g o χ hχ A j hj))

/-- A single annular error has polynomial L² size, with no global L² datum. -/
theorem cutoffExteriorVector_polynomial_bound
    (g : SmoothMetric M) (hK : IsKahler g) (hRic : ∀ x, (ricci g.form x).PosSemidef)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ) (o : M.Carrier)
    (χ : ℕ → M.Carrier → ℝ) (hχ : MetricCutoffFamily g.form o χ)
    (A : RealForm M k) (hA : SmoothRealForm A) (hclosed : ClosedRealForm A)
    (B0 : ℝ) (hb : ∀ x, formNormSq g.form A x ≤ B0^2) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ j (hj : 1 ≤ j),
      ‖cutoffExteriorVector g μ hμ o χ hχ A hA j hj‖^2 ≤ K * (j : ℝ)^(2*n) := by
  obtain ⟨c,hc,hcut⟩ := hχ
  refine ⟨c^2 * B0^2 * 2^(2*n) * μ.real (distBall g.form o 1),by positivity,?_⟩
  intro j hj
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hjp : (0 : ℝ) < j := by linarith
  let E := exteriorRealForm (multiplyRealForm (χ j) A)
  have hsource (y : M.Carrier) : formNormSq g.form E y ≤ c^2 * B0^2 := by
    have he := cutoff_exterior_point_bound g o χ c hcut A hA hclosed B0 hb j hj y
    have hdiv : 0 ≤ c/(j:ℝ) := div_nonneg hc.le hjp.le
    have hdivle : c/(j:ℝ) ≤ c := (div_le_iff₀ hjp).mpr (by nlinarith)
    exact he.trans (mul_le_mul_of_nonneg_right (by nlinarith : (c/(j:ℝ))^2 ≤ c^2) (sq_nonneg B0))
  have hEq : (∫ y in distBall g.form o (2*j), formNormSq g.form E y ∂μ) =
      ∫ y, formNormSq g.form E y ∂μ := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro y hy
    have he : E y = 0 := by
      by_contra h
      exact hy (cutoff_exterior_support g o χ ⟨c,hc,hcut⟩ A hA j hj (subset_closure h))
    rw [formNormSq_congr_at g.form (A' := (0 : RealForm M (k+1))) he,formNormSq_zero]
    rfl
  have hnorm := norm_setIntegral_le_of_norm_le_const
    (distBall_measure_lt_top g μ hμ o (by positivity : 0 < 2*(j:ℝ)))
    (f := formNormSq g.form E) (C := c^2 * B0^2) (fun y _ => by
      rw [Real.norm_eq_abs,abs_of_nonneg (formNormSq_nonneg g.form E y)]
      exact hsource y)
  rw [hEq,Real.norm_eq_abs,abs_of_nonneg (integral_nonneg (fun y => formNormSq_nonneg g.form E y))] at hnorm
  have hvol := distBall_real_volume_polynomial g hK hRic μ hμ o
    (show (1:ℝ) ≤ 2*(j:ℝ) by linarith)
  change ‖realizeActualForm g μ E _‖^2 ≤ _
  rw [realizeActualForm_norm_sq]
  calc
    _ ≤ μ.real (distBall g.form o (2*j)) * (c^2 * B0^2) := by simpa only [mul_comm] using hnorm
    _ ≤ ((2*(j:ℝ))^(2*n) * μ.real (distBall g.form o 1)) * (c^2 * B0^2) :=
      mul_le_mul_of_nonneg_right hvol (by positivity)
    _ = _ := by rw [mul_pow]; ring

end Yau.NodeProofs.P06Aux.ExteriorHeat
