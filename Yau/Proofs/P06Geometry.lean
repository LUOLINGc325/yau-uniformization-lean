import Yau.Proofs.G04

/-! The geometric part of P06, with the original fixed metric and form
calculators.  The heat construction is separate from these identities. -/

noncomputable section
open scoped Manifold Topology ContDiff Matrix ComplexOrder

namespace Yau.NodeProofs.P06Aux
open Yau Yau.Blueprint

variable {n : ℕ} {M : ComplexManifold n}

/-- The first four conclusions of the original smooth bounded Hodge target
are the already proved general Kähler normalization, specialized to X. -/
theorem hodgeGeometry (X : KahlerManifold n) :
    FormCalculusRealization X.metric.form ∧ HodgeNormalization X.metric.form ∧
      OneOneRepresentationBridge X.metric.form ∧ HodgeTraceDataBridge X.metric.form := by
  have h := G04_proved.2.1 n X.manifold X.metric.form
    (Yau.LeafProofs.L12Aux.metricSmooth_of_smoothMetric X.metric) X.kahler_metric
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩

/-- The paper curvature sign is supplied by the original manifold, including
zero directions, for which the normalized numerator is zero. -/
theorem nonnegativeHBC (X : KahlerManifold n) :
    ∀ x u v, 0 ≤ paperHolomorphicBisectionalCurvature X.metric.form x u v := by
  intro x u v
  have ht0 : tangentCoords x x (0 : TangentVector X.manifold x) = 0 := by
    unfold tangentCoords
    exact map_zero _
  apply div_nonneg
  · by_cases hu : u = 0
    · subst u
      simp [paperBisectionalNumerator, paperRm, ht0, realCoord]
    · by_cases hv : v = 0
      · subst v
        simp [paperBisectionalNumerator, paperComplexStructure, paperRm, ht0, realCoord]
      · exact (X.positive_bisectional_curvature x u v hu hv).le
  · exact mul_nonneg (mul_nonneg (by norm_num) (hermitianNormSq_nonneg _ _))
      (mul_nonneg (by norm_num) (hermitianNormSq_nonneg _ _))

/-- Metric-Lipschitz data are continuous in the existing manifold topology. -/
theorem continuous_of_metricLipschitz (g : SmoothMetric M) {f : M.Carrier → ℝ}
    (hf : LipschitzForMetric g.form f) : Continuous f := by
  obtain ⟨L, hL, hf⟩ := hf
  letI := Yau.LeafProofs.L12Aux.inducedMetricSpace g
  have hLip : LipschitzWith ⟨L, hL⟩ f := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    exact hf x y
  exact hLip.continuous

/-- The literal compact-exterior hypothesis produces a compactly supported
continuous difference from its value at infinity. -/
theorem compactExterior_difference (g : SmoothMetric M) {f : M.Carrier → ℝ}
    (hf : LipschitzForMetric g.form f) (hc : ConstantOutsideCompact f) :
    ∃ c : ℝ, Continuous (fun x => f x - c) ∧ HasCompactSupport (fun x => f x - c) := by
  obtain ⟨K, c, hK, hfc⟩ := hc
  refine ⟨c, (continuous_of_metricLipschitz g hf).sub continuous_const, ?_⟩
  apply hK.of_isClosed_subset isClosed_closure
  apply closure_minimal _ hK.isClosed
  intro x hx
  by_contra hxK
  exact hx (sub_eq_zero.mpr (hfc x hxK))

/-- In particular the data in the rough scalar clause have a genuine finite
global bound, before choosing an evolution. -/
theorem compactExterior_bounded (g : SmoothMetric M) {f : M.Carrier → ℝ}
    (hf : LipschitzForMetric g.form f) (hc : ConstantOutsideCompact f) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x, |f x| ≤ B := by
  obtain ⟨c, hcont, hcompact⟩ := compactExterior_difference g hf hc
  obtain ⟨B, hB⟩ := hcont.bounded_above_of_compact_support hcompact
  refine ⟨max B 0 + |c|, by positivity, ?_⟩
  intro x
  have hb : |f x - c| ≤ B := by simpa only [Real.norm_eq_abs] using hB x
  calc
    |f x| = |(f x - c) + c| := by rw [sub_add_cancel]
    _ ≤ |f x - c| + |c| := abs_add_le _ _
    _ ≤ max B 0 + |c| := add_le_add (hb.trans (le_max_left _ _)) le_rfl

end Yau.NodeProofs.P06Aux
