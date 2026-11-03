import spec.CHAIN.CONTRACTS

/-! Spatial slice smoothness follows by restriction of the supplied
space-time metric coefficients; no complete slice metric is assumed. -/

noncomputable section
open Set
open scoped ContDiff
namespace Yau.Blueprint.C02Proof
variable {n : ℕ} {M : ComplexManifold n}

theorem metricFamilySmooth_slice
    {h : ℝ → HermitianField M} {I : Set ℝ}
    (hFamily : MetricFamilySmooth h I) {t : ℝ} (ht : t ∈ I) : MetricSmooth (h t) := by
  intro x a b
  have hJoint : ContDiffOn ℝ ∞
      (fun p : ComplexVector n × ℝ => realMetricFn (h p.2) x p.1 a b)
      (chartTarget x ×ˢ I) := hFamily x a b
  have hSlice : ContDiff ℝ ∞ (fun z : ComplexVector n => (z, t)) := by fun_prop
  exact hJoint.comp hSlice.contDiffOn (fun z hz => ⟨hz, ht⟩)

end Yau.Blueprint.C02Proof
