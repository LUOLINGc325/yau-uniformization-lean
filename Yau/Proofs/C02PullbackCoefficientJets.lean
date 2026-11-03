import Yau.Proofs.C02RealMetricCoefficientJets
import Yau.Proofs.C02HermitianRealPullback

/-! Derivative estimates for the original pullbackMat coefficients follow
from the actual physical real pullback field on the same open domain. -/

noncomputable section
open Set Filter
open scoped Manifold ContDiff Topology
namespace Yau.Blueprint.C02Proof
variable {n : ℕ} {M : ComplexManifold n}

theorem pullback_coefficient_jet_le_real_metric
    (h : HermitianField M) {Φ : ComplexVector n → M.Carrier}
    {O : Set (ComplexVector n)} (hO : IsOpen O)
    (hΦ : ∀ y ∈ O, MDifferentiableAt 𝓘(ℂ, ComplexVector n) (ComplexModel n) Φ y)
    {Q : ComplexVector n → ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ℝ}
    (hSmooth : ContDiffOn ℝ ∞ Q O)
    (hActual : ∀ y ∈ O, ∀ u v, Q y u v = realPullbackMetric h Φ y u v)
    {x : ComplexVector n} (hx : x ∈ O) (m : ℕ) (a b : Fin n) :
    ‖iteratedFDeriv ℝ m (fun y => pullbackMat h Φ y a b) x‖ ≤
      ‖iteratedFDeriv ℝ m Q x‖ := by
  have hEq : (fun y => pullbackMat h Φ y a b) =ᶠ[𝓝 x]
      (realMetricCoefficientEntry a b ∘ Q) := by
    filter_upwards [hO.mem_nhds hx] with y hy
    rw [pullbackMat_eq_real_metric_coefficients h (hΦ y hy)]
    change _ = realMetricCoefficientEntry a b (Q y)
    rw [realMetricCoefficientEntry_apply, hActual y hy, hActual y hy]
  rw [(hEq.iteratedFDeriv ℝ m).eq_of_nhds]
  exact realMetricCoefficientEntry_jet_le hO hSmooth hx m a b

end Yau.Blueprint.C02Proof
