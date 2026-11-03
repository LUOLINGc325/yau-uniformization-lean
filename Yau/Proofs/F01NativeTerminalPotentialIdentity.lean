import Yau.Proofs.F01NativeLeviChartJetLimit
import Yau.Proofs.F01NativePotentialIdentityLimit

/-! Actual scaled spatial second-jet convergence identifies the
constructed terminal metric with the original terminal potential
formula in the canonical native frame. -/
noncomputable section
open Set Filter
open scoped ContDiff Manifold Topology Matrix ComplexOrder Matrix.Norms.Frobenius
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic Yau.LeafProofs.L17Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem native_terminal_potential_identity_of_chart_jets
    (g K : HermitianField M) (A : BoundedChartFamily g)
    (k : ℕ → HermitianField M) (v : ℕ → M.Carrier → ℝ) (u : M.Carrier → ℝ)
    (hv : ∀ m, SmoothFn (v m)) (hu : SmoothFn u)
    {σ : ℝ} (hσ : σ ≠ 0) (τ : ℕ → ℝ) (T : ℝ) (hτ : Tendsto τ atTop (𝓝 T))
    (hMetric : ∀ x, Tendsto (fun m => gMat (k m) x) atTop (𝓝 (gMat K x)))
    (hJets : ∀ a, Tendsto
      (fun m => iteratedFDeriv ℝ 2 (fun z => (σ ^ 2)⁻¹ * v m ((A.chart a) (σ • z))) 0)
      atTop (𝓝 (iteratedFDeriv ℝ 2 (fun z => (σ ^ 2)⁻¹ * u ((A.chart a) (σ • z))) 0)))
    (hIdentity : ∀ m x,
      gMat (k m) x = gMat g x - (τ m : ℂ) • ricci g x + levi (v m) x) :
    ∀ x, gMat K x = gMat g x - (T : ℂ) • ricci g x + levi u x := by
  apply native_potential_identity_of_actual_limits g K k v u τ T hτ hMetric
    (fun a => native_levi_limit_of_scaled_chart_second_jets g A v u hv hu hσ a (hJets a)) hIdentity

end Yau.NodeProofs.F01Aux
