import Yau.Proofs.F01PotentialMetricAssembly

/-! The original native metric-potential identity passes to genuine
matrix and Levi limits along the same clock sequence. -/
noncomputable section
open Set Filter
open scoped Topology Matrix ComplexOrder Matrix.Norms.Frobenius
namespace Yau.NodeProofs.F01Aux
open Yau
variable {n : ℕ} {M : ComplexManifold n}

theorem native_potential_identity_of_actual_limits
    (g K : HermitianField M) (k : ℕ → HermitianField M)
    (v : ℕ → M.Carrier → ℝ) (u : M.Carrier → ℝ)
    (τ : ℕ → ℝ) (T : ℝ) (hτ : Tendsto τ atTop (𝓝 T))
    (hMetric : ∀ x, Tendsto (fun m => gMat (k m) x) atTop (𝓝 (gMat K x)))
    (hLevi : ∀ x, Tendsto (fun m => levi (v m) x) atTop (𝓝 (levi u x)))
    (hIdentity : ∀ m x,
      gMat (k m) x = gMat g x - (τ m : ℂ) • ricci g x + levi (v m) x) :
    ∀ x, gMat K x = gMat g x - (T : ℂ) • ricci g x + levi u x := by
  intro x
  have hClock : Tendsto (fun m => (τ m : ℂ)) atTop (𝓝 (T : ℂ)) :=
    Complex.continuous_ofReal.continuousAt.tendsto.comp hτ
  have hRight : Tendsto (fun m => gMat g x - (τ m : ℂ) • ricci g x + levi (v m) x) atTop
      (𝓝 (gMat g x - (T : ℂ) • ricci g x + levi u x)) :=
    (tendsto_const_nhds.sub (hClock.smul tendsto_const_nhds)).add (hLevi x)
  have hSeq : (fun m => gMat (k m) x) =
      (fun m => gMat g x - (τ m : ℂ) • ricci g x + levi (v m) x) := funext (fun m => hIdentity m x)
  exact tendsto_nhds_unique (hMetric x) (hSeq ▸ hRight)

end Yau.NodeProofs.F01Aux
