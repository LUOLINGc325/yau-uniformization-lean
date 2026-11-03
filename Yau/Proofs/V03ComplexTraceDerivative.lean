import Yau.Proofs.V03ContinuousMapDerivative
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars

/-! A genuinely real-differentiable uniform trace whose point evaluations
are holomorphic has a genuine complex derivative in the uniform norm. -/

open scoped Topology

noncomputable section
namespace Yau.Blueprint.V03Proof

variable {K F : Type*} [TopologicalSpace K] [CompactSpace K]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem differentiableAt_complex_trace {u : ℂ → C(K, F)} {p : ℂ}
    (hu : DifferentiableAt ℝ u p)
    (hc : ∀ k, DifferentiableAt ℂ (fun z => u z k) p) : DifferentiableAt ℂ u p := by
  let D := fderiv ℝ u p
  have heval (v : ℂ) (k : K) : D v k = fderiv ℂ (fun z => u z k) p v := by
    have h₁ := ((ContinuousMap.evalCLM ℂ k).restrictScalars ℝ).hasFDerivAt.comp p hu.hasFDerivAt
    have h₂ := (hc k).hasFDerivAt.restrictScalars ℝ
    have hh := congrArg (fun A : ℂ →L[ℝ] F => A v) (h₁.unique h₂)
    exact hh
  let L : ℂ →L[ℂ] C(K, F) := ContinuousLinearMap.toSpanSingleton ℂ (D 1)
  have hL : L.restrictScalars ℝ = D := by
    apply ContinuousLinearMap.ext
    intro v
    ext k
    change v • D 1 k = D v k
    rw [heval 1 k, heval v k]
    simpa only [smul_eq_mul, mul_one] using
      ((fderiv ℂ (fun z => u z k) p).map_smul v (1 : ℂ)).symm
  exact (hasFDerivAt_of_restrictScalars ℝ hu.hasFDerivAt hL).differentiableAt

end Yau.Blueprint.V03Proof
