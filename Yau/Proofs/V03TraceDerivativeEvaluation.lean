import Yau.Proofs.V03ComplexTraceDerivative
import Mathlib.Analysis.Normed.Lp.lpSpace

/-! Evaluation commutes with genuine Fréchet derivatives of native
uniform and Hilbert traces. -/

open scoped Topology lp

noncomputable section
namespace Yau.Blueprint.V03Proof

theorem fderiv_continuousMap_eval {K P F : Type*} [TopologicalSpace K] [CompactSpace K]
    [NormedAddCommGroup P] [NormedSpace ℂ P]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    {u : P → C(K, F)} {p : P} (hu : DifferentiableAt ℂ u p) (v : P) (k : K) :
    fderiv ℂ u p v k = fderiv ℂ (fun z => u z k) p v := by
  have hh := (ContinuousMap.evalCLM ℂ k).hasFDerivAt.comp p hu.hasFDerivAt
  exact (congrArg (fun A : P →L[ℂ] F => A v) hh.fderiv).symm

theorem fderiv_l2_eval {P : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P]
    {u : P → ℓ²(ℤ, ℂ)} {p : P} (hu : DifferentiableAt ℂ u p) (v : P) (k : ℤ) :
    fderiv ℂ u p v k = fderiv ℂ (fun z => u z k) p v := by
  have hh := (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 k).hasFDerivAt.comp p hu.hasFDerivAt
  exact (congrArg (fun A : P →L[ℂ] ℂ => A v) hh.fderiv).symm

end Yau.Blueprint.V03Proof
