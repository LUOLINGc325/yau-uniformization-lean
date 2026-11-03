import Yau.Proofs.V03TraceDerivativeEvaluation

/-! Native real derivatives commute with bounded evaluation of actual
uniform and Hilbert traces. -/

open scoped Topology ContDiff lp

noncomputable section
namespace Yau.Blueprint.V03Proof

theorem fderiv_real_continuousMap_eval {K P F : Type*} [TopologicalSpace K] [CompactSpace K]
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {u : P → C(K, F)} {p : P} (hu : DifferentiableAt ℝ u p) (v : P) (k : K) :
    fderiv ℝ u p v k = fderiv ℝ (fun z => u z k) p v := by
  have hh := (ContinuousMap.evalCLM ℝ k).hasFDerivAt.comp p hu.hasFDerivAt
  exact (congrArg (fun A : P →L[ℝ] F => A v) hh.fderiv).symm

theorem fderiv_real_l2_eval {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {u : P → ℓ²(ℤ, ℂ)} {p : P} (hu : DifferentiableAt ℝ u p) (v : P) (k : ℤ) :
    fderiv ℝ u p v k = fderiv ℝ (fun z => u z k) p v := by
  have hh := ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 k).restrictScalars ℝ).hasFDerivAt.comp p hu.hasFDerivAt
  exact (congrArg (fun A : P →L[ℝ] ℂ => A v) hh.fderiv).symm

theorem fderiv_real_clm_apply {P E F : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {u : P → E →L[ℝ] F} {p : P} (hu : DifferentiableAt ℝ u p) (w : P) (v : E) :
    fderiv ℝ u p w v = fderiv ℝ (fun z => u z v) p w := by
  have hh := (ContinuousLinearMap.apply ℝ F v).hasFDerivAt.comp p hu.hasFDerivAt
  exact (congrArg (fun A : P →L[ℝ] F => A w) hh.fderiv).symm

end Yau.Blueprint.V03Proof
