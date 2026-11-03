import Yau.Proofs.V03ScalarLeviTwoForm
import Yau.Proofs.V03ExteriorCyclic

/-! The actual native real two-form of the scalar i∂∂bar calculator is
closed, by its genuine third derivative and native exterior differentiation. -/

open scoped Topology ContDiff
open Filter

noncomputable section
namespace Yau.Blueprint.V03Proof

theorem scalarLeviTwoForm_closed {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℝ E] {U : Set E} (hU : IsOpen U) {f : E → ℝ}
    (hf : ContDiffOn ℝ ∞ f U) {z : E} (hz : z ∈ U) :
    extDeriv (scalarLeviTwoForm f) z = 0 := by
  have hF : ContDiffAt ℝ ∞ f z := hf.contDiffAt (hU.mem_nhds hz)
  have hΩ : DifferentiableAt ℝ (scalarLeviTwoForm f) z :=
    ((scalarLeviTwoForm_contDiffOn hU hf).contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp)
  have heq (u v : E) : (fun p => scalarLeviTwoForm f p ![u, v]) =ᶠ[𝓝 z]
      (fun p => leviTwoForm f p u v) := by
    filter_upwards [hU.mem_nhds hz] with p hp
    exact scalarLeviTwoForm_apply ((hf.contDiffAt (hU.mem_nhds hp)).of_le (by simp)) u v
  apply ContinuousAlternatingMap.ext
  intro v
  change extDeriv (scalarLeviTwoForm f) z v = 0
  have hv : v = ![v 0, v 1, v 2] := by
    funext i
    fin_cases i <;> rfl
  rw [hv, extDeriv_twoForm_cyclic hΩ,
    (heq (v 1) (v 2)).fderiv_eq, (heq (v 2) (v 0)).fderiv_eq, (heq (v 0) (v 1)).fderiv_eq]
  exact leviTwoForm_closed (hF.of_le (by simp)) (v 0) (v 1) (v 2)

end Yau.Blueprint.V03Proof
