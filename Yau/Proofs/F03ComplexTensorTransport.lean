import Yau.Proofs.F03ClassicalCaloricOperator

/-! The real inclusion preserves every actual finite derivative tensor norm. -/
noncomputable section
open Filter Set
open scoped Topology ContDiff
namespace Yau.Proofs.F03Aux
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

theorem norm_iteratedFDeriv_ofReal {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ ∞ u x) (m : ℕ) :
    ‖iteratedFDeriv ℝ m (fun y => (u y : ℂ)) x‖=‖iteratedFDeriv ℝ m u x‖ := by
  change ‖iteratedFDeriv ℝ m (Complex.ofRealCLM ∘ u) x‖=_
  rw [Complex.ofRealCLM.iteratedFDeriv_comp_left hu (by simp)]
  exact Complex.ofRealLI.norm_compContinuousMultilinearMap _

theorem secondFDeriv_ofReal {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (v w : E) :
    fderiv ℝ (fderiv ℝ (fun y => (u y : ℂ))) x v w=
      (fderiv ℝ (fderiv ℝ u) x v w : ℂ) := by
  have h := congrArg (fun A => A ![v,w])
    (Complex.ofRealCLM.iteratedFDeriv_comp_left hu (i := 2) (by norm_num))
  simpa only [Function.comp_def,Complex.ofRealCLM_apply,
    ContinuousLinearMap.compContinuousMultilinearMap_coe,
    iteratedFDeriv_two_apply,Matrix.cons_val_zero,Matrix.cons_val_one] using h

theorem fderiv_ofReal_apply {u : E → ℝ} {x : E}
    (hu : DifferentiableAt ℝ u x) (v : E) :
    fderiv ℝ (fun y => (u y : ℂ)) x v=(fderiv ℝ u x v : ℂ) := by
  exact congrArg (fun A => A v) ((Complex.ofRealCLM.hasFDerivAt.comp x hu.hasFDerivAt).fderiv)

end Yau.Proofs.F03Aux
