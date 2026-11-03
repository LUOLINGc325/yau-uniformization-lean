import spec.CHAIN.CONTRACTS

/-! Integration and the canonical currying isometries, isolated to keep
operator-space instance inference small in the parameter-integral proof. -/
open MeasureTheory
open scoped Interval
noncomputable section
namespace Yau.NodeProofs.F01Aux
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

theorem norm_curryLeft_eq (m : ℕ) (p : E [×m + 1]→L[ℝ] F) :
    ‖p.curryLeft‖ = ‖p‖ :=
  (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) => E) F).norm_map p

theorem intervalIntegral_curryLeft (m : ℕ) {p : ℝ → E [×m + 1]→L[ℝ] F}
    (hp : IntervalIntegrable p volume 0 1) :
    (∫ t in (0 : ℝ)..1, (p t).curryLeft) = (∫ t in (0 : ℝ)..1, p t).curryLeft := by
  let C := (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) => E) F).toContinuousLinearEquiv.toContinuousLinearMap
  exact ContinuousLinearMap.intervalIntegral_comp_comm (𝕜 := ℝ)
    (E := E [×m + 1]→L[ℝ] F) (F := E →L[ℝ] (E [×m]→L[ℝ] F)) C hp

theorem intervalIntegral_curryZero {p : ℝ → E [×0]→L[ℝ] F}
    (hp : IntervalIntegrable p volume 0 1) :
    (∫ t in (0 : ℝ)..1, (p t).curry0) = (∫ t in (0 : ℝ)..1, p t).curry0 := by
  exact ContinuousLinearMap.intervalIntegral_comp_comm (𝕜 := ℝ)
    (continuousMultilinearCurryFin0 ℝ E F).toContinuousLinearEquiv.toContinuousLinearMap hp

end Yau.NodeProofs.F01Aux
