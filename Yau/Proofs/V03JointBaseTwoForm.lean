import Yau.Proofs.V03ChartKahlerTransport
import Yau.Proofs.V03JointBaseDifferential

/-! The genuine joint base area two-form is intrinsic and its expression
in every valid fixed chart uses the actual within base differential. -/

open scoped Manifold Topology ContDiff

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

variable {n : ℕ} {M : ComplexManifold n}
  {P : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P]

def jointBaseTwoForm (h : HermitianField M) (f : P → CotangentPoint M)
    (S : Set P) (p : P) : P [⋀^Fin 2]→L[ℝ] ℝ :=
  (chartKahlerTwoForm h (f p).1 (chartPt (f p).1 (f p).1)).compContinuousLinearMap
    ((fderivWithin ℂ (fun r => chartPt (f p).1 (f r).1) S p).restrictScalars ℝ)

theorem jointBaseTwoForm_J (h : HermitianField M) (f : P → CotangentPoint M)
    (S : Set P) (p u v : P) :
    jointBaseTwoForm h f S p ![Complex.I • u, Complex.I • v] = jointBaseTwoForm h f S p ![u, v] := by
  apply twoForm_complex_pullback_J
  exact chartKahlerTwoForm_J h (f p).1 (chartPt (f p).1 (f p).1)

theorem jointBaseTwoForm_eq_fixed_chart (h : HermitianField M)
    {f : P → CotangentPoint M} {S : Set P} (hf : CotangentHolomorphicOn f S)
    {p : P} (hp : p ∈ S) (hS : UniqueDiffWithinAt ℂ S p)
    (x : M.Carrier) (hx : f p ∈ cotangentSource x) :
    jointBaseTwoForm h f S p =
      (chartKahlerTwoForm h x (chartPt x (f p).1)).compContinuousLinearMap
        ((fderivWithin ℂ (fun r => chartPt x (f r).1) S p).restrictScalars ℝ) := by
  have hself : f p ∈ cotangentSource (f p).1 := mem_extChartAt_source _
  have hb : chartInv x (chartPt x (f p).1) = (f p).1 :=
    (extChartAt (ComplexModel n) x).left_inv hx
  have ht : chartPt x (f p).1 ∈ chartTarget x := (extChartAt (ComplexModel n) x).map_source hx
  have hΩ := chartKahlerTwoForm_chart_change h x (f p).1 ht (by rw [hb]; exact hself)
  rw [chartTransition_fderiv_eq_coordChange x (f p).1 ht, hb] at hΩ
  have hD := cotangentHolomorphicOn_fderivWithin_base_change hf hp hS x (f p).1 hx hself
  apply ContinuousAlternatingMap.ext
  intro v
  have hv : v = ![v 0, v 1] := by funext i; fin_cases i <;> rfl
  rw [hv, jointBaseTwoForm, twoForm_pullback_apply, hΩ, twoForm_pullback_apply, hD,
    twoForm_pullback_apply]
  rfl

end Yau.Blueprint.V03Proof
