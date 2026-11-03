import Yau.Proofs.V03GaussTwoFormTransport
import Yau.Proofs.V03JointCotangentDifferential

/-! The genuine joint Gauss two-form uses the original within derivative
and agrees with its expression in every valid fixed cotangent chart. -/

open scoped Manifold Topology ContDiff

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

variable {n q : ℕ} {M : ComplexManifold n}
  {P : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P]

def jointGaussTwoForm (G : CotangentPoint M → ComplexVector q)
    (f : P → CotangentPoint M) (S : Set P) (p : P) : P [⋀^Fin 2]→L[ℝ] ℝ :=
  (scalarLeviTwoForm (gaussPotential G (f p).1) (cotangentChart (f p).1 (f p))).compContinuousLinearMap
    ((fderivWithin ℂ (fun r => cotangentChart (f p).1 (f r)) S p).restrictScalars ℝ)

theorem jointGaussTwoForm_J {G : CotangentPoint M → ComplexVector q}
    (hG : CotangentImmersion G) (f : P → CotangentPoint M) (S : Set P) (p u v : P) :
    jointGaussTwoForm G f S p ![Complex.I • u, Complex.I • v] =
      jointGaussTwoForm G f S p ![u, v] := by
  apply twoForm_complex_pullback_J
  exact scalarLeviTwoForm_J
    ((gaussPotential_contDiffAt hG (f p).1
      (cotangentChart_mapsTo (f p).1 (mem_extChartAt_source _))).of_le (by simp))

theorem jointGaussTwoForm_eq_fixed_chart {G : CotangentPoint M → ComplexVector q}
    (hG : CotangentImmersion G) {f : P → CotangentPoint M} {S : Set P}
    (hf : CotangentHolomorphicOn f S) {p : P} (hp : p ∈ S)
    (hS : UniqueDiffWithinAt ℂ S p) (x : M.Carrier) (hx : f p ∈ cotangentSource x) :
    jointGaussTwoForm G f S p =
      (scalarLeviTwoForm (gaussPotential G x) (cotangentChart x (f p))).compContinuousLinearMap
        ((fderivWithin ℂ (fun r => cotangentChart x (f r)) S p).restrictScalars ℝ) := by
  have hself : f p ∈ cotangentSource (f p).1 := mem_extChartAt_source _
  have hbase : chartInv x (cotangentChart x (f p)).1 = (f p).1 :=
    (extChartAt (ComplexModel n) x).left_inv hx
  have hΩ := gaussTwoForm_chart_change hG x (f p).1
    (cotangentChart_mapsTo x hx) (by rw [hbase]; exact hself)
  rw [cotangentChart_left_inv x hx] at hΩ
  have hD := cotangentHolomorphicOn_fderivWithin_coords_change hf hp hS x (f p).1 hx hself
  apply ContinuousAlternatingMap.ext
  intro v
  have hv : v = ![v 0, v 1] := by funext i; fin_cases i <;> rfl
  rw [hv, jointGaussTwoForm, twoForm_pullback_apply, hΩ, twoForm_pullback_apply]
  rw [hD, twoForm_pullback_apply]
  rfl

end Yau.Blueprint.V03Proof
