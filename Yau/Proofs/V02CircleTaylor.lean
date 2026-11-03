import Yau.Proofs.V02CircleQuadratic
import Mathlib.Analysis.Calculus.Taylor

/-! The scalar circle Taylor estimate retains the literal nested mixed
Wirtinger derivative and the original cubic remainder. -/

open scoped Topology ContDiff
open MeasureTheory

noncomputable section
namespace Yau.Blueprint.V02Proof
open Yau Yau.Blueprint

theorem parameterAverage_abs_le {f : ℝ → ℝ} (hf : Continuous f)
    {M : ℝ} (hb : ∀ θ, |f θ| ≤ M) : |circleAverage f| ≤ M := by
  have hlow := circleAverage_lower_of_pointwise hf (fun θ => (abs_le.mp (hb θ)).1)
  have hnegc : Continuous (fun θ => -f θ) := hf.neg
  have hhigh := circleAverage_lower_of_pointwise hnegc
    (μ := -M) (fun θ => by have h := (abs_le.mp (hb θ)).2; linarith)
  have hn : circleAverage (fun θ => -f θ) = -circleAverage f := by
    unfold circleAverage
    rw [intervalIntegral.integral_neg]
    ring
  rw [hn] at hhigh
  exact abs_le.mpr ⟨hlow, by linarith⟩

theorem parameterCircleTaylor_of_pointwise {J : ℂ → ℝ}
    (hJ : ContDiffAt ℝ 2 J 0) {ρ C : ℝ}
    (hcont : Continuous (fun θ => J ((ρ : ℂ) * circlePoint θ)))
    (hrem : ∀ θ,
      |J ((ρ : ℂ) * circlePoint θ) - J 0 -
        fderiv ℝ J 0 ((ρ : ℂ) * circlePoint θ) - (1 / 2 : ℝ) *
        fderiv ℝ (fderiv ℝ J) 0 ((ρ : ℂ) * circlePoint θ) ((ρ : ℂ) * circlePoint θ)| ≤
          C * ρ ^ 3) :
    |circleAverage (fun θ => J ((ρ : ℂ) * circlePoint θ)) - J 0 -
      ρ ^ 2 * V03Proof.mixedReal J| ≤ C * ρ ^ 3 := by
  let T : ℝ → ℝ := fun θ => J 0 + fderiv ℝ J 0 ((ρ : ℂ) * circlePoint θ) +
    (1 / 2 : ℝ) * fderiv ℝ (fderiv ℝ J) 0
      ((ρ : ℂ) * circlePoint θ) ((ρ : ℂ) * circlePoint θ)
  have hT : Continuous T := by unfold T circlePoint; fun_prop
  have hbound : ∀ θ, |J ((ρ : ℂ) * circlePoint θ) - T θ| ≤ C * ρ ^ 3 := by
    intro θ
    convert hrem θ using 1
    congr 1
    unfold T
    ring
  have hAvg := parameterAverage_abs_le (hcont.sub hT) hbound
  change |circleAverage (fun θ => J ((ρ : ℂ) * circlePoint θ) - T θ)| ≤ C * ρ ^ 3 at hAvg
  rw [parameterAverage_sub hcont hT] at hAvg
  dsimp only [T] at hAvg
  rw [parameterCircle_secondTaylor_average hJ] at hAvg
  convert hAvg using 1
  congr 1
  ring

end Yau.Blueprint.V02Proof
