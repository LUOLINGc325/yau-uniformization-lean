import Yau.Proofs.V02DampingLoss
import Yau.Proofs.V03LogTrace
import Yau.Proofs.V03FourierMean

/-! Boundary damping errors are controlled by the unweighted mean loss.
The actual outer center is positive and at most one. -/

open scoped Topology ContDiff
open MeasureTheory

noncomputable section
namespace Yau.Blueprint.V02Proof
open Yau Yau.Blueprint V03Proof

theorem parameterAverage_mono {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    (hfg : ∀ θ, f θ ≤ g θ) : circleAverage f ≤ circleAverage g := by
  unfold circleAverage
  apply mul_le_mul_of_nonneg_left
    (intervalIntegral.integral_mono_on (by positivity : (0 : ℝ) ≤ 2 * Real.pi)
      (hf.intervalIntegrable _ _) (hg.intervalIntegrable _ _) (fun θ _ => hfg θ))
  positivity

theorem damped_boundary_average_loss {w B : ℝ → ℝ}
    (hw : Continuous w) (hB : Continuous B) {M η : ℝ} (hM : 0 ≤ M)
    (hw1 : ∀ θ, w θ ≤ 1) (hbound : ∀ θ, |B θ| ≤ M)
    (hloss : circleAverage (fun θ => 1 - w θ) ≤ η) :
    circleAverage (fun θ => w θ * B θ) - circleAverage B ≤ M * η := by
  rw [← parameterAverage_sub (f := fun θ => w θ * B θ) (g := B) (hw.mul hB) hB]
  have hp : ∀ θ, w θ * B θ - B θ ≤ M * (1 - w θ) := by
    intro θ
    have hb := (abs_le.mp (hbound θ)).1
    nlinarith [mul_nonneg (sub_nonneg.mpr (hw1 θ)) (by linarith : 0 ≤ B θ + M)]
  exact (parameterAverage_mono ((hw.mul hB).sub hB)
    (continuous_const.mul (continuous_const.sub hw)) hp).trans
      (by
        change circleAverage (fun θ => M * (1 - w θ)) ≤ M * η
        rw [parameterAverage_mul]
        exact mul_le_mul_of_nonneg_left hloss hM)

theorem outerCenter_pos_le_one {n q : ℕ} {X : KahlerManifold n}
    {d : VariationData X q} (hd : VariationSetup d) {j : ℕ}
    {F : VariationDisc X} (hF : AdmissibleVariationDisc d j F) (a : ℕ) :
    0 < outerCenter d j a F ∧ outerCenter d j a F ≤ 1 := by
  rw [outerCenter_eq_exp_logTrace]
  refine ⟨Real.exp_pos _, ?_⟩
  apply Real.exp_le_one_iff.mpr
  apply mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg a)
  have hh := parameterAverage_mono (admissible_logTrace_contDiff hd hF).continuous
    continuous_const (g := fun _ => (0 : ℝ)) (fun θ =>
      Real.log_nonpos (admissible_wallProduct_bounds hd hF θ).1.le
        (admissible_wallProduct_bounds hd hF θ).2)
  simpa only [parameterAverage_const] using hh

end Yau.Blueprint.V02Proof
