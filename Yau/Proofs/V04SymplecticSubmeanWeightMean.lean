import Yau.Proofs.V04SymplecticSubmeanWeights
import Yau.Proofs.V04SymplecticSubmeanMean

open scoped Topology ContDiff
open MeasureTheory Set
noncomputable section
namespace Yau.Blueprint.V04Proof.SymplecticSubmeanAux
open Yau Yau.Blueprint Yau.Blueprint.V03Proof

variable {n q : ℕ} {X : KahlerManifold n}

theorem average_add {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) :
    circleAverage (fun θ ↦ f θ + g θ) = circleAverage f + circleAverage g := by
  unfold circleAverage
  rw [intervalIntegral.integral_add (hf.intervalIntegrable _ _) (hg.intervalIntegrable _ _)]
  ring

theorem average_sub {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) :
    circleAverage (fun θ ↦ f θ - g θ) = circleAverage f - circleAverage g := by
  unfold circleAverage
  rw [intervalIntegral.integral_sub (hf.intervalIntegrable _ _) (hg.intervalIntegrable _ _)]
  ring

/-- The physical time contributes zero mean logarithm, and the original
wall power contributes exactly minus four times log outerCenter. -/
theorem average_log_submeanWeight {d : VariationData X q} (hd : VariationSetup d)
    {k : ClockData X} (hk : ClockCutoffs d k) {j a : ℕ} {F : VariationDisc X}
    (hF : AdmissibleVariationDisc d j F) :
    circleAverage (fun θ ↦ Real.log (submeanWeight d k j a F θ)) =
      circleAverage (fun θ ↦ Real.log (clockWeight d k j a F θ)) -
        4 * Real.log (outerCenter d j a F) := by
  obtain ⟨hγ, hγc, hγp⟩ := clock_weight_pos_smooth hd hk (a := a) hF
  have hm (θ : ℝ) := (admissible_wallPower_bounds hd hF a θ).1
  have hmc := real_closedDisc_trace_contDiff ((cotangentDisc_wallProduct_contDiffOn hd j hF.1).pow a)
  have hmLog : Continuous (fun θ ↦ Real.log (wallPower d j a (F.f (circlePoint θ)))) :=
    (hmc.log (fun θ ↦ (hm θ).ne')).continuous
  have hγLog : Continuous (fun θ ↦ Real.log (clockWeight d k j a F θ)) :=
    (hγc.log (fun θ ↦ (hγ θ).ne')).continuous
  have hre : Continuous (fun θ ↦ (F.w (circlePoint θ)).re) :=
    (real_closedDisc_trace_contDiff (Complex.reCLM.contDiff.comp_contDiffOn
      (hF.2.1.restrict_scalars ℝ))).continuous
  have hpoint (θ : ℝ) : Real.log (submeanWeight d k j a F θ) =
      2 * (F.w (circlePoint θ)).re + Real.log (clockWeight d k j a F θ) -
        4 * Real.log (wallPower d j a (F.f (circlePoint θ))) := by
    have ht : discTime F (circlePoint θ) / F.s = Real.exp (2 * (F.w (circlePoint θ)).re) := by
      unfold discTime
      field_simp [hF.2.2.2.1.ne']
    rw [submeanWeight, ht,
      Real.log_mul (mul_ne_zero (Real.exp_ne_zero _) (hγ θ).ne')
        (inv_ne_zero (pow_ne_zero 4 (hm θ).ne')),
      Real.log_mul (Real.exp_ne_zero _) (hγ θ).ne', Real.log_exp, Real.log_inv, Real.log_pow]
    ring
  rw [show (fun θ ↦ Real.log (submeanWeight d k j a F θ)) =
    (fun θ ↦ 2 * (F.w (circlePoint θ)).re + Real.log (clockWeight d k j a F θ) -
      4 * Real.log (wallPower d j a (F.f (circlePoint θ)))) from funext hpoint,
    average_sub (f := fun θ ↦ 2 * (F.w (circlePoint θ)).re + Real.log (clockWeight d k j a F θ))
      (g := fun θ ↦ 4 * Real.log (wallPower d j a (F.f (circlePoint θ))))
      ((hre.const_mul 2).add hγLog) (hmLog.const_mul 4),
    average_add (f := fun θ ↦ 2 * (F.w (circlePoint θ)).re)
      (g := fun θ ↦ Real.log (clockWeight d k j a F θ)) (hre.const_mul 2) hγLog,
    circleAverage_const_mul_value,
    circleAverage_const_mul_value, closedDisc_real_average hF.2.1, hF.2.2.1,
    Complex.zero_re, outerCenter, Real.log_exp]
  ring

/-- The constant in the frozen submean is the exact outer-factor center. -/
theorem exp_average_log_submeanWeight {d : VariationData X q} (hd : VariationSetup d)
    {k : ClockData X} (hk : ClockCutoffs d k) {j a : ℕ} {F : VariationDisc X}
    (hF : AdmissibleVariationDisc d j F) :
    Real.exp (circleAverage (fun θ ↦ Real.log (submeanWeight d k j a F θ))) =
      Real.exp (circleAverage (fun θ ↦ Real.log (clockWeight d k j a F θ))) *
        (outerCenter d j a F ^ 4)⁻¹ := by
  rw [average_log_submeanWeight hd hk hF, Real.exp_sub]
  have he : Real.exp (4 * Real.log (outerCenter d j a F)) = outerCenter d j a F ^ 4 := by
    rw [show (4 : ℝ) = (4 : ℕ) by norm_num, Real.exp_nat_mul,
      Real.exp_log (outerCenter_pos d j a F)]
  rw [he, div_eq_mul_inv]

end Yau.Blueprint.V04Proof.SymplecticSubmeanAux
