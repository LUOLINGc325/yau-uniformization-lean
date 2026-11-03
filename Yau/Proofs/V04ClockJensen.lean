import Yau.Proofs.V04ClockWeightBounds

/-! The elementary logarithm inequality proves the normalization bounds
for the actual circle average, including a fixed-index lower normalizer. -/

open scoped Topology ContDiff
noncomputable section
namespace Yau.Blueprint.V04Proof
open Yau Yau.Blueprint Yau.Blueprint.V03Proof

variable {n q : ℕ} {X : KahlerManifold n}

theorem circleAverage_neg (f : ℝ → ℝ) :
    circleAverage (fun θ => -f θ) = -circleAverage f := by
  simpa only [neg_one_mul] using circleAverage_const_mul (-1) f

theorem clockWeight_average_log {d : VariationData X q} (hd : VariationSetup d)
    {k : ClockData X} (hk : ClockCutoffs d k) {j a : ℕ} {F : VariationDisc X}
    (hF : AdmissibleVariationDisc d j F) :
    circleAverage (fun θ => Real.log (clockWeight d k j a F θ)) =
      -circleAverage (fun θ => -Real.log (clockWeightRaw d k j a F θ)) -
      Real.log (circleAverage (clockWeightRaw d k j a F)) := by
  have hc := (clockWeightRaw_contDiff (a := a) hd hk hF).continuous
  have hp := clockWeightRaw_pos (k := k) (a := a) hd hF
  have hZ := clockWeightRaw_average_pos (a := a) hd hF hc
  have heq : (fun θ => Real.log (clockWeight d k j a F θ)) =
      fun θ => Real.log (clockWeightRaw d k j a F θ) +
        (-Real.log (circleAverage (clockWeightRaw d k j a F))) := by
    funext θ
    exact (Real.log_div (hp θ).ne' hZ.ne').trans (sub_eq_add_neg _ _)
  rw [heq, circleAverage_add_of_continuous (hc.log (fun θ => (hp θ).ne'))
    continuous_const, circleAverage_const_value, circleAverage_neg]
  ring

theorem clockWeight_average_log_nonpos {d : VariationData X q} (hd : VariationSetup d)
    {k : ClockData X} (hk : ClockCutoffs d k) {j a : ℕ} {F : VariationDisc X}
    (hF : AdmissibleVariationDisc d j F) :
    circleAverage (fun θ => Real.log (clockWeight d k j a F θ)) ≤ 0 := by
  have hc := (clockWeightRaw_contDiff (a := a) hd hk hF).continuous
  have hn := clockWeight_normalization (a := a) hd hF hc
  have hg : Continuous (clockWeight d k j a F) := hc.div_const _
  have hh := circleAverage_mono_of_continuous (hg.log (fun θ => (hn.1 θ).ne'))
    (hg.add continuous_const) (fun θ => Real.log_le_sub_one_of_pos (hn.1 θ))
  change circleAverage (fun θ => Real.log (clockWeight d k j a F θ)) ≤
    circleAverage (fun θ => clockWeight d k j a F θ + (-1)) at hh
  rw [circleAverage_add_of_continuous hg continuous_const,
    circleAverage_const_value, hn.2] at hh
  linarith only [hh]

theorem clockWeightRaw_average_le_one {d : VariationData X q} (hd : VariationSetup d)
    {k : ClockData X} (hk : ClockCutoffs d k)
    {j a : ℕ} {F : VariationDisc X} (hF : AdmissibleVariationDisc d j F) :
    circleAverage (clockWeightRaw d k j a F) ≤ 1 := by
  simpa only [circleAverage_const_value] using
    circleAverage_mono_of_continuous (clockWeightRaw_contDiff (a := a) hd hk hF).continuous
      continuous_const (clockWeightRaw_le_one hd hk hF)

theorem clockWeight_normalization_loss_bounds {d : VariationData X q} (hd : VariationSetup d)
    {k : ClockData X} (hk : ClockCutoffs d k)
    {j a : ℕ} {F : VariationDisc X} (hF : AdmissibleVariationDisc d j F) :
    (0 ≤ 1 - circleAverage (clockWeightRaw d k j a F) ∧
      1 - circleAverage (clockWeightRaw d k j a F) ≤
        circleAverage (fun θ => -Real.log (clockWeightRaw d k j a F θ))) ∧
    (-circleAverage (fun θ => -Real.log (clockWeightRaw d k j a F θ)) ≤
      circleAverage (fun θ => Real.log (clockWeight d k j a F θ)) ∧
      circleAverage (fun θ => Real.log (clockWeight d k j a F θ)) ≤ 0) := by
  have hraw := (clockWeightRaw_contDiff (a := a) hd hk hF).continuous
  have hp := clockWeightRaw_pos (k := k) (a := a) hd hF
  have hZ := clockWeightRaw_average_pos (a := a) hd hF hraw
  have hZ1 := clockWeightRaw_average_le_one (a := a) hd hk hF
  have hlogZ : Real.log (circleAverage (clockWeightRaw d k j a F)) ≤ 0 :=
    Real.log_nonpos hZ.le hZ1
  have heq := clockWeight_average_log (a := a) hd hk hF
  have hupper := clockWeight_average_log_nonpos (a := a) hd hk hF
  refine ⟨⟨sub_nonneg.mpr hZ1, ?_⟩, ⟨by linarith only [heq, hlogZ], hupper⟩⟩
  have hh := circleAverage_mono_of_continuous
    (continuous_const.add (hraw.neg)) ((hraw.log (fun θ => (hp θ).ne')).neg)
    (fun θ => show 1 + -clockWeightRaw d k j a F θ ≤
      -Real.log (clockWeightRaw d k j a F θ) by
        linarith only [Real.log_le_sub_one_of_pos (hp θ)])
  change circleAverage (fun θ => 1 + -clockWeightRaw d k j a F θ) ≤
    circleAverage (fun θ => -Real.log (clockWeightRaw d k j a F θ)) at hh
  rw [circleAverage_add_of_continuous (f := fun _ => (1 : ℝ))
    (g := fun θ => -clockWeightRaw d k j a F θ) continuous_const hraw.neg,
    circleAverage_const_value, circleAverage_neg] at hh
  linarith only [hh]

theorem clockWeightRaw_average_lower_of_loss {d : VariationData X q} (hd : VariationSetup d)
    {k : ClockData X} (hk : ClockCutoffs d k) {j a : ℕ} {F : VariationDisc X}
    (hF : AdmissibleVariationDisc d j F) {A : ℝ}
    (hA : circleAverage (fun θ => -Real.log (clockWeightRaw d k j a F θ)) ≤ A) :
    Real.exp (-A) ≤ circleAverage (clockWeightRaw d k j a F) := by
  have heq := clockWeight_average_log (a := a) hd hk hF
  have hnon := clockWeight_average_log_nonpos (a := a) hd hk hF
  have hZ := clockWeightRaw_average_pos (a := a) hd hF (clockWeightRaw_contDiff (a := a) hd hk hF).continuous
  calc
    Real.exp (-A) ≤ Real.exp (Real.log (circleAverage (clockWeightRaw d k j a F))) :=
      Real.exp_le_exp.mpr (by linarith only [heq, hnon, hA])
    _ = _ := Real.exp_log hZ

end Yau.Blueprint.V04Proof
