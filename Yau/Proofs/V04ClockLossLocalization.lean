import Yau.Proofs.V04ClockLossLimits

/-! The three original normalization losses vanish in the original
sequence, penalty, and outer-index order. -/

open Filter
open scoped Topology ContDiff
noncomputable section
namespace Yau.Blueprint.V04Proof
open Yau Yau.Blueprint Yau.Blueprint.V03Proof

variable {n q : ℕ} {X : KahlerManifold n}

theorem localizedZero_of_eventually_abs_le {u v : ℕ → ℝ → ℕ → ℝ}
    (hv : LocalizedZero v)
    (h : ∀ᶠ j in atTop, ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ᶠ ν in atTop,
      |u j ε ν| ≤ |v j ε ν|) : LocalizedZero u := by
  intro r hr
  filter_upwards [hv r hr, h] with j hj hh
  filter_upwards [hj, hh] with ε hε hhε
  filter_upwards [hε, hhε] with ν hν hhν
  exact hhν.trans hν

theorem clockWeightRaw_average_loss_nonneg {d : VariationData X q} (hd : VariationSetup d)
    {k : ClockData X} (hk : ClockCutoffs d k) {j a : ℕ} {F : VariationDisc X}
    (hF : AdmissibleVariationDisc d j F) :
    0 ≤ circleAverage (fun θ => -Real.log (clockWeightRaw d k j a F θ)) := by
  apply circleAverage_nonneg
  intro θ
  exact neg_nonneg.mpr (Real.log_nonpos (clockWeightRaw_pos hd hF θ).le
    (clockWeightRaw_le_one hd hk hF θ))

theorem clockWeightRaw_loss_localized {d : VariationData X q} (hd : VariationSetup d)
    {k : ClockData X} (hk : ClockCutoffs d k) (hloc : LocalizationEstimates d)
    (a : ℕ) {F : ℕ → ℝ → ℕ → VariationDisc X} (hF : LocalizedMinimizers d F) :
    LocalizedZero (fun j ε ν =>
      circleAverage (fun θ => -Real.log (clockWeightRaw d k j a (F j ε ν) θ))) := by
  have hlocalized := hloc.2.2 F hF
  have hW := hlocalized.2.1
  obtain ⟨M, hM⟩ := hlocalized.2.2.2
  let M₀ := max M 0
  have hM₀ : 0 ≤ M₀ := le_max_right _ _
  let D : ℝ := 4 * a + 2
  have hD : 0 < D := by dsimp only [D]; positivity
  intro r hr
  let η := r / (2 * (M₀ + 1))
  have hη : 0 < η := div_pos hr (by positivity)
  have hb := (clockBaseLossCoefficient_tendsto k).eventually
    (Iio_mem_nhds (show (1 : ℝ) < 2 by norm_num))
  have hf := (clockFiberLossCoefficient_tendsto hd hk).eventually
    (Iio_mem_nhds hη)
  filter_upwards [hW (r / (2 * D)) (div_pos hr (by positivity)), hM, hF, hb, hf]
    with j hjW hjM hjF hjb hjf
  filter_upwards [hjW, hjM, hjF] with ε hεW hεM hεF
  filter_upwards [hεW, hεM] with ν hνW hνM
  have hA := hεF.1 ν
  have hnorm : 0 ≤ circleAverage (fun θ =>
      dualNorm (d.h (discTime (F j ε ν) (circlePoint θ)))
        ((F j ε ν).f (circlePoint θ)).1 ((F j ε ν).f (circlePoint θ)).2) :=
    circleAverage_nonneg (fun θ => dualNorm_nonneg _ _ _)
  have hwall := admissible_wallAverage_nonneg hd hA
  have hloss := clockWeightRaw_average_loss_le_refined (a := a) hd hk hA
  have hcoef := clockLoss_coefficients_nonneg hd hk j
  have hMbound : circleAverage (fun θ =>
      dualNorm (d.h (discTime (F j ε ν) (circlePoint θ)))
        ((F j ε ν).f (circlePoint θ)).1 ((F j ε ν).f (circlePoint θ)).2) ≤ M₀ :=
    hνM.trans (le_max_left _ _)
  have hwallbound := (le_abs_self _).trans hνW
  have hfiber : clockFiberLossCoefficient d k j * circleAverage (fun θ =>
      dualNorm (d.h (discTime (F j ε ν) (circlePoint θ)))
        ((F j ε ν).f (circlePoint θ)).1 ((F j ε ν).f (circlePoint θ)).2) ≤ r / 2 := by
    have hs := mul_le_mul hjf.le hMbound hnorm (by positivity : 0 ≤ η)
    have he : η * (M₀ + 1) = r / 2 := by dsimp only [η]; field_simp <;> ring
    nlinarith only [hs, he, hη]
  have hbase : (4 * (a : ℝ) + clockBaseLossCoefficient k j) *
      circleAverage (fun θ => wallCost d j ((F j ε ν).f (circlePoint θ))
        (discTime (F j ε ν) (circlePoint θ)) (F j ε ν).s) ≤ r / 2 := by
    have hs := mul_le_mul (show 4 * (a : ℝ) + clockBaseLossCoefficient k j ≤ D by
      dsimp only [D]; linarith only [hjb]) hwallbound hwall hD.le
    have he : D * (r / (2 * D)) = r / 2 := by field_simp <;> ring
    linarith only [hs, he]
  rw [abs_of_nonneg (clockWeightRaw_average_loss_nonneg hd hk hA)]
  linarith only [hloss, hfiber, hbase]

theorem clockNormalization_losses_localized {d : VariationData X q} (hd : VariationSetup d)
    {k : ClockData X} (hk : ClockCutoffs d k) (hloc : LocalizationEstimates d)
    (a : ℕ) {F : ℕ → ℝ → ℕ → VariationDisc X} (hF : LocalizedMinimizers d F) :
    LocalizedZero (fun j ε ν => circleAverage (clockWeightRaw d k j a (F j ε ν)) - 1) ∧
      LocalizedZero (fun j ε ν => circleAverage
        (fun θ => Real.log (clockWeight d k j a (F j ε ν) θ))) := by
  have hraw := clockWeightRaw_loss_localized hd hk hloc a hF
  have hpoint : ∀ᶠ j in atTop, ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ᶠ ν in atTop,
      |circleAverage (clockWeightRaw d k j a (F j ε ν)) - 1| ≤
        |circleAverage (fun θ => -Real.log (clockWeightRaw d k j a (F j ε ν) θ))| ∧
      |circleAverage (fun θ => Real.log (clockWeight d k j a (F j ε ν) θ))| ≤
        |circleAverage (fun θ => -Real.log (clockWeightRaw d k j a (F j ε ν) θ))| := by
    filter_upwards [hF] with j hj
    filter_upwards [hj] with ε hε
    apply Filter.Eventually.of_forall
    intro ν
    have hh := clockWeight_normalization_loss_bounds (a := a) hd hk (hε.1 ν)
    have hn := clockWeightRaw_average_loss_nonneg (a := a) hd hk (hε.1 ν)
    rw [abs_of_nonneg hn, abs_of_nonpos (by linarith only [hh.1.1]),
      abs_of_nonpos hh.2.2]
    constructor <;> linarith only [hh.1.2, hh.2.1]
  constructor
  · apply localizedZero_of_eventually_abs_le hraw
    filter_upwards [hpoint] with j hj
    filter_upwards [hj] with ε hε
    exact hε.mono (fun _ hν => hν.1)
  · apply localizedZero_of_eventually_abs_le hraw
    filter_upwards [hpoint] with j hj
    filter_upwards [hj] with ε hε
    exact hε.mono (fun _ hν => hν.2)

end Yau.Blueprint.V04Proof
