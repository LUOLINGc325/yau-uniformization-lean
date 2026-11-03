import Yau.Proofs.V03FixedDiscWalls
import Yau.Proofs.V03TimeScalars
import Yau.Proofs.V03LogTrace

/-! The actual base localization cost tends uniformly to zero on any fixed
smooth disc with its original clock. -/

open scoped Manifold Topology ContDiff Matrix ComplexOrder
open Filter MeasureTheory

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

variable {n q : ℕ} {X : KahlerManifold n}

theorem circleAverage_const_value (c : ℝ) : circleAverage (fun _ => c) = c := by
  unfold circleAverage
  rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul]
  have hp : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  rw [← mul_assoc, inv_mul_cancel₀ hp, one_mul]

theorem circleAverage_le_of_le {f : ℝ → ℝ} (hf : Continuous f) {c : ℝ}
    (hfc : ∀ θ, f θ ≤ c) : circleAverage f ≤ c := by
  rw [← circleAverage_const_value c]
  apply mul_le_mul_of_nonneg_left
    (intervalIntegral.integral_mono_on (by positivity : (0 : ℝ) ≤ 2 * Real.pi)
      (hf.intervalIntegrable _ _) intervalIntegrable_const (fun θ _ => hfc θ))
  positivity

theorem fixedDisc_baseCost_small {d : VariationData X q} (hd : VariationSetup d)
    (F : VariationDisc X) (hf : CotangentDisc F.f)
    (hw : ContDiffOn ℂ ∞ F.w (Metric.closedBall 0 1)) (hs : 0 < F.s)
    (ht : ∀ ζ ∈ Metric.closedBall (0 : ℂ) 1, discTime F ζ < d.T)
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ j in atTop, ∀ ζ ∈ Metric.closedBall (0 : ℂ) 1,
      baseCost d j (F.f ζ).1 (discTime F ζ) ≤ η := by
  have hI : Set.MapsTo (discTime F) (Metric.closedBall 0 1) (Set.Icc 0 d.extendedT) := by
    intro ζ hζ
    exact ⟨(discTime_pos hs ζ).le, (ht ζ hζ).le.trans hd.2.1.le⟩
  have hQ := cotangentDisc_smoothSpaceTime_contDiffOn hd.2.2.2.2.2.2.2.2.1.1 hf
    (discTime_contDiffOn hw) hI
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) 1).bddAbove_image hQ.continuousOn
  let C := |M| + 1
  have hrecip : Tendsto (fun j : ℕ => (((j + 1 : ℕ) : ℝ)⁻¹ * C)) atTop (𝓝 0) := by
    simpa only [Nat.cast_add, Nat.cast_one, one_div, zero_mul] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).mul_const C
  have hrec := hrecip.eventually (Iio_mem_nhds (half_pos hη))
  let K := (fun ζ => (F.f ζ).1) '' Metric.closedBall (0 : ℂ) 1
  have hK : IsCompact K := (isCompact_closedBall (0 : ℂ) 1).image_of_continuousOn hf.1.continuousOn
  have htail := hd.2.2.2.2.2.2.2.2.2.2.1 K hK (η / 2) (half_pos hη)
  filter_upwards [hrec, htail] with j hj htail ζ hζ
  have hQbd : d.Q (F.f ζ).1 (discTime F ζ) ≤ C :=
    (hM ⟨ζ, hζ, rfl⟩).trans (by dsimp [C]; linarith [le_abs_self M])
  have hρbd := htail (F.f ζ).1 ⟨ζ, hζ, rfl⟩ (discTime F ζ) (hI hζ)
  have hmul := mul_le_mul_of_nonneg_left hQbd (show 0 ≤ (((j + 1 : ℕ) : ℝ)⁻¹) by positivity)
  dsimp only [baseCost]
  linarith

theorem fixedDisc_admissible_eventually {d : VariationData X q} (hd : VariationSetup d)
    (F : VariationDisc X) (hf : CotangentDisc F.f)
    (hw : ContDiffOn ℂ ∞ F.w (Metric.closedBall 0 1)) (hw0 : F.w 0 = 0)
    (hs : 0 < F.s) (hsT : F.s < d.T)
    (hc : InCotangentTimeChart d.chart (F.f 0) F.s (centerCylinder d))
    (ht : ∀ ζ ∈ Metric.closedBall (0 : ℂ) 1, discTime F ζ < d.T) :
    ∀ᶠ j in atTop, AdmissibleVariationDisc d j F := by
  filter_upwards [fixedDisc_cutoff_plateaus hd hf, fixedDisc_energy_finite_eventually hd F hf hw]
    with j hj he
  exact ⟨hf, hw, hw0, hs, hsT, hc, ht,
    fun θ => cutoff_plateaus_mem_boundaryRegion hd (hj _ (circlePoint_mem_closedBall θ)), he⟩

end Yau.Blueprint.V03Proof
