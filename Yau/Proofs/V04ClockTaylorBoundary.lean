import Yau.Proofs.V04ClockTaylorTimeJets
import Yau.Proofs.V04ClockTaylorEnergy

/-! Literal averages for the frozen backward clock, with no pointwise
bound on the reciprocal walls. -/
open Set MeasureTheory
open scoped Topology ContDiff
noncomputable section
namespace Yau.Blueprint.V04Proof.ClockTaylorAux
open Yau Yau.Blueprint Yau.Blueprint.V03Proof

variable {n q : ℕ} {X : KahlerManifold n}

theorem circleAverage_mono {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    (hle : ∀ θ, f θ ≤ g θ) : circleAverage f ≤ circleAverage g := by
  unfold circleAverage
  exact mul_le_mul_of_nonneg_left
    (intervalIntegral.integral_mono_on (by positivity : (0 : ℝ) ≤ 2 * Real.pi)
      (hf.intervalIntegrable _ _) (hg.intervalIntegrable _ _) (fun θ _ => hle θ)) (by positivity)

theorem circleAverage_abs_le {f : ℝ → ℝ} (hf : Continuous f) {M : ℝ}
    (hb : ∀ θ, |f θ| ≤ M) : |circleAverage f| ≤ M := by
  calc
    _ ≤ circleAverage (fun θ => |f θ|) := by
      unfold circleAverage
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (2 * Real.pi)⁻¹)]
      exact mul_le_mul_of_nonneg_left
        (intervalIntegral.abs_integral_le_integral_abs (by positivity : (0 : ℝ) ≤ 2 * Real.pi)) (by positivity)
    _ ≤ _ := circleAverage_le_of_continuous hf.abs hb

theorem circleAverage_sub_of_continuous {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) :
    circleAverage (fun θ => f θ - g θ) = circleAverage f - circleAverage g := by
  unfold circleAverage
  rw [intervalIntegral.integral_sub (hf.intervalIntegrable _ _) (hg.intervalIntegrable _ _)]
  ring

def clockWallSum (d : VariationData X q) (j : ℕ) (F : VariationDisc X) (θ : ℝ) : ℝ :=
  wallBase d j (F.f (circlePoint θ)).1 + wallFiber d j (F.f (circlePoint θ))

theorem admissible_clockWallSum_nonneg {d : VariationData X q} (hd : VariationSetup d)
    {j : ℕ} {F : VariationDisc X} (hF : AdmissibleVariationDisc d j F) (θ : ℝ) :
    0 ≤ clockWallSum d j F θ := by
  have hb := hF.2.2.2.2.2.2.2.1 θ
  exact add_nonneg (wallBase_nonneg (setup_wallProfiles hd) (deltaBase_pos (setup_wallProfiles hd) (setup_index_bounds hd j).1 hb.1))
    (wallFiber_nonneg (setup_wallProfiles hd) (deltaFiber_pos (setup_wallProfiles hd) (setup_index_bounds hd j).2 hb.2))

theorem clockWallSum_average_le_boundaryCost {d : VariationData X q} (hd : VariationSetup d)
    {j : ℕ} {F : VariationDisc X} (hF : AdmissibleVariationDisc d j F) :
    0 ≤ circleAverage (clockWallSum d j F) ∧
      circleAverage (clockWallSum d j F) ≤ boundaryCost d j F := by
  refine ⟨circleAverage_nonneg (admissible_clockWallSum_nonneg hd hF), ?_⟩
  apply circleAverage_mono (admissible_wallSum_trace_contDiff hd hF).continuous
    (admissible_boundaryDensity_circle_contDiff hd hF).continuous
  intro θ
  have ht := admissible_discTime_mem hF (circlePoint_mem_closedBall θ)
  have hN := dualNorm_nonneg (d.h (discTime F (circlePoint θ))) (F.f (circlePoint θ)).1 (F.f (circlePoint θ)).2
  have hB := baseCost_nonneg hd j (F.f (circlePoint θ)).1 ⟨ht.1.le, ht.2.le.trans hd.2.1.le⟩
  have hW := admissible_clockWallSum_nonneg hd hF θ
  have hs := hF.2.2.2.1
  change clockWallSum d j F θ ≤ _
  dsimp only [boundaryDensity, wallCost]
  change clockWallSum d j F θ ≤ _ + (_ + (1 + F.s) * clockWallSum d j F θ)
  nlinarith

theorem logBackwardClock_smoothCost_trace {d : VariationData X q} (hd : VariationSetup d)
    {j : ℕ} {F : VariationDisc X} (hF : AdmissibleVariationDisc d j F) {Γ : ℂ → ℂ}
    (hΓ : ContDiffOn ℂ ∞ Γ (Metric.closedBall (0 : ℂ) 1))
    (hβ : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, 0 ≤ 1 + (Γ z).re)
    {u : ℝ} (hu : u ≤ 0) :
    ContDiff ℝ ∞ (fun θ => clockSmoothCost d j (F.f (circlePoint θ))
      (discTime (logBackwardClock F Γ u) (circlePoint θ))) := by
  have hs := hF.2.2.2.1
  have hs' : 0 < F.s * Real.exp u := mul_pos hs (Real.exp_pos u)
  have hle : F.s * Real.exp u ≤ F.s :=
    mul_le_of_le_one_right hs.le (Real.exp_le_one_iff.mpr hu)
  have htime := backwardClock_discTime_le F Γ hs hs' hle hβ
  have hw : ContDiffOn ℂ ∞ (logBackwardClock F Γ u).w (Metric.closedBall (0 : ℂ) 1) := by
    rw [logBackwardClock_w F Γ hs]
    exact hF.2.1.add (contDiffOn_const.mul hΓ)
  apply closedDisc_real_trace_contDiff (f := fun ζ => clockSmoothCost d j (F.f ζ) (discTime (logBackwardClock F Γ u) ζ))
  exact cotangentDisc_scalarTime_contDiffOn (b := clockSmoothCost d j) (I := Icc 0 d.extendedT) hF.1 (discTime_contDiffOn hw)
    (fun ζ hζ => ⟨(discTime_pos hs' ζ).le,
      ((htime ζ hζ).trans_lt (hF.2.2.2.2.2.2.1 ζ hζ)).le.trans hd.2.1.le⟩)
    (boundarySmoothChartCost_contDiffOn hd j)

theorem logBackwardClock_boundaryCost_split {d : VariationData X q} (hd : VariationSetup d)
    {j : ℕ} {F : VariationDisc X} (hF : AdmissibleVariationDisc d j F) {Γ : ℂ → ℂ}
    (hΓ : ContDiffOn ℂ ∞ Γ (Metric.closedBall (0 : ℂ) 1))
    (hβ : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, 0 ≤ 1 + (Γ z).re)
    {u : ℝ} (hu : u ≤ 0) :
    boundaryCost d j (logBackwardClock F Γ u) =
      circleAverage (fun θ => clockSmoothCost d j (F.f (circlePoint θ))
        (discTime (logBackwardClock F Γ u) (circlePoint θ))) +
      (1 + F.s * Real.exp u) * circleAverage (clockWallSum d j F) := by
  have hc := (logBackwardClock_smoothCost_trace hd hF hΓ hβ hu).continuous
  have hw := (admissible_wallSum_trace_contDiff hd hF).continuous
  have hw' : Continuous (fun θ => (1 + F.s * Real.exp u) * clockWallSum d j F θ) :=
    continuous_const.mul hw
  have hh : circleAverage (fun θ => clockSmoothCost d j (F.f (circlePoint θ))
      (discTime (logBackwardClock F Γ u) (circlePoint θ)) +
      (1 + F.s * Real.exp u) * clockWallSum d j F θ) =
      circleAverage (fun θ => clockSmoothCost d j (F.f (circlePoint θ))
        (discTime (logBackwardClock F Γ u) (circlePoint θ))) +
      (1 + F.s * Real.exp u) * circleAverage (clockWallSum d j F) := by
    rw [circleAverage_add_of_continuous hc hw', circleAverage_const_mul]
  rw [← hh]
  apply congrArg circleAverage
  funext θ
  dsimp only [boundaryCost, wallCost, clockSmoothCost, logBackwardClock, backwardClock, clockWallSum]
  ring

theorem clockBoundaryCost_jet_split {d : VariationData X q} (hd : VariationSetup d)
    {k : ClockData X} (hk : ClockCutoffs d k) {j a : ℕ} {F : VariationDisc X}
    (hF : AdmissibleVariationDisc d j F) :
    F.s * clockBoundaryCost d k j a F =
      circleAverage (fun θ => discTime F (circlePoint θ) * clockWeight d k j a F θ *
        clockTimeJet d j (F.f (circlePoint θ)) (discTime F (circlePoint θ))) +
      F.s * circleAverage (clockWallSum d j F) := by
  unfold clockBoundaryCost
  have hγ : Continuous (clockWeight d k j a F) := (clockWeightRaw_contDiff hd hk hF).continuous.div_const _
  have hc : Continuous (fun θ => discTime F (circlePoint θ) * clockWeight d k j a F θ *
      clockTimeJet d j (F.f (circlePoint θ)) (discTime F (circlePoint θ))) :=
    ((admissible_discTime_trace_contDiff hF).continuous.mul hγ).mul
      (admissible_clockTimeJet_trace_contDiff hd hF).continuous
  have hw : Continuous (fun θ => F.s * clockWallSum d j F θ) :=
    continuous_const.mul (admissible_wallSum_trace_contDiff hd hF).continuous
  have hh : circleAverage (fun θ => discTime F (circlePoint θ) * clockWeight d k j a F θ *
      clockTimeJet d j (F.f (circlePoint θ)) (discTime F (circlePoint θ)) + F.s * clockWallSum d j F θ) =
      circleAverage (fun θ => discTime F (circlePoint θ) * clockWeight d k j a F θ *
        clockTimeJet d j (F.f (circlePoint θ)) (discTime F (circlePoint θ))) +
      F.s * circleAverage (clockWallSum d j F) := by
    rw [circleAverage_add_of_continuous hc hw, circleAverage_const_mul]
  rw [← hh, ← circleAverage_const_mul]
  apply congrArg circleAverage
  funext θ
  have ht := admissible_discTime_mem hF (circlePoint_mem_closedBall θ)
  rw [clockTimeJet_eq_original hd j _ ⟨ht.1, ht.2.trans hd.2.1⟩]
  dsimp only [clockWallSum]
  field_simp [hF.2.2.2.1.ne']
  <;> ring

end Yau.Blueprint.V04Proof.ClockTaylorAux
