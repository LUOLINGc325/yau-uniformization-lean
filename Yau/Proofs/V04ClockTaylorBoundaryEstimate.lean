import Yau.Proofs.V04ClockTaylorBoundary
import Yau.Proofs.V04ClockTaylorExpComposition

/-! The complete original boundary cost has a uniform backward Taylor
remainder; only the average of the singular walls is bounded. -/
open Set
open scoped Topology ContDiff
noncomputable section
namespace Yau.Blueprint.V04Proof.ClockTaylorAux
open Yau Yau.Blueprint Yau.Blueprint.V03Proof

variable {n q : ℕ} {X : KahlerManifold n}

theorem exp_backward_remainder {u : ℝ} (hu : u ∈ Icc (-1) 0) :
    |Real.exp u - 1 - u| ≤ u ^ 2 := by
  have hh := backward_taylor_bound (f := Real.exp) (f₁ := Real.exp) (f₂ := Real.exp)
    (r := 1) (M := 1) zero_lt_one zero_le_one
    (fun x hx => (Real.hasDerivAt_exp x).hasDerivWithinAt)
    (fun x hx => (Real.hasDerivAt_exp x).hasDerivWithinAt)
    (fun x hx => by rw [abs_of_pos (Real.exp_pos x)]; exact Real.exp_le_one_iff.mpr hx.2) hu
  simpa only [Real.exp_zero, mul_one, one_mul] using hh

theorem fixed_index_boundaryCost_taylor {d : VariationData X q} (hd : VariationSetup d)
    {k : ClockData X} (hk : ClockCutoffs d k) (j a : ℕ) {C M : ℝ}
    (hC : 0 ≤ C) (hM : 0 ≤ M) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ (F : VariationDisc X), AdmissibleVariationDisc d j F →
      boundaryCost d j F ≤ M → ∀ Γ : ℂ → ℂ, ClockLift d k j a F Γ →
      (∀ z ∈ Metric.closedBall (0 : ℂ) 1, 0 ≤ 1 + (Γ z).re) →
      (∀ θ, clockWeight d k j a F θ ≤ C) → ∀ u ∈ Icc (-1) 0,
      |boundaryCost d j (logBackwardClock F Γ u) - boundaryCost d j F -
        u * F.s * clockBoundaryCost d k j a F| ≤ R * u ^ 2 := by
  obtain ⟨K, hK, hbound⟩ := fixed_index_timeJet_bounds hd j
  have hT : 0 ≤ d.T := hd.1.le
  let R₀ := K * (d.T * C) ^ 2 + K * (d.T * C ^ 2)
  refine ⟨R₀ + d.T * M, by dsimp [R₀]; positivity, ?_⟩
  intro F hF hFM Γ hΓ hβ hγ u hu
  have hγ0 : ∀ θ, 0 ≤ clockWeight d k j a F θ := fun θ =>
    (clockWeight_normalization hd hF (clockWeightRaw_contDiff hd hk hF).continuous).1 θ |>.le
  let B (v θ : ℝ) := clockSmoothCost d j (F.f (circlePoint θ))
    (discTime (logBackwardClock F Γ v) (circlePoint θ))
  let D (θ : ℝ) := discTime F (circlePoint θ) * clockWeight d k j a F θ *
    clockTimeJet d j (F.f (circlePoint θ)) (discTime F (circlePoint θ))
  have hpoint (θ : ℝ) : |B u θ - B 0 θ - u * D θ| ≤ R₀ * u ^ 2 := by
    let y := F.f (circlePoint θ)
    let t := discTime F (circlePoint θ)
    let γ := clockWeight d k j a F θ
    have ht := admissible_discTime_mem hF (circlePoint_mem_closedBall θ)
    have hy : y ∈ boundaryCompact d j := by
      have hh := hF.2.2.2.2.2.2.2.1 θ
      exact ⟨hh.1.le, hh.2.le⟩
    have hh := exp_composition_taylor (f := clockSmoothCost d j y)
      (f₁ := clockTimeJet d j y) (f₂ := clockTimeJet₂ d j y)
      (r := 1) (M := K) (t := t) (T := d.T) (γ := γ) (C := C)
      zero_lt_one hK ht.1.le ht.2.le (hγ0 θ) (hγ θ) (fun v hv => ?_) hu
    · simpa only [B, D, logBackwardClock_boundary_time hΓ hF.2.2.2.1,
        zero_mul, Real.exp_zero, mul_one, R₀, t, γ, y] using hh
    · have hτ0 : 0 < t * Real.exp (v * γ) := mul_pos ht.1 (Real.exp_pos _)
      have hτT : t * Real.exp (v * γ) ≤ d.T :=
        (mul_le_of_le_one_right ht.1.le
          (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg hv.2 (hγ0 θ)))).trans ht.2.le
      exact ⟨clockSmoothCost_hasDerivAt hd j y ⟨hτ0, hτT.trans_lt hd.2.1⟩,
        clockTimeJet_hasDerivAt hd j y ⟨hτ0, hτT.trans_lt hd.2.1⟩,
        hbound y hy _ ⟨hτ0.le, hτT⟩⟩
  have hBu := (logBackwardClock_smoothCost_trace hd hF hΓ.1 hβ hu.2).continuous
  have hB0 := (logBackwardClock_smoothCost_trace hd hF hΓ.1 hβ (u := 0) le_rfl).continuous
  have hD : Continuous D :=
    (((admissible_discTime_trace_contDiff hF).continuous.mul
      ((clockWeightRaw_contDiff hd hk hF).continuous.div_const
        (circleAverage (clockWeightRaw d k j a F)))).mul
        (admissible_clockTimeJet_trace_contDiff hd hF).continuous)
  have havg := circleAverage_abs_le ((hBu.sub hB0).sub (continuous_const.mul hD)) hpoint
  change |circleAverage (fun θ => B u θ - B 0 θ - u * D θ)| ≤ R₀ * u ^ 2 at havg
  have hsub : Continuous (fun θ => B u θ - B 0 θ) := hBu.sub hB0
  have hscale : Continuous (fun θ => u * D θ) := continuous_const.mul hD
  rw [circleAverage_sub_of_continuous hsub hscale,
    circleAverage_sub_of_continuous (show Continuous (B u) from hBu)
      (show Continuous (B 0) from hB0), circleAverage_const_mul] at havg
  have hsplit := logBackwardClock_boundaryCost_split hd hF hΓ.1 hβ hu.2
  have hzero := logBackwardClock_boundaryCost_split hd hF hΓ.1 hβ (u := 0) le_rfl
  simp only [logBackwardClock_zero F Γ hF.2.2.2.1, Real.exp_zero, mul_one] at hzero
  have hder := clockBoundaryCost_jet_split (a := a) hd hk hF
  have hW := clockWallSum_average_le_boundaryCost hd hF
  have hWle := hW.2.trans hFM
  have heq : boundaryCost d j (logBackwardClock F Γ u) - boundaryCost d j F -
      u * F.s * clockBoundaryCost d k j a F =
      (circleAverage (B u) - circleAverage (B 0) - u * circleAverage D) +
        F.s * (Real.exp u - 1 - u) * circleAverage (clockWallSum d j F) := by
    rw [hsplit, hzero]
    have hz : B 0 = fun θ => clockSmoothCost d j (F.f (circlePoint θ)) (discTime F (circlePoint θ)) := by
      funext θ
      simp only [B, logBackwardClock_zero F Γ hF.2.2.2.1]
    rw [hz, show u * F.s * clockBoundaryCost d k j a F = u * (F.s * clockBoundaryCost d k j a F) by ring, hder]
    ring
  rw [heq]
  calc
    _ ≤ |circleAverage (B u) - circleAverage (B 0) - u * circleAverage D| +
        |F.s * (Real.exp u - 1 - u) * circleAverage (clockWallSum d j F)| := abs_add_le _ _
    _ ≤ R₀ * u ^ 2 + d.T * u ^ 2 * M := by
      apply add_le_add havg
      rw [abs_mul, abs_mul, abs_of_pos hF.2.2.2.1, abs_of_nonneg hW.1]
      exact mul_le_mul
        (mul_le_mul hF.2.2.2.2.1.le (exp_backward_remainder hu) (abs_nonneg _) hd.1.le)
        hWle hW.1 (by positivity)
    _ = _ := by ring

end Yau.Blueprint.V04Proof.ClockTaylorAux
