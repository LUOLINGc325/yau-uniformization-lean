import Yau.Proofs.P03CirclePhase

open scoped Topology
open MeasureTheory

noncomputable section

namespace Yau.NodeProofs.P03Aux

variable {n : ℕ}

def circleKernelIntegrand (k : ComplexVector n → ℝ) (h : ComplexVector n → ℂ)
    (x : ComplexVector n) (p : ℝ × ComplexVector n) : ℂ :=
  k p.2 • h (x - circleMap 0 1 p.1 • p.2)

theorem circleKernelIntegrand_continuous {k : ComplexVector n → ℝ}
    {h : ComplexVector n → ℂ} (hk : Continuous k) (hc : Continuous h)
    (x : ComplexVector n) : Continuous (circleKernelIntegrand k h x) := by
  have harg : Continuous (fun p : ℝ × ComplexVector n => x - circleMap 0 1 p.1 • p.2) :=
    continuous_const.sub (((continuous_circleMap 0 1).comp continuous_fst).smul continuous_snd)
  exact (hk.comp continuous_snd).smul (hc.comp harg)

/-- The circle/Fubini interchange has an explicit L¹ majorant. Only values
of h on the compact ball meeting the actual kernel support are bounded. -/
theorem circleKernelIntegrand_integrable {k : ComplexVector n → ℝ}
    {h : ComplexVector n → ℂ} {r : ℝ} (hk : Continuous k) (hkc : HasCompactSupport k)
    (hks : tsupport k ⊆ Metric.closedBall 0 r) (hc : Continuous h)
    (x : ComplexVector n) :
    Integrable (circleKernelIntegrand k h x)
      (((volume : Measure ℝ).restrict (Set.Ioc 0 (2 * Real.pi))).prod volume) := by
  obtain ⟨B, hB⟩ := ((isCompact_closedBall x r).image hc).isBounded.exists_norm_le
  let C := max B 0
  have hbound {y : ComplexVector n} (hy : y ∈ Metric.closedBall x r) : ‖h y‖ ≤ C :=
    (hB _ (Set.mem_image_of_mem h hy)).trans (le_max_left _ _)
  letI : IsFiniteMeasure ((volume : Measure ℝ).restrict (Set.Ioc 0 (2 * Real.pi))) :=
    ⟨by
      rw [Measure.restrict_apply_univ, Real.volume_Ioc]
      exact ENNReal.ofReal_lt_top⟩
  have hconst : Integrable (fun _ : ℝ => C)
      ((volume : Measure ℝ).restrict (Set.Ioc 0 (2 * Real.pi))) := integrable_const C
  have hki : Integrable k volume := hk.integrable_of_hasCompactSupport hkc
  have hmajorant := hconst.mul_prod hki.norm
  apply hmajorant.mono' (circleKernelIntegrand_continuous hk hc x).aestronglyMeasurable
  filter_upwards with p
  by_cases hy : p.2 ∈ tsupport k
  · have hnorm : ‖p.2‖ ≤ r := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hks hy
    have harg : x - circleMap 0 1 p.1 • p.2 ∈ Metric.closedBall x r := by
      have heq : (x - circleMap 0 1 p.1 • p.2) - x =
          -(circleMap 0 1 p.1 • p.2) := by abel
      rw [Metric.mem_closedBall, dist_eq_norm, heq, norm_neg, norm_smul,
        norm_circleMap_zero, abs_one, one_mul]
      exact hnorm
    calc
      ‖circleKernelIntegrand k h x p‖ =
          ‖k p.2‖ * ‖h (x - circleMap 0 1 p.1 • p.2)‖ := norm_smul _ _
      _ ≤ ‖k p.2‖ * C := mul_le_mul_of_nonneg_left (hbound harg) (norm_nonneg _)
      _ = C * ‖k p.2‖ := mul_comm _ _
  · have hk0 := image_eq_zero_of_notMem_tsupport hy
    simp [circleKernelIntegrand, hk0]

end Yau.NodeProofs.P03Aux
