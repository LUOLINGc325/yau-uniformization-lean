import Yau.Proofs.C01IndexCutoffJets
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! The smooth index cutoff has uniformly controlled Dirichlet energy:
only two strips of total length 2κ contribute to its derivative. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology Interval

namespace Yau.NodeProofs.C01Aux

theorem integral_bound_of_zero_middle
    (Q : ℝ → ℝ) (hQ : ContinuousOn Q (Set.Icc (0 : ℝ) 1))
    (κ C : ℝ) (hκ : 0 < κ) (hκhalf : κ ≤ 1 / 2)
    (hzero : ∀ u ∈ Set.Ioo κ (1 - κ), Q u = 0)
    (hupper : ∀ u ∈ Set.Icc (0 : ℝ) 1, Q u ≤ C) :
    (∫ u in (0 : ℝ)..1, Q u) ≤ 2 * κ * C := by
  have hκ1 : κ ≤ 1 := by linarith
  have hmiddle : κ ≤ 1 - κ := by linarith
  have hi (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
      IntervalIntegrable Q volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hab]
    exact hQ.mono (Set.Icc_subset_Icc ha hb)
  have hleft : (∫ u in (0 : ℝ)..κ, Q u) ≤ κ * C := by
    have H := intervalIntegral.integral_mono_on hκ.le (hi 0 κ le_rfl hκ.le hκ1)
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => C) volume 0 κ)
      (fun u hu => hupper u ⟨hu.1, hu.2.trans hκ1⟩)
    simpa only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] using H
  have hright : (∫ u in (1 - κ)..(1 : ℝ), Q u) ≤ κ * C := by
    have H := intervalIntegral.integral_mono_on (by linarith : 1 - κ ≤ 1)
      (hi (1 - κ) 1 (by linarith) (by linarith) le_rfl)
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => C) volume (1 - κ) 1)
      (fun u hu => hupper u ⟨(by linarith [hu.1]), hu.2⟩)
    convert H using 1 <;> simp only [intervalIntegral.integral_const, smul_eq_mul] <;> ring
  have hmid : (∫ u in κ..(1 - κ), Q u) = 0 := by
    have H : (∫ u in κ..(1 - κ), Q u) = (∫ _u in κ..(1 - κ), (0 : ℝ)) :=
      intervalIntegral.integral_congr_Ioo_of_le (μ := volume) hmiddle hzero
    simpa using H
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (hi 0 κ le_rfl hκ.le hκ1) (hi κ (1 - κ) hκ.le hmiddle (by linarith))
  have hsplit' := intervalIntegral.integral_add_adjacent_intervals
    (hi 0 (1 - κ) le_rfl (by linarith) (by linarith))
    (hi (1 - κ) 1 (by linarith) (by linarith) le_rfl)
  rw [hmid, add_zero] at hsplit
  rw [← hsplit', ← hsplit]
  nlinarith [hleft, hright]

theorem indexCutoff_derivative_energy_bound :
    ∃ D : ℝ, 0 < D ∧ ∀ κ : ℝ, 0 < κ → κ ≤ 1 / 2 →
      (∫ u in (0 : ℝ)..1, deriv (indexCutoff κ) u ^ 2) ≤ D / κ := by
  obtain ⟨M, hM, hb⟩ := indexCutoff_derivative_bound
  refine ⟨2 * M ^ 2, mul_pos (by norm_num) (sq_pos_of_pos hM), ?_⟩
  intro κ hκ hκhalf
  have hcont : Continuous (fun u => deriv (indexCutoff κ) u ^ 2) :=
    ((indexCutoff_contDiff κ).continuous_deriv (by simp)).pow 2
  have hzero (u : ℝ) (hu : u ∈ Set.Ioo κ (1 - κ)) : deriv (indexCutoff κ) u ^ 2 = 0 := by
    have heq : indexCutoff κ =ᶠ[𝓝 u] (fun _ => (1 : ℝ)) := by
      filter_upwards [isOpen_Ioo.mem_nhds hu] with v hv
      exact indexCutoff_one_middle hκ hv.1.le hv.2.le
    rw [heq.deriv_eq, deriv_const, zero_pow (by norm_num : 2 ≠ 0)]
  have hupper (u : ℝ) (_hu : u ∈ Set.Icc (0 : ℝ) 1) :
      deriv (indexCutoff κ) u ^ 2 ≤ (M / κ) ^ 2 := by
    rw [← sq_abs (deriv (indexCutoff κ) u)]
    gcongr
    exact hb κ hκ u
  have H := integral_bound_of_zero_middle (fun u => deriv (indexCutoff κ) u ^ 2)
    hcont.continuousOn κ ((M / κ) ^ 2) hκ hκhalf hzero hupper
  convert H using 1 <;> field_simp [hκ.ne'] <;> ring

end Yau.NodeProofs.C01Aux
