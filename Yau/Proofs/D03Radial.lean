import Yau.Proofs.B01Coordinate

open scoped Manifold Topology ContDiff ENNReal
open MeasureTheory Set Filter

noncomputable section

namespace Yau.Proofs.D03Aux
open Yau Yau.Blueprint Yau.Blueprint.BundlePresentation

/-- The approximation sequence starts with parameter one. -/
def correctionParameter (n : ℕ) : ℝ := (n + 1 : ℕ)

theorem correctionParameter_pos (n : ℕ) : 0 < correctionParameter n := by
  unfold correctionParameter
  positivity

theorem correctionParameter_ne_zero (n : ℕ) : correctionParameter n ≠ 0 :=
  (correctionParameter_pos n).ne'

/-- The single fixed transition used at every approximation index. -/
def radialChi (t : ℝ) : ℝ := Real.smoothTransition (t + 2)

theorem radialChi_contDiff : ContDiff ℝ ∞ radialChi :=
  Real.smoothTransition.contDiff.comp (contDiff_id.add contDiff_const)

theorem radialChi_nonneg (t : ℝ) : 0 ≤ radialChi t :=
  Real.smoothTransition.nonneg _

theorem radialChi_le_one (t : ℝ) : radialChi t ≤ 1 :=
  Real.smoothTransition.le_one _

theorem radialChi_eq_zero {t : ℝ} (h : t ≤ -2) : radialChi t = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

theorem radialChi_eq_one {t : ℝ} (h : -1 ≤ t) : radialChi t = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

theorem radialChi_deriv_eq_zero {t : ℝ} (h : t ≤ -2 ∨ -1 ≤ t) :
    deriv radialChi t = 0 := by
  rcases h with h | h
  · apply IsLocalMin.deriv_eq_zero
    exact Filter.Eventually.of_forall (fun u => by rw [radialChi_eq_zero h]; exact radialChi_nonneg u)
  · apply IsLocalMax.deriv_eq_zero
    exact Filter.Eventually.of_forall (fun u => by rw [radialChi_eq_one h]; exact radialChi_le_one u)

private theorem radialChi_deriv_max_exists :
    ∃ t ∈ Icc (-2 : ℝ) (-1), ∀ u ∈ Icc (-2 : ℝ) (-1),
      |deriv radialChi u| ≤ |deriv radialChi t| := by
  obtain ⟨t, ht, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (s := Icc (-2 : ℝ) (-1)) (by exact ⟨-2, by norm_num⟩)
    (radialChi_contDiff.continuous_deriv (by simp)).abs.continuousOn
  exact ⟨t, ht, fun u hu => hmax hu⟩

private def radialChi_deriv_max_point : ℝ := Classical.choose radialChi_deriv_max_exists

/-- Fixed once from the maximum of the derivative on the transition interval. -/
def cutoffDerivativeBound : ℝ := 1 + |deriv radialChi radialChi_deriv_max_point|

theorem cutoffDerivativeBound_pos : 0 < cutoffDerivativeBound := by
  unfold cutoffDerivativeBound
  positivity

theorem radialChi_deriv_abs_le (t : ℝ) : |deriv radialChi t| ≤ cutoffDerivativeBound := by
  by_cases ht : t ∈ Icc (-2 : ℝ) (-1)
  · have h := (Classical.choose_spec radialChi_deriv_max_exists).2 t ht
    unfold cutoffDerivativeBound radialChi_deriv_max_point
    linarith
  · have h : t ≤ -2 ∨ -1 ≤ t := by
      simp only [mem_Icc, not_and_or, not_le] at ht
      rcases ht with ht | ht
      · exact Or.inl ht.le
      · exact Or.inr ht.le
    rw [radialChi_deriv_eq_zero h, abs_zero]
    exact cutoffDerivativeBound_pos.le

def cutoffWeightConstant : ℝ := 4 * cutoffDerivativeBound ^ 2

def cutoffSmallConstant : ℝ := Real.exp 7 * cutoffWeightConstant

theorem cutoffWeightConstant_pos : 0 < cutoffWeightConstant := by
  unfold cutoffWeightConstant
  exact mul_pos (by norm_num) (sq_pos_of_pos cutoffDerivativeBound_pos)

theorem cutoffSmallConstant_pos : 0 < cutoffSmallConstant :=
  mul_pos (Real.exp_pos _) cutoffWeightConstant_pos

variable {M : ComplexManifold 1}

/-- The genuine cutoff on the given punctured-disc coordinate. -/
def cutoff (c : DiscCoordinate M) (n : ℕ) (x : M.Carrier) : ℝ :=
  Real.smoothTransition (Real.log ‖c x‖ / correctionParameter n + 2)

/-- The genuine logarithmic and power weight on the same coordinate. -/
def weight (c : DiscCoordinate M) (n : ℕ) (x : M.Carrier) : ℝ :=
  (2 / correctionParameter n) * Real.log ‖c x‖ +
    ‖c x‖ ^ (1 / correctionParameter n)

def sourceAnnulus (c : DiscCoordinate M) (n : ℕ) : Set M.Carrier :=
  {x | Real.exp (-2 * correctionParameter n) < ‖c x‖ ∧
    ‖c x‖ < Real.exp (-correctionParameter n)}

def sourceTail (c : DiscCoordinate M) (n : ℕ) : Set M.Carrier :=
  {x | ‖c x‖ < Real.exp (-correctionParameter n)}

theorem sourceAnnulus_subset_tail (c : DiscCoordinate M) (n : ℕ) :
    sourceAnnulus c n ⊆ sourceTail c n := fun _ hx => hx.2

theorem cutoff_nonneg (c : DiscCoordinate M) (n : ℕ) (x : M.Carrier) :
    0 ≤ cutoff c n x := Real.smoothTransition.nonneg _

theorem cutoff_le_one (c : DiscCoordinate M) (n : ℕ) (x : M.Carrier) :
    cutoff c n x ≤ 1 := Real.smoothTransition.le_one _

theorem cutoff_eq_zero (c : DiscCoordinate M) (hc : IsDiscCoordinate c) (n : ℕ)
    (x : M.Carrier) (hx : ‖c x‖ ≤ Real.exp (-2 * correctionParameter n)) :
    cutoff c n x = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  have hlog : Real.log ‖c x‖ ≤ -2 * correctionParameter n :=
    (Real.log_le_iff_le_exp (B01Aux.disc_mem c hc x).1).2 hx
  have h := (div_le_iff₀ (correctionParameter_pos n)).2 hlog
  linarith

theorem cutoff_eq_one (c : DiscCoordinate M) (hc : IsDiscCoordinate c) (n : ℕ)
    (x : M.Carrier) (hx : Real.exp (-correctionParameter n) ≤ ‖c x‖) :
    cutoff c n x = 1 := by
  apply Real.smoothTransition.one_of_one_le
  have hlog : -correctionParameter n ≤ Real.log ‖c x‖ :=
    (Real.le_log_iff_exp_le (B01Aux.disc_mem c hc x).1).2 hx
  have h : -1 ≤ Real.log ‖c x‖ / correctionParameter n :=
    (le_div_iff₀ (correctionParameter_pos n)).2 (by simpa using hlog)
  linarith

theorem cutoff_smooth (c : DiscCoordinate M) (hc : IsDiscCoordinate c) (n : ℕ) :
    SmoothFn (cutoff c n) := by
  intro a z hz
  have hnorm := ((B01Aux.disc_inChart_contDiffAt c hc a hz).restrict_scalars ℝ).norm ℂ
    (norm_pos_iff.mp (B01Aux.disc_mem c hc (chartInv a z)).1)
  exact (Real.smoothTransition.contDiffAt.comp z
    ((hnorm.log (B01Aux.disc_mem c hc (chartInv a z)).1.ne').div_const _ |>.add contDiffAt_const)).contDiffWithinAt

theorem weight_smooth (c : DiscCoordinate M) (hc : IsDiscCoordinate c) (n : ℕ) :
    SmoothFn (weight c n) := by
  intro a z hz
  have hnorm := ((B01Aux.disc_inChart_contDiffAt c hc a hz).restrict_scalars ℝ).norm ℂ
    (norm_pos_iff.mp (B01Aux.disc_mem c hc (chartInv a z)).1)
  exact ((contDiffAt_const.mul (hnorm.log (B01Aux.disc_mem c hc (chartInv a z)).1.ne')).add
    ((Real.contDiffAt_rpow_const_of_ne (B01Aux.disc_mem c hc (chartInv a z)).1.ne').comp z hnorm)).contDiffWithinAt

end Yau.Proofs.D03Aux
