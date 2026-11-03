import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

open Set Filter MeasureTheory
open scoped Topology Interval
noncomputable section
set_option maxHeartbeats 2000000
namespace Yau.LeafProofs.L05AutonomousAux

/-- The backward second difference; its dyadic reconstruction has a plus sign. -/
def autoRealSecond (f : ℝ → ℝ) (t h : ℝ) : ℝ := f t-2*f (t-h)+f (t-2*h)

def autoBackwardSlope (f : ℝ → ℝ) (t h : ℝ) : ℝ := (f t-f (t-h))/h

def autoDyadicStep (h : ℝ) (k : ℕ) : ℝ := h/(2 : ℝ)^k

theorem auto_backward_dyadic_identity (f : ℝ → ℝ) (t h : ℝ) :
    f t-f (t-h)=(f t-f (t-2*h))/2+autoRealSecond f t h/2 := by
  unfold autoRealSecond
  ring

theorem auto_backward_slope_double (f : ℝ → ℝ) (t h : ℝ) :
    autoBackwardSlope f t h-autoBackwardSlope f t (2*h)=autoRealSecond f t h/(2*h) := by
  unfold autoBackwardSlope autoRealSecond
  ring

theorem auto_backward_slope_half (f : ℝ → ℝ) (t : ℝ) {h : ℝ} (hh : h ≠ 0) :
    autoBackwardSlope f t (h/2)-autoBackwardSlope f t h=autoRealSecond f t (h/2)/h := by
  unfold autoBackwardSlope autoRealSecond
  rw [show 2*(h/2)=h by ring]
  field_simp
  ring

theorem auto_dyadicStep_pos {h : ℝ} (hh : 0 < h) (k : ℕ) : 0 < autoDyadicStep h k :=
  div_pos hh (pow_pos (by norm_num) _)

theorem auto_dyadicStep_le {h : ℝ} (hh : 0 ≤ h) (k : ℕ) : autoDyadicStep h k ≤ h :=
  div_le_self hh (one_le_pow₀ (by norm_num))

theorem auto_dyadicStep_zero (h : ℝ) : autoDyadicStep h 0=h := by simp [autoDyadicStep]

theorem auto_dyadicStep_succ (h : ℝ) (k : ℕ) : autoDyadicStep h (k+1)=autoDyadicStep h k/2 := by
  simp only [autoDyadicStep,pow_succ]
  ring

theorem auto_dyadicStep_tendsto (h : ℝ) : Tendsto (autoDyadicStep h) atTop (𝓝 0) :=
  tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2))

theorem auto_dyadicStep_rpow {h : ℝ} (hh : 0 ≤ h) (r : ℝ) (k : ℕ) :
    (autoDyadicStep h k)^r=h^r*((1/2 : ℝ)^r)^k := by
  have hEq : autoDyadicStep h k=h*(1/2 : ℝ)^k := by simp only [autoDyadicStep,div_pow,one_pow]; ring
  rw [hEq,Real.mul_rpow hh (pow_nonneg (by norm_num) _),Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 1/2)]

theorem auto_geometric_sum_bound {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (N : ℕ) :
    ∑ k∈Finset.range N, r^k ≤ 1/(1-r) := by
  apply (le_div_iff₀ (sub_pos.mpr hr1)).mpr
  rw [geom_sum_mul_neg]
  linarith [pow_nonneg hr0 N]

theorem auto_geometric_limit {u : ℕ → ℝ} {B r : ℝ} (hr : r < 1)
    (hStep : ∀ k, |u (k+1)-u k| ≤ B*r^k) :
    ∃ v : ℝ, Tendsto u atTop (𝓝 v) ∧ ∀ k, |u k-v| ≤ B*r^k/(1-r) := by
  have hDist (k : ℕ) : dist (u k) (u (k+1)) ≤ B*r^k := by
    simpa only [Real.dist_eq,abs_sub_comm] using hStep k
  obtain ⟨v,hv⟩ := cauchySeq_tendsto_of_complete (cauchySeq_of_le_geometric r B hr hDist)
  exact ⟨v,hv,fun k => by simpa only [Real.dist_eq] using dist_le_of_le_geometric_of_tendsto r B hr hDist hv k⟩

end Yau.LeafProofs.L05AutonomousAux
