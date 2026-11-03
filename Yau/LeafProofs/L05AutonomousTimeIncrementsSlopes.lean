import Yau.LeafProofs.L05AutonomousTimeIncrements
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Topology.Order.ProjIcc

open Set Filter MeasureTheory Metric
open scoped Topology Interval
noncomputable section
set_option maxHeartbeats 2000000
namespace Yau.LeafProofs.L05AutonomousAux

def autoDyadicDerivative (f : ℝ → ℝ) (h t : ℝ) : ℝ :=
  limUnder atTop (fun k : ℕ => autoBackwardSlope f t (autoDyadicStep h k))

theorem auto_second_slope_step {a b d A s : ℝ} (hd : 0 < d) (hA : 0 ≤ A) (hs : 0 ≤ s)
    {f : ℝ → ℝ}
    (hSecond : ∀ t h : ℝ, 0 < h → a ≤ t-2*h → t ≤ b → |autoRealSecond f t h| ≤ A*h^s)
    {t h : ℝ} (ht : t∈Icc (a+d) b) (hh : 0 < h) (hhd : h ≤ d/2) :
    |autoBackwardSlope f t (h/2)-autoBackwardSlope f t h| ≤ A*h^(s-1) := by
  rw [auto_backward_slope_half f t hh.ne',abs_div,abs_of_pos hh]
  have hSec := hSecond t (h/2) (half_pos hh) (by linarith [ht.1]) ht.2
  have hPow := Real.rpow_le_rpow (half_pos hh).le (show h/2 ≤ h by linarith) hs
  have hNum := hSec.trans (mul_le_mul_of_nonneg_left hPow hA)
  have hDiv := div_le_div_of_nonneg_right hNum hh.le
  rw [Real.rpow_sub_one hh.ne']
  simpa only [mul_div_assoc] using hDiv

theorem auto_dyadic_slope_step {a b d A s h : ℝ} (hd : 0 < d) (hA : 0 ≤ A) (hs : 0 ≤ s)
    {f : ℝ → ℝ}
    (hSecond : ∀ t h : ℝ, 0 < h → a ≤ t-2*h → t ≤ b → |autoRealSecond f t h| ≤ A*h^s)
    (hh : 0 < h) (hhd : h ≤ d/2) {t : ℝ} (ht : t∈Icc (a+d) b) (k : ℕ) :
    |autoBackwardSlope f t (autoDyadicStep h (k+1))-autoBackwardSlope f t (autoDyadicStep h k)| ≤
      A*h^(s-1)*((1/2 : ℝ)^(s-1))^k := by
  rw [auto_dyadicStep_succ]
  have hStep := auto_second_slope_step hd hA hs hSecond ht (auto_dyadicStep_pos hh k)
    ((auto_dyadicStep_le hh.le k).trans hhd)
  rw [auto_dyadicStep_rpow hh.le] at hStep
  simpa only [mul_assoc] using hStep

theorem auto_dyadic_slope_tendsto {a b d A s h : ℝ} (hd : 0 < d) (hA : 0 ≤ A) (hs : 1 < s)
    {f : ℝ → ℝ}
    (hSecond : ∀ t h : ℝ, 0 < h → a ≤ t-2*h → t ≤ b → |autoRealSecond f t h| ≤ A*h^s)
    (hh : 0 < h) (hhd : h ≤ d/2) {t : ℝ} (ht : t∈Icc (a+d) b) :
    Tendsto (fun k => autoBackwardSlope f t (autoDyadicStep h k)) atTop (𝓝 (autoDyadicDerivative f h t)) ∧
      ∀ k, |autoBackwardSlope f t (autoDyadicStep h k)-autoDyadicDerivative f h t| ≤
        A*h^(s-1)*((1/2 : ℝ)^(s-1))^k/(1-(1/2 : ℝ)^(s-1)) := by
  have hr : (1/2 : ℝ)^(s-1) < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) (by linarith)
  have hStep := auto_dyadic_slope_step hd hA (by linarith : 0 ≤ s) hSecond hh hhd ht
  have hDist (k : ℕ) : dist (autoBackwardSlope f t (autoDyadicStep h k))
      (autoBackwardSlope f t (autoDyadicStep h (k+1))) ≤ A*h^(s-1)*((1/2 : ℝ)^(s-1))^k := by
    simpa only [Real.dist_eq,abs_sub_comm] using hStep k
  have hConv := (cauchySeq_of_le_geometric _ _ hr hDist).tendsto_limUnder
  refine ⟨hConv,fun k => ?_⟩
  simpa only [Real.dist_eq,autoDyadicDerivative] using dist_le_of_le_geometric_of_tendsto _ _ hr hDist hConv k

theorem auto_uniform_limit_of_geometric_error {X : Type*} {S : Set X} {F : ℕ → X → ℝ} {V : X → ℝ}
    {B r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hError : ∀ k x, x∈S → |F k x-V x| ≤ B*r^k) : TendstoUniformlyOn F V atTop S := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro eps heps
  have hLim : Tendsto (fun k : ℕ => B*r^k) atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).const_mul B
  filter_upwards [hLim.eventually (gt_mem_nhds heps)] with k hk x hx
  simpa only [Real.dist_eq,abs_sub_comm] using (hError k x hx).trans_lt hk

theorem auto_dyadic_slope_uniform {a b d A s h : ℝ} (hd : 0 < d) (hA : 0 ≤ A) (hs : 1 < s)
    {f : ℝ → ℝ}
    (hSecond : ∀ t h : ℝ, 0 < h → a ≤ t-2*h → t ≤ b → |autoRealSecond f t h| ≤ A*h^s)
    (hh : 0 < h) (hhd : h ≤ d/2) :
    TendstoUniformlyOn (fun k t => autoBackwardSlope f t (autoDyadicStep h k))
      (autoDyadicDerivative f h) atTop (Icc (a+d) b) := by
  have hr0 : 0 ≤ (1/2 : ℝ)^(s-1) := Real.rpow_nonneg (by norm_num) _
  have hr1 : (1/2 : ℝ)^(s-1) < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) (by linarith)
  apply auto_uniform_limit_of_geometric_error
    (B := A*h^(s-1)/(1-(1/2 : ℝ)^(s-1))) (r := (1/2 : ℝ)^(s-1)) hr0 hr1
  intro k t ht
  have h := (auto_dyadic_slope_tendsto hd hA hs hSecond hh hhd ht).2 k
  convert h using 1 <;> ring

end Yau.LeafProofs.L05AutonomousAux
