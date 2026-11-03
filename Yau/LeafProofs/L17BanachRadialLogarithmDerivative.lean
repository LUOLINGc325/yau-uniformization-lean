import Yau.LeafProofs.L17BanachRadialLogarithmSeries

open Set Metric Filter
open scoped Topology
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17BanachRadialLogarithmAux
open Yau.LeafProofs.L17BanachLogarithmAux

variable (A : Type*) [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

theorem logIncrement_eq_radial_primitive_tsum {z : A} {s : ℝ} (hzs : ‖s • z‖ < 1) :
    logIncrement A (s • z)=∑' k : ℕ, radialLogPrimitiveTerm A z k s := by
  have h := (logIncrement_summable A hzs).sum_add_tsum_nat_add 1
  simpa only [Finset.sum_range_one,logCoefficient_zero,zero_smul,zero_add,
    logIncrement,radialLogPrimitiveTerm] using h.symm

theorem radialLogDerivative_hasDerivAt {z : A} (hz : ‖z‖ < 1) {t : ℝ} (ht : |t| ≤ 1) :
    HasDerivAt (fun s : ℝ => logIncrement A (s • z)) (radialLogDerivative A z t) t := by
  obtain ⟨a,ha,hq0,hq⟩ := radialLog_buffer A hz
  have ha0 : 0 ≤ a := by linarith
  have hnorm (s : ℝ) (hs : s ∈ Ioo (-a) a) : ‖s • z‖ < 1 := by
    calc
      ‖s • z‖ = |s| * ‖z‖ := by rw [norm_smul,Real.norm_eq_abs]
      _ ≤ a*‖z‖ := mul_le_mul_of_nonneg_right (abs_lt.mpr hs).le (norm_nonneg z)
      _ < 1 := hq
  have hzero : Summable (fun k : ℕ => radialLogPrimitiveTerm A z k 0) := by
    have hf : (fun k : ℕ => radialLogPrimitiveTerm A z k 0)=(fun _ : ℕ => (0 : A)) := by
      funext k
      simp [radialLogPrimitiveTerm]
    rw [hf]
    exact summable_zero
  have htI : t ∈ Ioo (-a) a := by
    have h := abs_le.mp ht
    constructor <;> linarith
  have h : HasDerivAt (fun s : ℝ => ∑' k : ℕ, radialLogPrimitiveTerm A z k s)
      (radialLogDerivative A z t) t :=
    hasDerivAt_tsum_of_isPreconnected
      ((summable_geometric_of_lt_one hq0 hq).mul_left ‖z‖)
      isOpen_Ioo (convex_Ioo (-a) a).isPreconnected
      (fun k s _ => radialLogPrimitiveTerm_hasDerivAt A z k s)
      (fun k s hs => radialLogTerm_norm_le A z ha0 (abs_lt.mpr hs).le k)
      (show (0 : ℝ) ∈ Ioo (-a) a by constructor <;> linarith) hzero htI
  apply h.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds htI] with s hs
  exact logIncrement_eq_radial_primitive_tsum A (hnorm s hs)

end Yau.LeafProofs.L17BanachRadialLogarithmAux
