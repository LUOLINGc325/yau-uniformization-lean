import Yau.LeafProofs.L05AutonomousBallMeanKernelSmooth
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.Deriv.Support

open Set Filter MeasureTheory Metric
open scoped Topology ContDiff
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05AutonomousAux

def autoGreenBump : ContDiffBump (0 : ℝ) where
  rIn := 1
  rOut := 2
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

def autoGreenInner (eta s : ℝ) : ℝ := 1-autoGreenBump (s/eta)
def autoGreenOuter (r eta s : ℝ) : ℝ := if s < r then autoGreenInner eta (r-s) else 0
def autoGreenTest (d : ℕ) (omega r eta s : ℝ) : ℝ :=
  autoRadialGreen d omega r s*autoGreenInner eta s*autoGreenOuter r eta s

theorem auto_green_inner_range (eta s : ℝ) : 0 ≤ autoGreenInner eta s ∧ autoGreenInner eta s ≤ 1 := by
  have h0 := autoGreenBump.nonneg (x := s/eta)
  have h1 := autoGreenBump.le_one (x := s/eta)
  dsimp only [autoGreenInner]
  constructor <;> linarith

theorem auto_green_inner_zero {eta s : ℝ} (heta : 0 < eta) (hs : |s| ≤ eta) :
    autoGreenInner eta s=0 := by
  have hMem : s/eta∈closedBall (0 : ℝ) autoGreenBump.rIn := by
    simp only [mem_closedBall,dist_zero_right,Real.norm_eq_abs,autoGreenBump,abs_div,abs_of_pos heta]
    exact (div_le_one heta).mpr hs
  simp only [autoGreenInner,autoGreenBump.one_of_mem_closedBall hMem,sub_self]

theorem auto_green_inner_one {eta s : ℝ} (heta : 0 < eta) (hs : 2*eta ≤ |s|) :
    autoGreenInner eta s=1 := by
  have hNot : s/eta∉Function.support autoGreenBump := by
    rw [autoGreenBump.support_eq]
    simp only [mem_ball,dist_zero_right,Real.norm_eq_abs,autoGreenBump,abs_div,abs_of_pos heta]
    exact not_lt.mpr ((le_div_iff₀ heta).mpr (by simpa only [mul_comm] using hs))
  simp only [autoGreenInner,Function.notMem_support.mp hNot,sub_zero]

theorem auto_green_inner_contDiff (eta : ℝ) : ContDiff ℝ ∞ (autoGreenInner eta) :=
  contDiff_const.sub (autoGreenBump.contDiff.comp (contDiff_id.div_const eta))

theorem auto_green_outer_range (r eta s : ℝ) : 0 ≤ autoGreenOuter r eta s ∧ autoGreenOuter r eta s ≤ 1 := by
  by_cases hs : s < r
  · simpa only [autoGreenOuter,ite_eq_left hs] using auto_green_inner_range eta (r-s)
  · simp only [autoGreenOuter,ite_eq_right hs,le_refl,zero_le_one,and_self]

theorem auto_green_outer_zero {eta r s : ℝ} (heta : 0 < eta) (hs : r-eta ≤ s) :
    autoGreenOuter r eta s=0 := by
  by_cases hsr : s < r
  · rw [autoGreenOuter,ite_eq_left hsr]
    apply auto_green_inner_zero heta
    rw [abs_of_pos (sub_pos.mpr hsr)]
    linarith
  · exact ite_eq_right hsr

theorem auto_green_outer_one {eta r s : ℝ} (heta : 0 < eta) (hs : s ≤ r-2*eta) :
    autoGreenOuter r eta s=1 := by
  have hsr : s < r := by linarith
  rw [autoGreenOuter,ite_eq_left hsr]
  apply auto_green_inner_one heta
  rw [abs_of_pos (sub_pos.mpr hsr)]
  linarith

theorem auto_green_outer_contDiff {eta : ℝ} (heta : 0 < eta) (r : ℝ) :
    ContDiff ℝ ∞ (autoGreenOuter r eta) := by
  apply contDiff_iff_contDiffAt.mpr
  intro s
  by_cases hs : s < r
  · have hEq : autoGreenOuter r eta=ᶠ[𝓝 s] (fun t => autoGreenInner eta (r-t)) := by
      filter_upwards [isOpen_Iio.mem_nhds hs] with t ht
      exact ite_eq_left ht
    exact ((auto_green_inner_contDiff eta).comp (contDiff_const.sub contDiff_id)).contDiffAt.congr_of_eventuallyEq hEq
  · have hsr : r ≤ s := le_of_not_gt hs
    have hEq : autoGreenOuter r eta=ᶠ[𝓝 s] (fun _ => (0 : ℝ)) := by
      filter_upwards [isOpen_Ioi.mem_nhds (show r-eta < s by linarith)] with t ht
      exact auto_green_outer_zero heta ht.le
    exact contDiffAt_const.congr_of_eventuallyEq hEq

theorem auto_green_test_zero {d : ℕ} (omega r : ℝ) {eta s : ℝ}
    (heta : 0 < eta) (hs : s∉Icc eta (r-eta)) : autoGreenTest d omega r eta s=0 := by
  by_cases hsr : 0 < s ∧ s < r
  · by_cases hse : s < eta
    · have hI := auto_green_inner_zero heta (show |s| ≤ eta by rw [abs_of_pos hsr.1]; exact hse.le)
      simp only [autoGreenTest,hI,mul_zero,zero_mul]
    · have hO : autoGreenOuter r eta s=0 := auto_green_outer_zero heta (by
        by_contra h
        exact hs ⟨le_of_not_gt hse,(lt_of_not_ge h).le⟩)
      simp only [autoGreenTest,hO,mul_zero]
  · simp only [autoGreenTest,auto_radialGreen_zero_outside d omega r hsr,zero_mul]

theorem auto_green_test_tsupport {d : ℕ} (omega r : ℝ) {eta : ℝ} (heta : 0 < eta) :
    tsupport (autoGreenTest d omega r eta) ⊆ Icc eta (r-eta) := by
  apply closure_minimal ?_ isClosed_Icc
  intro s hs
  by_contra h
  exact hs (auto_green_test_zero omega r heta h)

theorem auto_green_test_compact {d : ℕ} (omega r : ℝ) {eta : ℝ} (heta : 0 < eta) :
    HasCompactSupport (autoGreenTest d omega r eta) :=
  isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) (auto_green_test_tsupport omega r heta)

theorem auto_green_test_contDiff {d : ℕ} (hd : 2 ≤ d) (omega : ℝ)
    {r eta : ℝ} (hr : 0 < r) (heta : 0 < eta) :
    ContDiff ℝ ∞ (autoGreenTest d omega r eta) := by
  apply contDiff_iff_contDiffAt.mpr
  intro s
  by_cases hs : s∈Ioo 0 r
  · have hEq : autoGreenTest d omega r eta=ᶠ[𝓝 s]
        (fun t => autoGreenPrimitive d omega r t*autoGreenInner eta t*autoGreenOuter r eta t) := by
      filter_upwards [isOpen_Ioo.mem_nhds hs] with t ht
      simp only [autoGreenTest,autoRadialGreen,ite_eq_left (show 0 < t ∧ t < r from ht)]
    exact (((auto_green_primitive_contDiffAt hd omega hr hs.1).mul
      (auto_green_inner_contDiff eta).contDiffAt).mul (auto_green_outer_contDiff heta r).contDiffAt).congr_of_eventuallyEq hEq
  · have hNot : s∉tsupport (autoGreenTest d omega r eta) := by
      intro hm
      have hh := auto_green_test_tsupport omega r heta hm
      exact hs ⟨heta.trans_le hh.1,by linarith [hh.2]⟩
    exact contDiffAt_const.congr_of_eventuallyEq (notMem_tsupport_iff_eventuallyEq.mp hNot)

theorem auto_green_test_nonneg_le {d : ℕ} (hd : 0 < d) {omega r eta s : ℝ}
    (hOmega : 0 < omega) (hr : 0 < r) :
    0 ≤ autoGreenTest d omega r eta s ∧ autoGreenTest d omega r eta s ≤ autoRadialGreen d omega r s := by
  have hK := auto_radialGreen_nonneg (r := r) hd hOmega s
  obtain ⟨hI0,hI1⟩ := auto_green_inner_range eta s
  obtain ⟨hO0,hO1⟩ := auto_green_outer_range r eta s
  constructor
  · exact mul_nonneg (mul_nonneg hK hI0) hO0
  · dsimp only [autoGreenTest]
    calc
      _ ≤ autoRadialGreen d omega r s*1*1 := by gcongr
      _ = _ := by ring

theorem auto_green_test_tendsto {d : ℕ} (omega r s : ℝ) :
    Tendsto (fun eta : ℝ => autoGreenTest d omega r eta s) (𝓝[>] 0)
      (𝓝 (autoRadialGreen d omega r s)) := by
  by_cases hs : 0 < s ∧ s < r
  · have hp : 0 < min (s/2) ((r-s)/2) := lt_min (half_pos hs.1) (half_pos (sub_pos.mpr hs.2))
    have hEvent : Ioo (0 : ℝ) (min (s/2) ((r-s)/2))∈𝓝[>] 0 :=
      mem_nhdsGT_iff_exists_Ioo_subset.mpr ⟨_,hp,subset_rfl⟩
    apply tendsto_const_nhds.congr'
    filter_upwards [hEvent] with eta heta
    have hI : autoGreenInner eta s=1 := auto_green_inner_one heta.1 (by
      rw [abs_of_pos hs.1]
      have h := heta.2.trans_le (min_le_left _ _)
      linarith)
    have hO : autoGreenOuter r eta s=1 := auto_green_outer_one heta.1 (by
      have h := heta.2.trans_le (min_le_right _ _)
      linarith)
    simp only [autoGreenTest,hI,hO,mul_one]
  · have hZero : ∀ eta : ℝ, autoGreenTest d omega r eta s=0 := by
      intro eta
      simp only [autoGreenTest,auto_radialGreen_zero_outside d omega r hs,zero_mul]
    simpa only [hZero,auto_radialGreen_zero_outside d omega r hs] using
      (tendsto_const_nhds (x := (0 : ℝ)) : Tendsto (fun _ : ℝ => (0 : ℝ)) (𝓝[>] 0) (𝓝 0))

end Yau.LeafProofs.L05AutonomousAux
