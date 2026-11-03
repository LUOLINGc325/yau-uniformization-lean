import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

open Set Filter MeasureTheory Metric
open scoped Topology Interval
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05AutonomousAux

def autoGreenIntegrand (d : ℕ) (r s : ℝ) : ℝ := s^(1-(d : ℝ))-s/r^d

def autoGreenPrimitive (d : ℕ) (omega r s : ℝ) : ℝ :=
  (∫ a in s..r, autoGreenIntegrand d r a)/((d : ℝ)*omega)

/-- The value at the origin is harmless; the actual Green kernel is integrable there. -/
def autoRadialGreen (d : ℕ) (omega r s : ℝ) : ℝ :=
  if 0 < s ∧ s < r then autoGreenPrimitive d omega r s else 0

theorem auto_greenIntegrand_continuousOn (d : ℕ) (r : ℝ) :
    ContinuousOn (autoGreenIntegrand d r) (Ioi 0) := by
  exact (continuousOn_id.rpow_const (fun s hs => Or.inl (ne_of_gt hs))).sub (continuousOn_id.div_const _)

theorem auto_greenIntegrand_integrable (d : ℕ) {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    IntervalIntegrable (autoGreenIntegrand d r) volume s r :=
  ((auto_greenIntegrand_continuousOn d r).mono (fun _t ht => (lt_min hs hr).trans_le ht.1)).intervalIntegrable

theorem auto_greenIntegrand_nonneg (d : ℕ) {r s : ℝ} (hs : 0 < s) (hsr : s ≤ r) :
    0 ≤ autoGreenIntegrand d r s := by
  unfold autoGreenIntegrand
  rw [Real.rpow_sub hs,Real.rpow_one,Real.rpow_natCast]
  have hPow := pow_le_pow_left₀ hs.le hsr d
  exact sub_nonneg.mpr (div_le_div_of_nonneg_left hs.le (pow_pos hs _) hPow)

theorem auto_green_primitive_nonneg {d : ℕ} (hd : 0 < d) {omega r s : ℝ}
    (hOmega : 0 < omega) (hs : 0 < s) (hsr : s ≤ r) : 0 ≤ autoGreenPrimitive d omega r s := by
  apply div_nonneg _ (mul_pos (by exact_mod_cast hd) hOmega).le
  exact intervalIntegral.integral_nonneg hsr (fun t ht => auto_greenIntegrand_nonneg d (hs.trans_le ht.1) ht.2)

theorem auto_radialGreen_nonneg {d : ℕ} (hd : 0 < d) {omega r : ℝ} (hOmega : 0 < omega) (s : ℝ) :
    0 ≤ autoRadialGreen d omega r s := by
  unfold autoRadialGreen
  split_ifs with hs
  · exact auto_green_primitive_nonneg hd hOmega hs.1 hs.2.le
  · exact le_rfl

theorem auto_radialGreen_zero_outside (d : ℕ) (omega r : ℝ) {s : ℝ} (hs : s∉Ioo 0 r) :
    autoRadialGreen d omega r s=0 := ite_eq_right hs

theorem auto_green_primitive_hasDerivAt (d : ℕ) (omega : ℝ) {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    HasDerivAt (autoGreenPrimitive d omega r) (-autoGreenIntegrand d r s/((d : ℝ)*omega)) s := by
  have hCont := auto_greenIntegrand_continuousOn d r
  have hDeriv := intervalIntegral.integral_hasDerivAt_left (auto_greenIntegrand_integrable d hr hs)
    (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioi hCont s hs)
    (hCont.continuousAt (isOpen_Ioi.mem_nhds hs))
  exact hDeriv.div_const _

theorem auto_radialGreen_hasDerivAt (d : ℕ) (omega : ℝ) {r s : ℝ} (hr : 0 < r)
    (hs : 0 < s) (hsr : s < r) :
    HasDerivAt (autoRadialGreen d omega r) (-autoGreenIntegrand d r s/((d : ℝ)*omega)) s := by
  apply (auto_green_primitive_hasDerivAt d omega hr hs).congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hs hsr] with t ht
  exact ite_eq_left ht

theorem auto_greenIntegrand_hasDerivAt (d : ℕ) {r s : ℝ} (hs : 0 < s) :
    HasDerivAt (autoGreenIntegrand d r) ((1-(d : ℝ))*s^(-(d : ℝ))-1/r^d) s := by
  have hD := ((hasDerivAt_id s).rpow_const (p := 1-(d : ℝ)) (Or.inl hs.ne')).sub
    ((hasDerivAt_id s).div_const (r^d))
  convert! hD using 1; simp [id_eq,one_mul,show 1-(d : ℝ)-1=-(d : ℝ) by ring]

theorem auto_green_radial_laplacian {d : ℕ} (hd : 0 < d) {omega r s : ℝ}
    (hOmega : 0 < omega) (hr : 0 < r) (hs : 0 < s) :
    -((1-(d : ℝ))*s^(-(d : ℝ))-1/r^d)/((d : ℝ)*omega)+
      ((d : ℝ)-1)*(-autoGreenIntegrand d r s/((d : ℝ)*omega))/s=1/(omega*r^d) := by
  rw [autoGreenIntegrand,Real.rpow_sub hs,Real.rpow_one,Real.rpow_natCast,
    Real.rpow_neg hs.le,Real.rpow_natCast]
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  field_simp [hd0,hOmega.ne',hr.ne',hs.ne']
  ring

theorem auto_green_radial_flux {d : ℕ} (hd : 0 < d) (omega r : ℝ) {s : ℝ} (hs : 0 < s) :
    s^(d-1)*(-autoGreenIntegrand d r s/((d : ℝ)*omega))=
      (s^d/r^d-1)/((d : ℝ)*omega) := by
  have hPower : s^d=s^(d-1)*s := by rw [← pow_succ,Nat.sub_add_cancel hd]
  rw [autoGreenIntegrand,Real.rpow_sub hs,Real.rpow_one,Real.rpow_natCast]
  rw [hPower]
  by_cases hO : omega=0
  · simp [hO]
  by_cases hR : r=0
  · subst r
    simp only [zero_pow hd.ne',div_zero,sub_zero,zero_sub,neg_div]
    field_simp [hs.ne']
  · have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
    field_simp [hd0,hO,hR,hs.ne']
    ; ring

theorem auto_green_primitive_outer (d : ℕ) (omega r : ℝ) : autoGreenPrimitive d omega r r=0 := by
  simp [autoGreenPrimitive]

theorem auto_green_primitive_hasDerivAt_outer (d : ℕ) (omega : ℝ) {r : ℝ} (hr : 0 < r) :
    HasDerivAt (autoGreenPrimitive d omega r) 0 r := by
  have h := auto_green_primitive_hasDerivAt d omega hr hr
  have hZero : autoGreenIntegrand d r r=0 := by
    rw [autoGreenIntegrand,Real.rpow_sub hr,Real.rpow_one,Real.rpow_natCast,sub_self]
  simpa only [hZero,neg_zero,zero_div] using h

end Yau.LeafProofs.L05AutonomousAux
