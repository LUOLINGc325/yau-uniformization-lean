import Yau.LeafProofs.L05AutonomousActualDerivativesSpatialBuffer
import Yau.LeafProofs.L05AutonomousTimeIncrementsFTC

open Set Filter MeasureTheory Metric
open scoped Topology ContDiff Interval
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05AutonomousAux
open Yau.Parabolic

theorem auto_backward_time_slice {n : ℕ} {r : ℝ} {x : Space n} (hx : x∈ball 0 r) :
    {t : ℝ | (x,t)∈backward r}=Ioc (-(r^2)) 0 := by
  ext t
  change (x∈ball 0 r ∧ t∈Ioc (-(r^2)) 0) ↔ t∈Ioc (-(r^2)) 0
  simp only [hx,true_and]

theorem auto_backward_time_uniqueDiff {n : ℕ} {r : ℝ} (hr : 0 < r) {p : Point n}
    (hp : p∈backward r) : UniqueDiffWithinAt ℝ {t : ℝ | (p.1,t)∈backward r} p.2 := by
  rw [auto_backward_time_slice hp.1]
  have hInterval : -(r^2) < (0 : ℝ) := by nlinarith [sq_pos_of_pos hr]
  have hOn : UniqueDiffOn ℝ (Ioc (-(r^2)) 0) := uniqueDiffOn_convex (convex_Ioc _ _)
    (by simpa only [interior_Ioc,nonempty_Ioo] using hInterval)
  exact hOn p.2 hp.2

theorem auto_time_integrable_on_buffer {n : ℕ} {R a b : ℝ} {V : Point n → ℝ}
    (hV : ContinuousOn V (autoDerivativeClosed R)) {x : Space n} (hx : x∈ball 0 R)
    (ha : a∈Icc (-(R^2)) 0) (hb : b∈Icc (-(R^2)) 0) :
    IntervalIntegrable (fun t : ℝ => V (x,t)) volume a b := by
  apply ((auto_derivativeClosed_time_continuousOn hV hx).mono ?_).intervalIntegrable
  intro t ht
  exact ⟨(le_min ha.1 hb.1).trans ht.1,ht.2.trans (max_le ha.2 hb.2)⟩

section Time
variable {n : ℕ} {r R : ℝ} (hr : 0 < r) (hrR : r < R) {u V : Point n → ℝ}
  (hV : ContinuousOn V (autoDerivativeClosed R))
  (hTimeFTC : ∀ x∈ball (0 : Space n) R, ∀ a∈Icc (-(R^2)) 0, ∀ b∈Icc (-(R^2)) 0,
    u (x,b)-u (x,a)=∫ t in a..b, V (x,t))

include hr hrR hV hTimeFTC

theorem auto_time_from_buffered_ftc {p : Point n} (hp : p∈backward r) :
    HasDerivWithinAt (fun t : ℝ => u (p.1,t)) (V p) {t : ℝ | (p.1,t)∈backward r} p.2 := by
  have hpC := auto_backward_subset_derivativeClosed hr hrR hp
  have hx : p.1∈ball (0 : Space n) R := ball_subset_ball hrR.le hp.1
  have hR : 0 < R := hr.trans hrR
  have hInterval : -(R^2) < (0 : ℝ) := by nlinarith [sq_pos_of_pos hR]
  have hWithin := auto_hasDerivWithinAt_of_ftc (f := fun t : ℝ => u (p.1,t)) (V := fun t : ℝ => V (p.1,t)) hInterval
    (auto_derivativeClosed_time_continuousOn hV hx) (hTimeFTC p.1 hx) hpC.2
  rw [auto_backward_time_slice hp.1]
  apply hWithin.mono
  intro t ht
  have hsq : r^2 < R^2 := by nlinarith [mul_self_lt_mul_self hr.le hrR]
  exact ⟨by linarith [ht.1],ht.2⟩

theorem auto_timeD_from_buffered_ftc {p : Point n} (hp : p∈backward r) :
    timeD (backward r) u p=V p :=
  (auto_time_from_buffered_ftc hr hrR hV hTimeFTC hp).derivWithin (auto_backward_time_uniqueDiff hr hp)

end Time
end Yau.LeafProofs.L05AutonomousAux
