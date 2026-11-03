import Yau.LeafProofs.L05AutonomousActualDerivativesSpatial

open Set Filter MeasureTheory Metric
open scoped Topology ContDiff Interval
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05AutonomousAux
open Yau.Parabolic

def autoDerivativeClosed {n : ℕ} (R : ℝ) : Set (Point n) :=
  closedBall (0 : Space n) R ×ˢ Icc (-(R^2)) 0

theorem auto_backward_subset_derivativeClosed {n : ℕ} {r R : ℝ} (hr : 0 < r) (hrR : r < R) :
    backward (n := n) r ⊆ autoDerivativeClosed R := by
  intro p hp
  change p.1∈ball (0 : Space n) r ∧ p.2∈Ioc (-(r^2)) 0 at hp
  change p.1∈closedBall (0 : Space n) R ∧ p.2∈Icc (-(R^2)) 0
  have hsq : r^2 < R^2 := by nlinarith [mul_self_lt_mul_self hr.le hrR]
  exact ⟨closedBall_subset_closedBall hrR.le (ball_subset_closedBall hp.1),⟨by linarith [hp.2.1],hp.2.2⟩⟩

theorem auto_derivativeClosed_spatial_continuousOn {n : ℕ} {F : Type*} [TopologicalSpace F]
    {R t : ℝ} {W : Point n → F} (hW : ContinuousOn W (autoDerivativeClosed R))
    (ht : t∈Icc (-(R^2)) 0) : ContinuousOn (fun x : Space n => W (x,t)) (ball 0 R) := by
  simpa only [Function.comp_def,id_eq] using hW.comp
    (continuous_id.prodMk continuous_const).continuousOn (fun x hx => ⟨ball_subset_closedBall hx,ht⟩)

theorem auto_derivativeClosed_time_continuousOn {n : ℕ} {F : Type*} [TopologicalSpace F]
    {R : ℝ} {W : Point n → F} (hW : ContinuousOn W (autoDerivativeClosed R))
    {x : Space n} (hx : x∈ball 0 R) : ContinuousOn (fun t : ℝ => W (x,t)) (Icc (-(R^2)) 0) := by
  simpa only [Function.comp_def,id_eq] using hW.comp
    (continuous_const.prodMk continuous_id).continuousOn (fun t ht => ⟨ball_subset_closedBall hx,ht⟩)

section Spatial
variable {n : ℕ} {R : ℝ} {u : Point n → ℝ}
  {G : Point n → Space n →L[ℝ] ℝ}
  {B : Point n → Space n →L[ℝ] Space n →L[ℝ] ℝ}
  (hG : ContinuousOn G (autoDerivativeClosed R)) (hB : ContinuousOn B (autoDerivativeClosed R))
  (hScalarFTC : ∀ t∈Icc (-(R^2)) 0, ∀ x∈ball (0 : Space n) R, ∀ h : Space n,
    (∀ s∈Icc (0 : ℝ) 1, x+s • h∈ball 0 R) →
    u (x+h,t)-u (x,t)=∫ s in (0 : ℝ)..1, G (x+s • h,t) h)
  (hGradientFTC : ∀ t∈Icc (-(R^2)) 0, ∀ x∈ball (0 : Space n) R, ∀ h : Space n,
    (∀ s∈Icc (0 : ℝ) 1, x+s • h∈ball 0 R) →
    G (x+h,t)-G (x,t)=∫ s in (0 : ℝ)..1, B (x+s • h,t) h)

include hG hB hScalarFTC hGradientFTC

theorem auto_spatial_from_buffered_ftc {t : ℝ} (ht : t∈Icc (-(R^2)) 0)
    {x : Space n} (hx : x∈ball 0 R) :
    HasFDerivAt (fun y : Space n => u (y,t)) (G (x,t)) x ∧
    HasFDerivAt (fun y : Space n => G (y,t)) (B (x,t)) x ∧
    spatialD u (x,t)=G (x,t) ∧ spatialDD u (x,t)=B (x,t) ∧
    ContDiffAt ℝ 2 (fun y : Space n => u (y,t)) x := by
  have hGS := auto_derivativeClosed_spatial_continuousOn hG ht
  have hBS := auto_derivativeClosed_spatial_continuousOn hB ht
  have hD := auto_scalar_from_segment_integral (f := fun y : Space n => u (y,t)) isOpen_ball hGS (hScalarFTC t ht)
  have hDD := auto_gradient_from_segment_integral (g := fun y : Space n => G (y,t)) isOpen_ball hBS (hGradientFTC t ht)
  refine ⟨hD x hx,hDD x hx,(hD x hx).fderiv,?_,?_⟩
  · exact auto_second_derivative_of_actual_derivatives isOpen_ball hDD hD x hx
  · exact auto_contDiffAt_two_of_actual_derivatives isOpen_ball hBS hDD hD x hx

theorem auto_spatial_from_buffered_ftc_on_backward {r : ℝ} (hr : 0 < r) (hrR : r < R)
    {p : Point n} (hp : p∈backward r) :
    HasFDerivAt (fun x : Space n => u (x,p.2)) (G p) p.1 ∧
    HasFDerivAt (fun x : Space n => G (x,p.2)) (B p) p.1 ∧
    spatialD u p=G p ∧ spatialDD u p=B p ∧
    ContDiffAt ℝ 2 (fun x : Space n => u (x,p.2)) p.1 := by
  have hpC := auto_backward_subset_derivativeClosed hr hrR hp
  have hx : p.1∈ball (0 : Space n) R := (ball_subset_ball hrR.le) hp.1
  exact auto_spatial_from_buffered_ftc hG hB hScalarFTC hGradientFTC hpC.2 hx

theorem auto_spatial_hasFDerivAt_from_buffered_ftc {r : ℝ} (hr : 0 < r) (hrR : r < R)
    {p : Point n} (hp : p∈backward r) :
    HasFDerivAt (fun x : Space n => u (x,p.2)) (G p) p.1 :=
  (auto_spatial_from_buffered_ftc_on_backward hG hB hScalarFTC hGradientFTC hr hrR hp).1

theorem auto_gradient_hasFDerivAt_from_buffered_ftc {r : ℝ} (hr : 0 < r) (hrR : r < R)
    {p : Point n} (hp : p∈backward r) :
    HasFDerivAt (fun x : Space n => G (x,p.2)) (B p) p.1 :=
  (auto_spatial_from_buffered_ftc_on_backward hG hB hScalarFTC hGradientFTC hr hrR hp).2.1

theorem auto_spatialD_from_buffered_ftc {r : ℝ} (hr : 0 < r) (hrR : r < R)
    {p : Point n} (hp : p∈backward r) : spatialD u p=G p :=
  (auto_spatial_from_buffered_ftc_on_backward hG hB hScalarFTC hGradientFTC hr hrR hp).2.2.1

theorem auto_spatialDD_from_buffered_ftc {r : ℝ} (hr : 0 < r) (hrR : r < R)
    {p : Point n} (hp : p∈backward r) : spatialDD u p=B p :=
  (auto_spatial_from_buffered_ftc_on_backward hG hB hScalarFTC hGradientFTC hr hrR hp).2.2.2.1

theorem auto_spatialC2_from_buffered_ftc {r : ℝ} (hr : 0 < r) (hrR : r < R)
    {p : Point n} (hp : p∈backward r) : ContDiffAt ℝ 2 (fun x : Space n => u (x,p.2)) p.1 :=
  (auto_spatial_from_buffered_ftc_on_backward hG hB hScalarFTC hGradientFTC hr hrR hp).2.2.2.2

end Spatial
end Yau.LeafProofs.L05AutonomousAux
