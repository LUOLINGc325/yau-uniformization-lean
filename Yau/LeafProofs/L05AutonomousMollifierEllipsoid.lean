import Yau.LeafProofs.L05AutonomousMollifierTime
import Yau.LeafProofs.L05AutonomousEllipsoidViscosity

noncomputable section
open Filter Set MeasureTheory Matrix
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius BoundedContinuousFunction
namespace Yau.LeafProofs.L05AutonomousAux
open Yau.Parabolic Yau.LeafProofs.L05Aux

/-- The two genuine finite probability integrals commute before division by the second scale. -/
theorem auto_mollify_ellipsoid_second {n : ℕ} (B : Space n ≃L[ℝ] Space n) (r eps : ℝ)
    (heps : 0 < eps) (w : Point n →ᵇ ℝ) (hw : UniformContinuous (w : Point n → ℝ)) (p : Point n) :
    Integrable (fun y => autoEllipsoidSecond B r w (p.1-y,p.2)) (autoMollifierMeasure n eps heps) ∧
    autoEllipsoidSecond B r (autoSpatialMollify eps heps w) p =
      ∫ y, autoEllipsoidSecond B r w (p.1-y,p.2) ∂autoMollifierMeasure n eps heps := by
  let mu := autoLinearBallProbability B
  let nu := autoMollifierMeasure n eps heps
  let : IsProbabilityMeasure mu := autoLinearBallProbability_isProbability B
  let : IsProbabilityMeasure nu := autoMollifierMeasure_isProbability n eps heps
  have hc : Continuous (fun q : Space n × Space n => w (p.1+q.1-q.2,p.2)) :=
    w.continuous.comp (((continuous_const.add continuous_fst).sub continuous_snd).prodMk continuous_const)
  have hi : Integrable (fun q : Space n × Space n => w (p.1+q.1-q.2,p.2)) (mu.prod nu) :=
    Integrable.of_bound hc.stronglyMeasurable.aestronglyMeasurable ‖w‖
      (ae_of_all _ fun q => w.norm_coe_le_norm _)
  have hswap : (∫ z, (∫ y, w (p.1+z-y,p.2) ∂nu) ∂mu)=
      ∫ y, (∫ z, w (p.1+z-y,p.2) ∂mu) ∂nu := integral_integral_swap hi
  have hfun : (fun y => ∫ z, w (p.1+z-y,p.2) ∂mu)=
      (fun y => autoEllipsoidMean B w (p.1-y,p.2)) := by
    funext y
    apply integral_congr_ae
    exact ae_of_all _ fun z => by
      change w (p.1+z-y,p.2)=w (p.1-y+z,p.2)
      have heq : p.1+z-y=p.1-y+z := by abel
      rw [heq]
  have hmean : Integrable (fun y => autoEllipsoidMean B w (p.1-y,p.2)) nu := by
    rw [← hfun]
    exact hi.integral_prod_right
  have hcenter := autoSpatialMollify_time_slice_integrable eps heps w hw p.1 p.2
  have hsecond : Integrable (fun y => autoEllipsoidSecond B r w (p.1-y,p.2)) nu :=
    (hmean.sub hcenter).div_const _
  refine ⟨hsecond,?_⟩
  have hmeanEq : autoEllipsoidMean B (autoSpatialMollify eps heps w) p=
      ∫ y, autoEllipsoidMean B w (p.1-y,p.2) ∂nu := by
    change (∫ z, autoSpatialMollify eps heps w (p.1+z,p.2) ∂mu)=_
    simp_rw [autoSpatialMollify_integral_minus eps heps w hw]
    rw [hswap,hfun]
  change (autoEllipsoidMean B (autoSpatialMollify eps heps w) p-autoSpatialMollify eps heps w p)/r^2=_
  rw [hmeanEq,show autoSpatialMollify eps heps w p=∫ y, w (p.1-y,p.2) ∂nu from
    autoSpatialMollify_integral_minus eps heps w hw p.1 p.2,
    ← integral_sub hmean hcenter,← integral_div]
  rfl

/-- Actual source equality is used only at the center and at almost every genuine displacement. -/
theorem auto_ellipsoid_second_congr {n : ℕ} {K : Set (Point n)} {u v : Point n → ℝ}
    (huv : EqOn u v K) (B : Space n ≃L[ℝ] Space n) {b : ℝ}
    (hB : ‖B.toContinuousLinearMap‖ ≤ b) (r : ℝ) (p : Point n) (hp : p ∈ K)
    (hbuffer : ∀ z ∈ Metric.closedBall (0 : Space n) b, (p.1+z,p.2) ∈ K) :
    autoEllipsoidSecond B r u p=autoEllipsoidSecond B r v p := by
  have heq : autoEllipsoidMean B u p=autoEllipsoidMean B v p := by
    apply integral_congr_ae
    filter_upwards [autoLinearBallProbability_ball_ae B hB] with z hz
    exact huv (hbuffer z hz)
  exact congrArg₂ (fun a c => (a-c)/r^2) heq (huv hp)

end Yau.LeafProofs.L05AutonomousAux
