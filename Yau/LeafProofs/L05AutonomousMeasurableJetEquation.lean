import Yau.LeafProofs.L05AutonomousMeasurableJetGeometry

noncomputable section
open Filter Set MeasureTheory Asymptotics
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05AutonomousAux
open Yau.Parabolic Yau.LeafProofs.L05Aux

/-- Only actual spatial neighborhood equality is used to transfer the Peano
remainder from the compact extension to the original solution. -/
theorem auto_measurableJet_original_peano {n : ℕ} {u w : Point n → ℝ}
    (hwu : EqOn w u (unitClosed n)) {p : Point n}
    (hp : p ∈ autoOpen (0 : Space n) (5/8) 0)
    (l : Space n →L[ℝ] ℝ) (B : Space n →L[ℝ] Space n →L[ℝ] ℝ)
    (hRem : (fun y => w (y,p.2)-w p-l (y-p.1)-(1/2 : ℝ)*B (y-p.1) (y-p.1))
      =o[𝓝 p.1] (fun y => ‖y-p.1‖^2)) :
    (fun y => u (y,p.2)-u p-l (y-p.1)-(1/2 : ℝ)*B (y-p.1) (y-p.1))
      =o[𝓝 p.1] (fun y => ‖y-p.1‖^2) := by
  have hx : ‖p.1‖ < 1 :=
    (show ‖p.1‖ < 5/8 by simpa only [Metric.mem_ball,dist_zero_right] using hp.1).trans (by norm_num)
  have ht : p.2 ∈ Icc (-1 : ℝ) 0 := ⟨by linarith only [hp.2.1],hp.2.2.le⟩
  have hpU := auto_measurableJet_open_unitClosed (by norm_num : (0 : ℝ) < 5/8)
    (by norm_num : (5/8 : ℝ) < 1) hp
  have hEq := auto_unit_spatial_eventuallyEq hwu hx ht
  refine hRem.congr' ?_ (Eventually.of_forall fun _ => rfl)
  filter_upwards [hEq] with y hy
  rw [hy,hwu hpU]

/-- The genuine Peano-point equation is applied only on the open interior
cylinder. No assertion of a PDE at the terminal face is made. -/
theorem auto_measurableJet_point_equation {n : ℕ} {u w V : Point n → ℝ} {F : Sym n → ℝ}
    (hwu : EqOn w u (unitClosed n)) (hF : Continuous F)
    (hu : ContinuousOn u (unitClosed n))
    (hV : ContinuousOn V (autoOpen (0 : Space n) (5/8) 0))
    (hTime : ∀ q ∈ autoOpen (0 : Space n) (5/8) 0,
      HasDerivAt (fun t => u (q.1,t)) (V q) q.2)
    (hsol : viscositySolution (unitOpen n) (fun H _ => F H) (fun _ => 0) u)
    {p : Point n} (hp : p ∈ autoOpen (0 : Space n) (5/8) 0)
    (hRem : (fun y => w (y,p.2)-w p-spatialD w p (y-p.1)-
      (1/2 : ℝ)*autoBilinearMap n (peanoMeasurableHessian w p) (y-p.1) (y-p.1))
      =o[𝓝 p.1] (fun y => ‖y-p.1‖^2)) : F (peanoMeasurableHessian w p)=V p := by
  have hQU := autoOpen_subset_unitOpen (n := n) (by norm_num : (0 : ℝ) < 5/8)
    (by norm_num : (5/8 : ℝ) < 1)
  have hQC := auto_measurableJet_open_unitClosed (n := n) (by norm_num : (0 : ℝ) < 5/8)
    (by norm_num : (5/8 : ℝ) < 1)
  have hSolQ : viscositySolution (autoOpen (0 : Space n) (5/8) 0)
      (fun H _ => F H) (fun _ => 0) u :=
    ⟨viscositySub_mono_domain hsol.1 hQU,viscositySuper_mono_domain hsol.2 hQU⟩
  have hRemU := auto_measurableJet_original_peano hwu hp (spatialD w p)
    (autoBilinearMap n (peanoMeasurableHessian w p)) hRem
  have hEquation := auto_peano_residual_eq (autoOpen_isOpen 0 (5/8) 0) hF
    (hu.mono hQC) hV hTime hSolQ hp (spatialD w p)
    (autoBilinearMap n (peanoMeasurableHessian w p))
    (autoBilinearMap_symmetric (peanoMeasurableHessian w p)) hRemU
  rw [auto_measurableJet_sym_bilinear] at hEquation
  exact hEquation.symm

end Yau.LeafProofs.L05AutonomousAux
