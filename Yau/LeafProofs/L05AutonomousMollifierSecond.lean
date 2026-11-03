import Yau.LeafProofs.L05AutonomousMollifierTime
import Yau.LeafProofs.L05AutonomousSecondLimit

noncomputable section
open Filter Set MeasureTheory Matrix
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius BoundedContinuousFunction
namespace Yau.LeafProofs.L05AutonomousAux
open Yau.Parabolic

/-- Every finite second difference commutes exactly with the genuine smoothing integral. -/
theorem auto_mollify_second {n : ℕ} (eps : ℝ) (heps : 0 < eps)
    (w : Point n →ᵇ ℝ) (hw : UniformContinuous (w : Point n → ℝ)) (e : Space n) (h : ℝ) (p : Point n) :
    Integrable (fun y => autoSecond w e h (p.1-y,p.2)) (autoMollifierMeasure n eps heps) ∧
    autoSecond (autoSpatialMollify eps heps w) e h p=
      ∫ y, autoSecond w e h (p.1-y,p.2) ∂autoMollifierMeasure n eps heps := by
  let nu := autoMollifierMeasure n eps heps
  have hplus := autoSpatialMollify_time_slice_integrable eps heps w hw (p.1+h • e) p.2
  have hminus := autoSpatialMollify_time_slice_integrable eps heps w hw (p.1-h • e) p.2
  have hcenter := autoSpatialMollify_time_slice_integrable eps heps w hw p.1 p.2
  have heq : (fun y => (w (p.1+h • e-y,p.2)+w (p.1-h • e-y,p.2)-2*w (p.1-y,p.2))/h^2)=
      (fun y => autoSecond w e h (p.1-y,p.2)) := by
    funext y
    have hp : p.1+h • e-y=p.1-y+h • e := by abel
    have hm : p.1-h • e-y=p.1-y-h • e := by abel
    simp only [autoSecond,hp,hm]
  have hsum : Integrable (fun y => w (p.1+h • e-y,p.2)+w (p.1-h • e-y,p.2)) nu := hplus.add hminus
  have hi := (hsum.sub (hcenter.const_mul 2)).div_const (h^2)
  change Integrable (fun y => (w (p.1+h • e-y,p.2)+w (p.1-h • e-y,p.2)-2*w (p.1-y,p.2))/h^2) nu at hi
  rw [heq] at hi
  refine ⟨hi,?_⟩
  change (autoSpatialMollify eps heps w (p.1+h • e,p.2)+autoSpatialMollify eps heps w (p.1-h • e,p.2)-
    2*autoSpatialMollify eps heps w p)/h^2=_
  rw [autoSpatialMollify_integral_minus eps heps w hw (p.1+h • e) p.2,
    autoSpatialMollify_integral_minus eps heps w hw (p.1-h • e) p.2,
    autoSpatialMollify_integral_minus eps heps w hw p.1 p.2,
    ← integral_add hplus hminus,← integral_const_mul,← integral_sub hsum (hcenter.const_mul 2),
    ← integral_div]
  exact congrArg (fun f : Space n → ℝ => ∫ y, f y ∂nu) heq

end Yau.LeafProofs.L05AutonomousAux
