import Yau.LeafProofs.L05AutonomousBallMeanCutoffDerivatives
import Yau.LeafProofs.L05AutonomousBallMeanError

open Set Filter MeasureTheory Metric
open scoped Topology ContDiff
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05AutonomousAux

def autoGreenCutoffProduct (r eta s : ℝ) : ℝ := autoGreenInner eta s*autoGreenOuter r eta s

theorem auto_green_cutoff_product_contDiff {eta : ℝ} (heta : 0 < eta) (r : ℝ) :
    ContDiff ℝ ∞ (autoGreenCutoffProduct r eta) :=
  (auto_green_inner_contDiff eta).mul (auto_green_outer_contDiff heta r)

theorem auto_green_product_deriv (d : ℕ) (omega : ℝ) {r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    {q : ℝ → ℝ} (hq : ContDiff ℝ ∞ q) :
    deriv (fun t : ℝ => autoGreenPrimitive d omega r t*q t) s=
      (-autoGreenIntegrand d r s/((d : ℝ)*omega))*q s+autoGreenPrimitive d omega r s*deriv q s :=
  ((auto_green_primitive_hasDerivAt d omega hr hs).mul
    (contDiff_infty_iff_deriv.mp hq).1.differentiableAt.hasDerivAt).deriv

theorem auto_green_product_second (d : ℕ) (omega : ℝ) {r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    {q : ℝ → ℝ} (hq : ContDiff ℝ ∞ q) :
    deriv (deriv (fun t : ℝ => autoGreenPrimitive d omega r t*q t)) s=
      (-((1-(d : ℝ))*s^(-(d : ℝ))-1/r^d)/((d : ℝ)*omega))*q s+
      2*(-autoGreenIntegrand d r s/((d : ℝ)*omega))*deriv q s+
      autoGreenPrimitive d omega r s*deriv (deriv q) s := by
  have hEq : deriv (fun t : ℝ => autoGreenPrimitive d omega r t*q t)=ᶠ[𝓝 s]
      (fun t : ℝ => (-autoGreenIntegrand d r t/((d : ℝ)*omega))*q t+
        autoGreenPrimitive d omega r t*deriv q t) := by
    filter_upwards [isOpen_Ioi.mem_nhds hs] with t ht
    exact auto_green_product_deriv d omega hr ht hq
  rw [hEq.deriv_eq]
  have hK := auto_green_primitive_hasDerivAt d omega hr hs
  have hD := (auto_greenIntegrand_hasDerivAt d (r := r) hs).neg.div_const ((d : ℝ)*omega)
  have hqD : HasDerivAt q (deriv q s) s := (contDiff_infty_iff_deriv.mp hq).1.differentiableAt.hasDerivAt
  have hqDD : HasDerivAt (deriv q) (deriv (deriv q) s) s :=
    (contDiff_infty_iff_deriv.mp (contDiff_infty_iff_deriv.mp hq).2).1.differentiableAt.hasDerivAt
  have h := ((hD.mul hqD).add (hK.mul hqDD)).deriv
  simp only [Pi.neg_apply] at h
  convert! h using 1 <;> ring

theorem auto_green_test_scalar_laplacian {d : ℕ} (hd : 0 < d) {omega r eta s : ℝ}
    (hOmega : 0 < omega) (hr : 0 < r) (heta : 0 < eta) (hs : s∈Ioo 0 r) :
    deriv (deriv (autoGreenTest d omega r eta)) s+
      ((d : ℝ)-1)/s*deriv (autoGreenTest d omega r eta) s=
      autoGreenCutoffProduct r eta s/(omega*r^d)+
      autoGreenCutoffError d omega r s (deriv (autoGreenCutoffProduct r eta) s)
        (deriv (deriv (autoGreenCutoffProduct r eta)) s) := by
  let q := autoGreenCutoffProduct r eta
  have hq : ContDiff ℝ ∞ q := auto_green_cutoff_product_contDiff heta r
  have hEq : autoGreenTest d omega r eta=ᶠ[𝓝 s]
      (fun t : ℝ => autoGreenPrimitive d omega r t*q t) := by
    filter_upwards [isOpen_Ioo.mem_nhds hs] with t ht
    simp only [autoGreenTest,autoRadialGreen,ite_eq_left (show 0 < t ∧ t < r from ht),q,
      autoGreenCutoffProduct,mul_assoc]
  rw [hEq.deriv_eq,hEq.deriv.deriv_eq,auto_green_product_deriv d omega hr hs.1 hq,
    auto_green_product_second d omega hr hs.1 hq]
  have hLap := auto_green_radial_laplacian hd hOmega hr hs.1
  have hLap' : -((1-(d : ℝ))*s^(-(d : ℝ))-1/r^d)/((d : ℝ)*omega)+
      ((d : ℝ)-1)/s*(-autoGreenIntegrand d r s/((d : ℝ)*omega))=1/(omega*r^d) := by
    convert hLap using 1 <;> ring
  change _=q s/(omega*r^d)+_
  dsimp only [autoGreenCutoffError]
  calc
    _ = (-((1-(d : ℝ))*s^(-(d : ℝ))-1/r^d)/((d : ℝ)*omega)+
        ((d : ℝ)-1)/s*(-autoGreenIntegrand d r s/((d : ℝ)*omega)))*q s+
        (autoGreenPrimitive d omega r s*deriv (deriv q) s+
        2*(-autoGreenIntegrand d r s/((d : ℝ)*omega))*deriv q s+
        ((d : ℝ)-1)/s*autoGreenPrimitive d omega r s*deriv q s) := by ring
    _ = _ := by rw [hLap']; ring

end Yau.LeafProofs.L05AutonomousAux
