import Yau.LeafProofs.L16ExpBoundaryLogEquation

/-! The actual exponential change of variable retains every coefficient
 derivative in its divergence flux, including the one-sided time face. -/

open Set
open scoped ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 2200000
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.LeafProofs.L16Aux Yau.LeafProofs.L16ExpBoundaryAux

theorem F05_exp_flux_divergence {n : ℕ} {O : Set (Space n)} (hO : IsOpen O)
    {a : Space n → Mat n} {w : Space n → ℝ} {x : Space n} (hx : x ∈ O)
    (ha : ∀ i j, DifferentiableAt ℝ (fun y => a y i j) x)
    (hw : ∀ y ∈ O, ContDiffAt ℝ 2 w y) (i : Yau.RIdx n) :
    d (fun y => ∑ j,(a y i j/Real.exp (w y))*d (fun z => Real.exp (w z)) y j) x i =
      ∑ j,(d (fun y => a y i j) x i*d w x j+
        a x i j*fderiv ℝ (fderiv ℝ w) x (Yau.realVec i) (Yau.realVec j)) := by
  have hh := log_flux_divergence hO hx ha (fun y hy => (hw y hy).exp)
    (fun y _ => Real.exp_ne_zero (w y)) i
  simpa only [Real.log_exp] using hh

theorem F05_timeD_exp {n : ℕ} {D : Set (Space n)} {T : ℝ} (hT : 0 < T)
    {w : Point n → ℝ} (hw : C2 (cylinder D 0 T) w) {p : Point n}
    (hp : p ∈ cylinder D 0 T) :
    timeD (cylinder D 0 T) (fun q => Real.exp (w q)) p =
      Real.exp (w p)*timeD (cylinder D 0 T) w p := by
  have hFiber : {r | (p.1,r) ∈ cylinder D 0 T} = Icc 0 T := by ext r; exact and_iff_right hp.1
  have hTime : HasDerivWithinAt (fun t => w (p.1,t))
      (timeD (cylinder D 0 T) w p) (Icc 0 T) p.2 := by
    simpa only [timeD,hFiber] using (hw.2.2.2.2.2 p hp).hasDerivWithinAt
  have hExp := hTime.exp.derivWithin (uniqueDiffOn_Icc hT p.2 hp.2)
  simpa only [timeD,hFiber,Prod.eta] using hExp

end Yau.Proofs.F05Aux
