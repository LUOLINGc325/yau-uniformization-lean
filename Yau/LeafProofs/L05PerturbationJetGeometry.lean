import Yau.LeafProofs.L05PerturbationHolderGeometry
import Yau.LeafProofs.L05PerturbationTaylorBasic

open Filter Set Metric
open scoped Topology ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05Aux
open Yau.Parabolic

theorem perturb_common_cylinder {n : ℕ} (z w : Point n) :
    perturbClosed z.1 (parabolicDistance z w) (min z.2 w.2) ⊆
      perturbClosed z.1 (4*parabolicDistance z w) z.2 ∩
        perturbClosed w.1 (4*parabolicDistance z w) w.2 := by
  let d := parabolicDistance z w
  have hd : 0 ≤ d := perturb_distance_nonneg z w
  have hx : ‖z.1-w.1‖ ≤ d := le_add_of_nonneg_right (Real.sqrt_nonneg _)
  have ht : |z.2-w.2| ≤ d^2 := by
    have hs := Real.sq_sqrt (abs_nonneg (z.2-w.2))
    have hn := norm_nonneg (z.1-w.1)
    have hrt := Real.sqrt_nonneg |z.2-w.2|
    dsimp only [d,parabolicDistance]
    nlinarith only [hs,hn,hrt]
  have hMinZ : z.2-d^2 ≤ min z.2 w.2 := by
    apply le_min
    · linarith only [sq_nonneg d]
    · linarith only [(le_abs_self (z.2-w.2)).trans ht]
  have hMinW : w.2-d^2 ≤ min z.2 w.2 := by
    apply le_min
    · have hh : w.2-z.2 ≤ d^2 := by
        have hAbs : w.2-z.2 ≤ |z.2-w.2| := by
          simpa only [neg_sub] using neg_le_abs (z.2-w.2)
        exact hAbs.trans ht
      linarith only [hh]
    · linarith only [sq_nonneg d]
  intro p hp
  have hpX : ‖p.1-z.1‖ ≤ d := by simpa only [mem_closedBall,dist_eq_norm] using hp.1
  have hpWX : ‖p.1-w.1‖ ≤ 2*d := by
    have hTri : ‖p.1-w.1‖ ≤ ‖p.1-z.1‖+‖z.1-w.1‖ := by
      simpa only [sub_add_sub_cancel] using norm_add_le (p.1-z.1) (z.1-w.1)
    linarith only [hTri,hpX,hx]
  have hpT : min z.2 w.2-d^2 ≤ p.2 := hp.2.1
  refine ⟨⟨?_,?_,hp.2.2.trans (min_le_left _ _)⟩,⟨?_,?_,hp.2.2.trans (min_le_right _ _)⟩⟩
  · change dist p.1 z.1 ≤ 4*d
    rw [dist_eq_norm]
    linarith only [hpX,hd]
  · change z.2-(4*d)^2 ≤ p.2
    nlinarith only [hMinZ,hpT,sq_nonneg d]
  · change dist p.1 w.1 ≤ 4*d
    rw [dist_eq_norm]
    linarith only [hpWX,hd]
  · change w.2-(4*d)^2 ≤ p.2
    nlinarith only [hMinW,hpT,sq_nonneg d]

def perturbTaylorConstant {n : ℕ} (Q : Set (Point n)) (u : Point n → ℝ) (z : Point n) : ℝ :=
  u z-spatialD u z z.1+(1/2 : ℝ)*spatialDD u z z.1 z.1-timeD Q u z*z.2

def perturbTaylorLinear {n : ℕ} (u : Point n → ℝ) (z : Point n) : Space n →L[ℝ] ℝ :=
  spatialD u z-spatialDD u z z.1

theorem perturb_taylor_global_polynomial {n : ℕ} {Q : Set (Point n)} {u : Point n → ℝ}
    (hu : C2 Q u) {z : Point n} (hz : z∈Q) (p : Point n) :
    perturbTaylor Q u z p=perturbPolynomial (perturbTaylorConstant Q u z)
      (perturbTaylorLinear u z) (hessian u z) (timeD Q u z) p := by
  simp only [perturbTaylor,perturbPolynomial,perturbTaylorConstant,perturbTaylorLinear,
    perturb_spatialDD_eq_bilinear hu hz,perturbQuad_eq_bilinear,map_sub,sub_apply]
  rw [perturbBilinear_symmetric (hessian u z) p.1 z.1]
  ring

end Yau.LeafProofs.L05Aux
