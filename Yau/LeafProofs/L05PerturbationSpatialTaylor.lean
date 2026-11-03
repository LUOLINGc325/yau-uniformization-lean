import Yau.LeafProofs.L05PerturbationTaylorBasic

open Filter MeasureTheory Set Metric
open scoped Topology ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05Aux
open Yau.Parabolic

theorem perturb_spatial_taylor_remainder {n : ℕ} {sigma C r : ℝ}
    (hs : 0 < sigma) {u : Point n → ℝ} (hh : SchauderBound sigma (backward (1/4)) u C)
    (hr : 0 < r) (hrb : r ≤ 1/8) {x : Space n} (hx : x∈closedBall 0 r) :
    |u (x,0)-perturbPolynomial (u 0) (spatialD u 0) (hessian u 0) 0 (x,0)| ≤ C*r^sigma*r^2 := by
  let b := spatialD u (0 : Point n)
  let B := perturbBilinear (hessian u (0 : Point n))
  let G : Space n → Space n →L[ℝ] ℝ := fun y => spatialD u (y,0)-b-B y
  let P := perturbPolynomial (u 0) b (hessian u 0) 0
  let f : Space n → ℝ := fun y => u (y,0)-P (y,0)
  have hNonneg : 0 ≤ C*r^sigma := mul_nonneg hh.2.1 (Real.rpow_nonneg hr.le sigma)
  have hPoint (y : Space n) (hy : y∈closedBall 0 r) : (y,(0 : ℝ))∈backward (1/4) :=
    perturb_small_closed_subset_quarter hr hrb ⟨hy,sub_le_self _ (sq_nonneg _),le_rfl⟩
  have hB : B=spatialDD u (0 : Point n) :=
    (perturb_spatialDD_eq_bilinear hh.1 perturb_quarter_origin).symm
  have hGD (y : Space n) (hy : y∈closedBall 0 r) :
      HasFDerivAt G (spatialDD u (y,0)-B) y := by
    have hd : DifferentiableAt ℝ (fun z => spatialD u (z,0)) y := by
      exact ((hh.1.2.2.2.2.1 (y,0) (hPoint y hy)).fderiv_right (m := 1)
        (by norm_num)).differentiableAt (by norm_num)
    convert! (hd.hasFDerivAt.sub_const b).sub B.hasFDerivAt using 1
  have hGBound (y : Space n) (hy : y∈closedBall 0 r) :
      ‖spatialDD u (y,0)-B‖ ≤ C*r^sigma := by
    rw [hB]
    exact perturb_spatial_second_holder_at_zero hs hh hr hrb hy
  have hG0 : G 0=0 := by
    simp only [G,b,map_zero,sub_zero]
    change spatialD u (0 : Point n)-spatialD u 0=0
    exact sub_self _
  have hGNorm (y : Space n) (hy : y∈closedBall 0 r) : ‖G y‖ ≤ C*r^sigma*r := by
    have hMean := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
      (fun z hz => (hGD z hz).hasFDerivWithinAt) hGBound
      (convex_closedBall (0 : Space n) r) (mem_closedBall_self hr.le) hy
    rw [hG0,sub_zero,sub_zero] at hMean
    exact hMean.trans (mul_le_mul_of_nonneg_left
      (by simpa only [mem_closedBall,dist_zero_right] using hy) hNonneg)
  have hfD (y : Space n) (hy : y∈closedBall 0 r) : HasFDerivAt f (G y) y := by
    have hd := (hh.1.2.2.2.2.1 (y,0) (hPoint y hy)).differentiableAt (by norm_num)
    have hPoly := perturb_polynomial_spatial_hasFDerivAt (u 0) b (hessian u 0) 0 0 y
    convert! hd.hasFDerivAt.sub hPoly using 1
    ext z
    change (spatialD u (y,0)-b-B y) z=(spatialD u (y,0)-(b+B y)) z
    congr 1
    abel
  have hf0 : f 0=0 := by
    simp only [f,P,perturbPolynomial,map_zero,add_zero,perturbQuad_eq_bilinear,mul_zero]
    change u (0 : Point n)-u 0=0
    exact sub_self _
  have hMean := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun y hy => (hfD y hy).hasFDerivWithinAt) hGNorm
    (convex_closedBall (0 : Space n) r) (mem_closedBall_self hr.le) hx
  rw [hf0,sub_zero,sub_zero,Real.norm_eq_abs] at hMean
  have hxN : ‖x‖ ≤ r := by simpa only [mem_closedBall,dist_zero_right] using hx
  have hEnd := hMean.trans (mul_le_mul_of_nonneg_left hxN (mul_nonneg hNonneg hr.le))
  change |f x| ≤ C*r^sigma*r^2
  exact hEnd.trans_eq (by ring)

end Yau.LeafProofs.L05Aux
