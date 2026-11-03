import Yau.LeafProofs.L05PerturbationPolynomialUpdate
import Yau.LeafProofs.L05PerturbationBilinearBounds

open Filter Set Metric
open scoped Topology InnerProductSpace Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05Aux
open Yau.Parabolic

theorem perturb_iter_quad_sub {n : ℕ} (A B : Sym n) (x : Space n) :
    perturbQuad (A-B) x=perturbQuad A x-perturbQuad B x := by
  simp only [perturbQuad,(selfAdjoint (Mat n)).coe_sub,Matrix.sub_apply,sub_mul,Finset.sum_sub_distrib]

theorem perturb_polynomial_sub {n : ℕ} (c1 c2 q1 q2 : ℝ)
    (b1 b2 : Space n →L[ℝ] ℝ) (A1 A2 : Sym n) (p : Point n) :
    perturbPolynomial c1 b1 A1 q1 p-perturbPolynomial c2 b2 A2 q2 p=
      perturbPolynomial (c1-c2) (b1-b2) (A1-A2) (q1-q2) p := by
  simp only [perturbPolynomial,sub_apply,perturb_iter_quad_sub]
  ring

theorem perturb_polynomial_evaluation_bound {n : ℕ} (c q : ℝ)
    (b : Space n →L[ℝ] ℝ) (A : Sym n) (p : Point n) :
    |perturbPolynomial c b A q p| ≤
      |c|+‖b‖*‖p.1‖+(1/2 : ℝ)*‖A‖*‖p.1‖^2+|q| *|p.2| := by
  have hB : |b p.1| ≤ ‖b‖*‖p.1‖ := by simpa only [Real.norm_eq_abs] using b.le_opNorm p.1
  have hA : |perturbQuad A p.1| ≤ ‖A‖*‖p.1‖^2 := by
    rw [perturbQuad_eq_bilinear]
    simpa only [Real.norm_eq_abs,pow_two,mul_assoc] using perturbBilinear_apply_norm_le A p.1 p.1
  have hHalf : |(1/2 : ℝ)*perturbQuad A p.1| ≤ (1/2 : ℝ)*‖A‖*‖p.1‖^2 := by
    rw [abs_mul,abs_of_nonneg (show 0 ≤ (1/2 : ℝ) by norm_num)]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hA (show 0 ≤ (1/2 : ℝ) by norm_num)
  calc
    _ ≤ |c+b p.1+(1/2 : ℝ)*perturbQuad A p.1|+|q*p.2| := abs_add_le _ _
    _ ≤ (|c+b p.1|+|(1/2 : ℝ)*perturbQuad A p.1|)+|q*p.2| := by linarith only [abs_add_le (c+b p.1) ((1/2 : ℝ)*perturbQuad A p.1)]
    _ ≤ (|c|+|b p.1|+|(1/2 : ℝ)*perturbQuad A p.1|)+|q*p.2| := by gcongr; exact abs_add_le _ _
    _ ≤ _ := by
      rw [abs_mul q p.2]
      linarith only [hB,hHalf]

theorem perturb_polynomial_closed_bound {n : ℕ} {r C B D Q : ℝ} (hr : 0 ≤ r)
    (c q : ℝ) (b : Space n →L[ℝ] ℝ) (A : Sym n)
    (hc : |c| ≤ C) (hb : ‖b‖ ≤ B) (hA : ‖A‖ ≤ D) (hq : |q| ≤ Q)
    {p : Point n} (hp : p∈perturbClosed (0 : Space n) r 0) :
    |perturbPolynomial c b A q p| ≤ C+B*r+(1/2 : ℝ)*D*r^2+Q*r^2 := by
  have hx : ‖p.1‖ ≤ r := by simpa only [mem_closedBall,dist_zero_right] using hp.1
  have ht : |p.2| ≤ r^2 := by
    rw [abs_of_nonpos hp.2.2]
    have hh := hp.2.1
    simp only [zero_sub] at hh
    linarith
  have hBn : 0 ≤ B := (norm_nonneg b).trans hb
  have hDn : 0 ≤ D := (norm_nonneg A).trans hA
  have hQn : 0 ≤ Q := (abs_nonneg q).trans hq
  have hbb : ‖b‖*‖p.1‖ ≤ B*r := mul_le_mul hb hx (norm_nonneg _) hBn
  have haa : (1/2 : ℝ)*‖A‖*‖p.1‖^2 ≤ (1/2 : ℝ)*D*r^2 := by gcongr
  have hqq : |q| * |p.2| ≤ Q*r^2 := mul_le_mul hq ht (abs_nonneg _) hQn
  exact (perturb_polynomial_evaluation_bound c q b A p).trans (by linarith)

end Yau.LeafProofs.L05Aux
