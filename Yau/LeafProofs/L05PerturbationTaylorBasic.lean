import Yau.LeafProofs.L05PerturbationBilinearBounds
import Yau.LeafProofs.L05PerturbationWeights
import Mathlib.Analysis.Calculus.MeanValue

open Filter MeasureTheory Set Metric
open scoped Topology ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05Aux
open Yau.Parabolic

def perturbTaylor {n : ℕ} (Q : Set (Point n)) (u : Point n → ℝ) (z p : Point n) : ℝ :=
  u z+spatialD u z (p.1-z.1)+(1/2 : ℝ)*spatialDD u z (p.1-z.1) (p.1-z.1)+
    timeD Q u z*(p.2-z.2)

theorem perturb_taylor_origin_polynomial {n : ℕ} {Q : Set (Point n)} {u : Point n → ℝ}
    (hu : C2 Q u) (h0 : (0 : Point n)∈Q) (p : Point n) :
    perturbTaylor Q u 0 p=perturbPolynomial (u 0) (spatialD u 0) (hessian u 0) (timeD Q u 0) p := by
  simp only [perturbTaylor,perturbPolynomial,Prod.fst_zero,Prod.snd_zero,sub_zero,
    perturb_spatialDD_eq_bilinear hu h0,perturbQuad_eq_bilinear]

theorem perturb_small_closed_subset_quarter {n : ℕ} {r : ℝ} (hr : 0 < r) (hrb : r ≤ 1/8) :
    perturbClosed (0 : Space n) r 0 ⊆ backward (1/4) := by
  intro p hp
  have hx : ‖p.1‖ ≤ r := by simpa only [mem_closedBall,dist_zero_right] using hp.1
  have ht : -r^2 ≤ p.2 := by simpa only [zero_sub] using hp.2.1
  refine ⟨?_,?_,hp.2.2⟩
  · change dist p.1 0 < 1/4
    rw [dist_zero_right]
    linarith
  · change -(1/4 : ℝ)^2 < p.2
    nlinarith

theorem perturb_quarter_origin {n : ℕ} : (0 : Point n)∈backward (1/4) := by
  norm_num [backward]

theorem perturb_spatial_second_holder_at_zero {n : ℕ} {sigma C r : ℝ}
    (hs : 0 < sigma) {u : Point n → ℝ} (hh : SchauderBound sigma (backward (1/4)) u C)
    (hr : 0 < r) (hrb : r ≤ 1/8) {x : Space n} (hx : x∈closedBall 0 r) :
    ‖spatialDD u (x,0)-spatialDD u 0‖ ≤ C*r^sigma := by
  have hp : (x,(0 : ℝ))∈perturbClosed (0 : Space n) r 0 :=
    ⟨hx,sub_le_self _ (sq_nonneg _),le_rfl⟩
  have hH := hh.2.2.2.1.2.2 (x,0) (perturb_small_closed_subset_quarter hr hrb hp) 0 perturb_quarter_origin
  simp only [holderWeight,Prod.fst_zero,Prod.snd_zero,sub_zero,sub_self,abs_zero,
    Real.zero_rpow (show sigma/2≠0 by positivity),add_zero] at hH
  exact hH.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (norm_nonneg x) (by simpa only [mem_closedBall,dist_zero_right] using hx) hs.le) hh.2.1)

theorem perturb_time_holder_at_zero {n : ℕ} {sigma C r : ℝ}
    (hs : 0 < sigma) {u : Point n → ℝ} (hh : SchauderBound sigma (backward (1/4)) u C)
    (hr : 0 < r) (hrb : r ≤ 1/8) {p : Point n} (hp : p∈perturbClosed (0 : Space n) r 0) :
    ‖timeD (backward (1/4)) u p-timeD (backward (1/4)) u 0‖ ≤ 2*C*r^sigma := by
  have hH := hh.2.2.2.2.2.2 p (perturb_small_closed_subset_quarter hr hrb hp) 0 perturb_quarter_origin
  have hx : ‖p.1‖ ≤ r := by simpa only [mem_closedBall,dist_zero_right] using hp.1
  have ht : |p.2| ≤ r^2 := by
    rw [abs_of_nonpos hp.2.2]
    have htLo : -r^2 ≤ p.2 := by simpa only [zero_sub] using hp.2.1
    linarith
  have hSpace := Real.rpow_le_rpow (norm_nonneg p.1) hx hs.le
  have hTime := Real.rpow_le_rpow (abs_nonneg p.2) ht (show 0 ≤ sigma/2 by positivity)
  have hPower : (r^2)^(sigma/2)=r^sigma := by
    rw [← Real.rpow_natCast_mul hr.le 2]
    congr 1
    norm_num
    ring
  rw [hPower] at hTime
  simp only [holderWeight,Prod.fst_zero,Prod.snd_zero,sub_zero] at hH
  have hW := mul_le_mul_of_nonneg_left (add_le_add hSpace hTime) hh.2.1
  exact hH.trans (by nlinarith only [hW])

end Yau.LeafProofs.L05Aux
