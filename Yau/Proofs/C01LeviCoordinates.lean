import Yau.Proofs.C01ScalarHarnack

/-! Coordinate expansion of the actual Wirtinger directions, also for
complex-valued metric entries, used in the original bisectional curvature. -/

noncomputable section

open scoped Topology ContDiff

namespace Yau.NodeProofs.C01Aux

open Yau
open Yau.Blueprint.Alignment.Y03Proof

theorem wirtBar_stdVec_sum {n : ℕ} (f : ComplexVector n → ℂ)
    (z v : ComplexVector n) :
    wirtBar f z v = ∑ i, star (v i) * wirtBar f z (stdVec i) := by
  have hsum : (∑ i, v i • stdVec i) = v := by
    ext i
    simp [stdVec, EuclideanSpace.single, Pi.single_apply]
  calc
    _ = wirtBar f z (∑ i, v i • stdVec i) := congrArg (wirtBar f z) hsum.symm
    _ = ∑ i, wirtBar f z (v i • stdVec i) := wirtBar_sum_dir Finset.univ f z _
    _ = _ := Finset.sum_congr rfl fun i _ => wirtBar_complex_smul_dir f z (stdVec i) (v i)

theorem complex_mixedLevi_stdVec_sum {n : ℕ} (f : ComplexVector n → ℂ)
    (z v : ComplexVector n) (hf : ContDiffAt ℝ 2 f z) :
    wirt (fun p => wirtBar f p v) z v =
      ∑ k, ∑ l, v k * star (v l) *
        wirt (fun p => wirtBar f p (stdVec l)) z (stdVec k) := by
  have hinner : (fun p => wirtBar f p v) =
      (fun p => ∑ l, star (v l) * wirtBar f p (stdVec l)) :=
    funext fun p => wirtBar_stdVec_sum f p v
  have hd (l : Fin n) : DifferentiableAt ℝ (fun p => wirtBar f p (stdVec l)) z :=
    (wirtBar_contDiffAt hf (stdVec l)).differentiableAt (by norm_num)
  have hsum := wirt_sum_fn Finset.univ (fun l p => star (v l) * wirtBar f p (stdVec l))
    (fun l _ => (hd l).const_mul (star (v l))) v
  rw [hinner, hsum]
  calc
    _ = ∑ l, star (v l) * wirt (fun p => wirtBar f p (stdVec l)) z v := by
      apply Finset.sum_congr rfl
      intro l _
      exact wirt_const_mul_fn (hd l) v (star (v l))
    _ = ∑ l, ∑ k, star (v l) * v k *
        wirt (fun p => wirtBar f p (stdVec l)) z (stdVec k) := by
      apply Finset.sum_congr rfl
      intro l _
      rw [wirt_stdVec_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro l _
      ring

end Yau.NodeProofs.C01Aux
