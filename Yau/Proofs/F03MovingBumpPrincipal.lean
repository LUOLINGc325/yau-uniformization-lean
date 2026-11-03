import Yau.Proofs.F03MovingBumpHessian
import Yau.LeafProofs.L19HeatRegularityEllipticity

/-! Actual matrix contraction of the cubic Hessian in the real chart basis. -/
noncomputable section
open scoped Topology InnerProductSpace
namespace Yau.Proofs.F03Aux
open Yau Parabolic LeafProofs.L12Aux LeafProofs.L16Aux
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

theorem real_basis_trace_contraction {n : ℕ} (A : Mat n) :
    (∑ i, ∑ j, A i j*inner ℝ (realVec i) (realVec j))=∑ i, A i i := by
  classical
  simp only [real_inner_realVec,realCoord_realVec,mul_ite,mul_one,mul_zero,
    Finset.sum_ite_eq,Finset.mem_univ,ite_true]

theorem movingBallBump_principal {n : ℕ} (A : Mat n)
    (R : ℝ) (c : ℝ → Space n) (p : Point n) :
    (∑ i, ∑ j, A i j*spatialDD (movingBallBump R c) p (realVec i) (realVec j)) =
      24*positivePower 1 (R^2-‖p.1-c p.2‖^2)*
        (∑ i, ∑ j, A i j*realCoord (p.1-c p.2) i*realCoord (p.1-c p.2) j) -
      6*positivePower 2 (R^2-‖p.1-c p.2‖^2)*(∑ i, A i i) := by
  rw [← real_basis_trace_contraction A]
  simp only [Finset.mul_sum,spatialDD]
  simp_rw [movingBallBump_space_hessian,real_inner_realVec]
  simp only [mul_sub,Finset.sum_sub_distrib]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  · apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring

end Yau.Proofs.F03Aux
