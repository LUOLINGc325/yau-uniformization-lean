import Yau.Proofs.C04BoundedGeometryChartsCoordinateComponents
import Yau.LeafProofs.L21MatrixBounds

/-! Scalar component estimates control every jet of the same vector coordinate function. -/
noncomputable section
open scoped Topology ContDiff
namespace Yau.Proofs.C04ChartsAux
open Yau Yau.LeafProofs.L21Aux
variable {n : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 5

theorem coordinate_component_iteratedFDeriv (F : ComplexVector n → ComplexVector n)
    (hF : ContDiff ℝ ∞ F) (m : ℕ) (x : ComplexVector n) (k : Fin n)
    (V : Fin m → ComplexVector n) :
    iteratedFDeriv ℝ m (fun y => F y k) x V = iteratedFDeriv ℝ m F x V k := by
  let pr : ComplexVector n →L[ℝ] ℂ := (EuclideanSpace.proj k).restrictScalars ℝ
  have H := pr.iteratedFDeriv_comp_left (hF.contDiffAt (x := x)) (by simp : (m : ℕ∞ω) ≤ ∞)
  change (iteratedFDeriv ℝ m (pr ∘ F) x) V = pr (iteratedFDeriv ℝ m F x V)
  rw [H]
  rfl

theorem norm_vector_iteratedFDeriv_le_sum_components (F : ComplexVector n → ComplexVector n)
    (hF : ContDiff ℝ ∞ F) (m : ℕ) (x : ComplexVector n) :
    ‖iteratedFDeriv ℝ m F x‖ ≤ ∑ k : Fin n, ‖iteratedFDeriv ℝ m (fun y => F y k) x‖ := by
  apply ContinuousMultilinearMap.opNorm_le_bound (Finset.sum_nonneg fun k _ => norm_nonneg _)
  intro V
  calc
    ‖iteratedFDeriv ℝ m F x V‖ ≤ ∑ k : Fin n, ‖iteratedFDeriv ℝ m F x V k‖ :=
      euclidean_norm_le_sum_coordinates _
    _ = ∑ k : Fin n, ‖iteratedFDeriv ℝ m (fun y => F y k) x V‖ := by
      apply Finset.sum_congr rfl
      intro k _
      rw [coordinate_component_iteratedFDeriv F hF]
    _ ≤ ∑ k : Fin n, ‖iteratedFDeriv ℝ m (fun y => F y k) x‖ * ∏ i : Fin m, ‖V i‖ :=
      Finset.sum_le_sum (fun k _ => (iteratedFDeriv ℝ m (fun y => F y k) x).le_opNorm V)
    _ = (∑ k : Fin n, ‖iteratedFDeriv ℝ m (fun y => F y k) x‖) * ∏ i : Fin m, ‖V i‖ :=
      by rw [Finset.sum_mul]

theorem norm_vector_iteratedFDeriv_le_dimension (F : ComplexVector n → ComplexVector n)
    (hF : ContDiff ℝ ∞ F) (m : ℕ) (x : ComplexVector n) {D : ℝ}
    (hcomponents : ∀ k : Fin n, ‖iteratedFDeriv ℝ m (fun y => F y k) x‖ ≤ D) :
    ‖iteratedFDeriv ℝ m F x‖ ≤ (n : ℝ) * D := by
  exact (norm_vector_iteratedFDeriv_le_sum_components F hF m x).trans
    ((Finset.sum_le_sum (fun k _ => hcomponents k)).trans_eq (by simp))

end Yau.Proofs.C04ChartsAux
