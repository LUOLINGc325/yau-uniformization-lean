import Yau.LeafProofs.L16DomainDataSource
import Yau.LeafProofs.L16ChartOperatorAlgebra

open MeasureTheory Filter Set
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic

theorem frobenius_norm_le_sum_abs {n : ℕ} (A : Mat n) :
    ‖A‖ ≤ ∑ i : Yau.RIdx n, ∑ j : Yau.RIdx n, |A i j| := by
  rw [Matrix.frobenius_norm_def,← Real.sqrt_eq_rpow]
  apply Real.sqrt_le_iff.mpr
  refine ⟨Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => abs_nonneg _)),?_⟩
  simp only [Real.norm_eq_abs,Real.rpow_two]
  calc
    _ ≤ ∑ i : Yau.RIdx n, (∑ j : Yau.RIdx n, |A i j|)^2 := by
      apply Finset.sum_le_sum
      intro i _
      exact Finset.sum_sq_le_sq_sum_of_nonneg (fun j _ => abs_nonneg (A i j))
    _ ≤ _ := Finset.sum_sq_le_sq_sum_of_nonneg
      (fun i _ => Finset.sum_nonneg (fun j _ => abs_nonneg (A i j)))

theorem holderBound_matrix_of_entries {n : ℕ} {α C : ℝ} {Q : Set (Point n)}
    {a : Point n → Mat n} (hC : 0 ≤ C)
    (ha : ∀ i j, HolderBound α Q (fun p => a p i j) C) :
    HolderBound α Q a ((Fintype.card (Yau.RIdx n) : ℝ)^2*C) := by
  refine ⟨by positivity,?_,?_⟩
  · intro p hp
    exact (frobenius_norm_le_sum_abs (a p)).trans (by
      calc
        _ ≤ ∑ i : Yau.RIdx n, ∑ j : Yau.RIdx n, C :=
          Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => by
            simpa only [Real.norm_eq_abs] using (ha i j).2.1 p hp))
        _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; ring)
  · intro p hp q hq
    exact (frobenius_norm_le_sum_abs (a p-a q)).trans (by
      calc
        _ ≤ ∑ i : Yau.RIdx n, ∑ j : Yau.RIdx n, C*holderWeight α p q :=
          Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => by
            simpa only [Real.norm_eq_abs,Matrix.sub_apply] using (ha i j).2.2 p hp q hq))
        _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; ring)

end Yau.LeafProofs.L16Aux
