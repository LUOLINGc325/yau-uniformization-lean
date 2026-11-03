import Yau.Proofs.Y03FiniteGraphs
import Yau.Proofs.Y03WeightLevels
import Yau.Proofs.Y03RowSpace

/-! The finite weight flag gives compatible lifts at every real threshold with a uniform O(n C) bound. -/

noncomputable section

namespace Yau.Blueprint.Alignment.Y03Proof

open Yau

variable {n : ℕ}

theorem exists_threshold_graphs (wold wnew : Fin n → ℝ) (B : Herm n) {C : ℝ} (hC : 0 ≤ C)
    (hprojection : ∀ r, r < (weightValueSet wold).card →
      ∀ a : selectedRowSpace B (newWeightLevel wold wnew r),
        ‖a‖ ≤ C * ‖coordinateProjectionOnto (oldWeightLevel wold r) a‖) :
    ∃ T : (x : ℝ) → coordinateSubspace (lowerWeightSet wold x) →L[ℂ] ComplexVector n,
      (∀ x, (coordinateProjectionOnto (lowerWeightSet wold x)).comp (T x) =
        ContinuousLinearMap.id ℂ (coordinateSubspace (lowerWeightSet wold x))) ∧
      (∀ x y, x ≤ y → LinearMap.range (T x).toLinearMap ≤ LinearMap.range (T y).toLinearMap) ∧
      (∀ x, selectedRowSpace B (lowerWeightSet wnew x) ≤ LinearMap.range (T x).toLinearMap) ∧
      ∀ x, ‖T x‖ ≤ 1 + (n : ℝ) * C := by
  let m := (weightValueSet wold).card
  let s := oldWeightLevel wold
  let A := fun r => selectedRowSpace B (newWeightLevel wold wnew r)
  have hstop : s m = Finset.univ := oldWeightLevel_top wold le_rfl
  have hbase : CoordinateGraph (s m) (A m) 1 := by
    refine ⟨(coordinateSubspace (s m)).subtypeL, coordinateProjectionOnto_right_inverse _, ?_, ?_⟩
    · intro a _
      refine ⟨⟨a, ?_⟩, rfl⟩
      intro i hi
      exact (hi (by rw [hstop]; exact Finset.mem_univ i)).elim
    · refine (coordinateSubspace (s m)).subtypeL.opNorm_le_bound zero_le_one ?_
      intro v
      change ‖(v : ComplexVector n)‖ ≤ 1 * ‖v‖
      rw [one_mul]
      exact le_rfl
  obtain ⟨G, hG⟩ := exists_finite_nested_graphs s A hC
    (fun r _ => oldWeightLevel_mono wold (Nat.le_succ r))
    (fun r _ => selectedRowSpace_mono B (newWeightLevel_mono wold wnew (Nat.le_succ r))) hprojection hbase
  have hGmono : Monotone (fun r => LinearMap.range (G r).lift.toLinearMap) :=
    Fin.monotone_iff_le_succ.2 hG
  let r := fun x : ℝ => (⟨orderedCutIndex (weightValueEmbedding wold) x,
    Nat.lt_succ_of_le (orderedCutIndex_le _ _)⟩ : Fin (m + 1))
  have hset (x : ℝ) : s (r x).val = lowerWeightSet wold x := oldWeightLevel_cut wold x
  let inc := fun x : ℝ => coordinateInclusion (Finset.subset_of_eq (hset x).symm)
  let T := fun x : ℝ => (G (r x)).lift.comp (inc x)
  have hrange (x : ℝ) : LinearMap.range (T x).toLinearMap = LinearMap.range (G (r x)).lift.toLinearMap := by
    apply le_antisymm
    · rintro a ⟨v, rfl⟩
      exact ⟨inc x v, rfl⟩
    · rintro a ⟨v, rfl⟩
      refine ⟨⟨v.1, coordinateSubspace_mono (Finset.subset_of_eq (hset x)) v.property⟩, ?_⟩
      rfl
  refine ⟨T, ?_, ?_, ?_, ?_⟩
  · intro x
    exact restrict_coordinate_graph_right_inverse (Finset.subset_of_eq (hset x).symm)
      (G (r x)).lift (G (r x)).right_inverse
  · intro x y hxy
    rw [hrange, hrange]
    exact hGmono (orderedCutIndex_monotone (weightValueEmbedding wold) hxy)
  · intro x
    rw [hrange]
    exact (selectedRowSpace_mono B (newWeightLevel_cut_covers wold wnew x)).trans (G (r x)).contains
  · intro x
    have ht := restrict_coordinate_graph_norm_le (Finset.subset_of_eq (hset x).symm) (G (r x)).lift
    apply ht.trans
    apply (G (r x)).norm_bound.trans
    have hmn : m ≤ n := weightValueSet_card_le wold
    have hdiff : m - (r x).val ≤ n := (Nat.sub_le _ _).trans hmn
    have hdiffR : ((m - (r x).val : ℕ) : ℝ) ≤ n := by exact_mod_cast hdiff
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_right hdiffR hC)

end Yau.Blueprint.Alignment.Y03Proof
