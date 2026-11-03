import Yau.Proofs.Y03GraphMatrix
import Yau.Proofs.Y03RowSpace

/-! The nested graph rows form the required basis and give the literal inverse zero pattern. -/

open scoped Matrix

noncomputable section

namespace Yau.Blueprint.Alignment.Y03Proof

open Yau

variable {n : ℕ}

theorem rowLinearMap_injective_of_isUnit {B : Herm n} (hB : IsUnit B) : Function.Injective (rowLinearMap B) := by
  intro v w hvw
  apply WithLp.ofLp_injective
  apply (Matrix.vecMul_injective_iff_isUnit.2 hB)
  rw [rowLinearMap_apply, rowLinearMap_apply] at hvw
  exact congrArg WithLp.ofLp hvw

theorem graphMatrix_row (w : Fin n → ℝ)
    (T : (x : ℝ) → coordinateSubspace (lowerWeightSet w x) →L[ℂ] ComplexVector n) (i : Fin n) :
    rowLinearMap (graphMatrix w T) (stdVec i) = T (w i) (weightBasis w i) := by
  ext l
  rw [rowLinearMap_apply]
  change (WithLp.ofLp (stdVec i) ᵥ* graphMatrix w T) l = _
  simp [stdVec, EuclideanSpace.single, Matrix.single_vecMul, graphMatrix]

theorem graphMatrix_selected_rows_le (w : Fin n → ℝ)
    (T : (x : ℝ) → coordinateSubspace (lowerWeightSet w x) →L[ℂ] ComplexVector n)
    (hnested : ∀ x y, x ≤ y → LinearMap.range (T x).toLinearMap ≤ LinearMap.range (T y).toLinearMap)
    (x : ℝ) : selectedRowSpace (graphMatrix w T) (lowerWeightSet w x) ≤ LinearMap.range (T x).toLinearMap := by
  rintro a ⟨c, rfl⟩
  change rowLinearMap (graphMatrix w T) (c : ComplexVector n) ∈ LinearMap.range (T x).toLinearMap
  rw [← sum_stdVec (c : ComplexVector n), map_sum]
  apply Submodule.sum_mem
  intro i _
  rw [map_smul]
  by_cases hi : i ∈ lowerWeightSet w x
  · apply Submodule.smul_mem
    rw [graphMatrix_row]
    exact (hnested (w i) x (Finset.mem_filter.1 hi).2) ⟨weightBasis w i, rfl⟩
  · rw [c.property i hi, zero_smul]
    exact Submodule.zero_mem _

theorem graphMatrix_selected_rows_eq (w : Fin n → ℝ)
    (T : (x : ℝ) → coordinateSubspace (lowerWeightSet w x) →L[ℂ] ComplexVector n)
    (hT : ∀ x, (coordinateProjectionOnto (lowerWeightSet w x)).comp (T x) =
      ContinuousLinearMap.id ℂ (coordinateSubspace (lowerWeightSet w x)))
    (hnested : ∀ x y, x ≤ y → LinearMap.range (T x).toLinearMap ≤ LinearMap.range (T y).toLinearMap)
    (x : ℝ) : selectedRowSpace (graphMatrix w T) (lowerWeightSet w x) = LinearMap.range (T x).toLinearMap := by
  have hLunit := strict_weight_isUnit (graphMatrix w T) w (graphMatrix_diagonal w T hT)
    (graphMatrix_strict_support w T hT)
  have hrowinj := (rowLinearMap_injective_of_isUnit hLunit).comp
    (Subtype.val_injective : Function.Injective (fun v : coordinateSubspace (lowerWeightSet w x) => (v : ComplexVector n)))
  have hTinj : Function.Injective (T x) := by
    intro u v huv
    have hp := congrArg (coordinateProjectionOnto (lowerWeightSet w x)) huv
    have hleft (z : coordinateSubspace (lowerWeightSet w x)) :
        coordinateProjectionOnto (lowerWeightSet w x) (T x z) = z :=
      congrArg (fun L : coordinateSubspace (lowerWeightSet w x) →L[ℂ] coordinateSubspace (lowerWeightSet w x) => L z) (hT x)
    simpa only [hleft] using hp
  apply Submodule.eq_of_le_of_finrank_eq (graphMatrix_selected_rows_le w T hnested x)
  exact (LinearMap.finrank_range_of_inj hrowinj).trans (LinearMap.finrank_range_of_inj hTinj).symm

theorem selectedRowSpace_inverse_support {L : Herm n} (hL : IsUnit L) {s : Finset (Fin n)}
    {a : ComplexVector n} (ha : a ∈ selectedRowSpace L s) : rowApply L⁻¹ a ∈ coordinateSubspace s := by
  obtain ⟨c, hc⟩ := ha
  have hca : rowApply L (c : ComplexVector n) = a := (rowLinearMap_apply _ _).symm.trans hc
  rw [← hca, ← rowApply_mul, Matrix.mul_nonsing_inv L ((Matrix.isUnit_iff_isUnit_det L).1 hL)]
  have hone : rowApply (1 : Herm n) (c : ComplexVector n) = (c : ComplexVector n) := by
    apply WithLp.ofLp_injective
    exact Matrix.vecMul_one _
  rw [hone]
  exact c.property

theorem selectedRowSpace_row_mem (B : Herm n) {s : Finset (Fin n)} {i : Fin n} (hi : i ∈ s) :
    rowApply B (stdVec i) ∈ selectedRowSpace B s := by
  refine ⟨⟨stdVec i, stdVec_mem_coordinateSubspace hi⟩, ?_⟩
  exact rowLinearMap_apply B (stdVec i)

theorem graphMatrix_zero_pattern (wold wnew : Fin n → ℝ) (B : Herm n)
    (T : (x : ℝ) → coordinateSubspace (lowerWeightSet wold x) →L[ℂ] ComplexVector n)
    (hT : ∀ x, (coordinateProjectionOnto (lowerWeightSet wold x)).comp (T x) =
      ContinuousLinearMap.id ℂ (coordinateSubspace (lowerWeightSet wold x)))
    (hnested : ∀ x y, x ≤ y → LinearMap.range (T x).toLinearMap ≤ LinearMap.range (T y).toLinearMap)
    (hrequired : ∀ x, selectedRowSpace B (lowerWeightSet wnew x) ≤ LinearMap.range (T x).toLinearMap)
    (i l : Fin n) (hweight : wnew i < wold l) : (B * (graphMatrix wold T)⁻¹) i l = 0 := by
  let L := graphMatrix wold T
  have hLunit : IsUnit L := strict_weight_isUnit L wold (graphMatrix_diagonal wold T hT)
    (graphMatrix_strict_support wold T hT)
  have ha : rowApply B (stdVec i) ∈ selectedRowSpace L (lowerWeightSet wold (wnew i)) := by
    rw [graphMatrix_selected_rows_eq wold T hT hnested]
    exact hrequired (wnew i) (selectedRowSpace_row_mem B (Finset.mem_filter.2 ⟨Finset.mem_univ _, le_rfl⟩))
  have hs := selectedRowSpace_inverse_support hLunit ha
  have hl : l ∉ lowerWeightSet wold (wnew i) := by
    intro hl
    exact (not_le_of_gt hweight) (Finset.mem_filter.1 hl).2
  have hz := hs l hl
  rw [← rowApply_mul] at hz
  change (WithLp.ofLp (stdVec i) ᵥ* (B * L⁻¹)) l = 0 at hz
  simpa [stdVec, EuclideanSpace.single, Matrix.single_vecMul] using hz

end Yau.Blueprint.Alignment.Y03Proof
