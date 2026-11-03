import Yau.Proofs.F05DefiningCoordinates

/-! An actual real tangential/normal product for a flattened physical face.
The last coordinate is the inward normal, so the physical side is r≥0. -/

open Set
open scoped ContDiff
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.LeafProofs.L16Aux
variable {n : ℕ}

def F05Tangential (j : RIdx n) : Submodule ℝ (Space n) := (realCoordLinear j).ker

def F05TangentPoint (j : RIdx n) (x : Space n) (hx : realCoord x j = 0) : F05Tangential j :=
  ⟨x,by
    change realCoordLinear j x = 0
    rw [realCoordLinear_apply]
    exact hx⟩

def F05TangentProjection (j : RIdx n) : Space n →L[ℝ] F05Tangential j :=
  (ContinuousLinearMap.id ℝ (Space n)-(realCoordLinear j).smulRight (realVec j)).codRestrict
    (F05Tangential j) (by
      intro x
      change realCoordLinear j (x-realCoordLinear j x • realVec j) = 0
      have he : realCoordLinear j (realVec j) = 1 := by simp [realCoordLinear,realVec_norm]
      simp only [map_sub,map_smul,he,smul_eq_mul,mul_one,sub_self])

def F05NormalSplitMap (j : RIdx n) : Space n →L[ℝ] F05Tangential j × ℝ :=
  (F05TangentProjection j).prod (-(realCoordLinear j))

def F05NormalMergeMap (j : RIdx n) : (F05Tangential j × ℝ) →L[ℝ] Space n :=
  (F05Tangential j).subtypeL.comp (ContinuousLinearMap.fst ℝ (F05Tangential j) ℝ)-
    (ContinuousLinearMap.snd ℝ (F05Tangential j) ℝ).smulRight (realVec j)

theorem F05_normal_merge_split (j : RIdx n) (x : Space n) :
    F05NormalMergeMap j (F05NormalSplitMap j x) = x := by
  change (x-realCoordLinear j x • realVec j)-(-realCoordLinear j x) • realVec j = x
  simp only [neg_smul,sub_neg_eq_add,sub_add_cancel]

theorem F05_normal_split_merge (j : RIdx n) (q : F05Tangential j × ℝ) :
    F05NormalSplitMap j (F05NormalMergeMap j q) = q := by
  have hq : realCoordLinear j q.1.val = 0 := q.1.property
  have he : realCoordLinear j (realVec j) = 1 := by simp [realCoordLinear,realVec_norm]
  apply Prod.ext
  · apply Subtype.ext
    change (q.1.val-q.2 • realVec j)-
      realCoordLinear j (q.1.val-q.2 • realVec j) • realVec j = q.1.val
    simp only [map_sub,map_smul,hq,he,smul_eq_mul,mul_one,zero_sub,neg_smul,sub_neg_eq_add,sub_add_cancel]
  · change -realCoordLinear j (q.1.val-q.2 • realVec j) = q.2
    simp only [map_sub,map_smul,hq,he,smul_eq_mul,mul_one,zero_sub,neg_neg]

def F05NormalProduct (j : RIdx n) : Space n ≃L[ℝ] F05Tangential j × ℝ where
  toFun := F05NormalSplitMap j
  invFun := F05NormalMergeMap j
  left_inv := F05_normal_merge_split j
  right_inv := F05_normal_split_merge j
  map_add' := (F05NormalSplitMap j).map_add
  map_smul' := (F05NormalSplitMap j).map_smul
  continuous_toFun := (F05NormalSplitMap j).continuous
  continuous_invFun := (F05NormalMergeMap j).continuous

theorem F05_normal_product_inward (j : RIdx n) (q : F05Tangential j × ℝ) :
    realCoord (F05NormalMergeMap j q) j = -q.2 := by
  have hq : realCoordLinear j q.1.val = 0 := q.1.property
  have he : realCoordLinear j (realVec j) = 1 := by simp [realCoordLinear,realVec_norm]
  rw [← realCoordLinear_apply]
  change realCoordLinear j (q.1.val-q.2 • realVec j) = -q.2
  simp only [map_sub,map_smul,hq,he,smul_eq_mul,mul_one,zero_sub]

end Yau.Proofs.F05Aux
