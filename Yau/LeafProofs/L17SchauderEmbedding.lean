import Yau.LeafProofs.L17LocalHolderEmbedding
import Yau.LeafProofs.L17SchauderSpaceNorm

/-! Same-cylinder exponent descent preserves the actual function and all four jets. -/

noncomputable section

open Set Metric

set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false

namespace Yau.LeafProofs.L17SchauderAux

open Yau.LeafProofs.L17Aux Yau.LeafProofs.L17HolderAux

variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}

def schauderWeakenElement (P : UniformChartPartition g) {T α β : ℝ} {hpos : 0 < T}
    (hT : T ≤ P.radius ^ 2) (hβα : β ≤ α) (u : SchauderSpace P T α hpos) :
    SchauderSpace P T β hpos :=
  ⟨((weakenCLM P hT hβα u.val.1.1, localWeakenCLM (D1 n) P hT hβα u.val.1.2),
    (localWeakenCLM (D2 n) P hT hβα u.val.2.1, weakenCLM P hT hβα u.val.2.2)), by
      exact u.property⟩

theorem schauderWeakenElement_function (P : UniformChartPartition g)
    {T α β : ℝ} {hpos : 0 < T} (hT : T ≤ P.radius ^ 2) (hβα : β ≤ α)
    (u : SchauderSpace P T α hpos) :
    schauderFun (schauderWeakenElement P hT hβα u) = schauderFun u := rfl

theorem schauderWeakenElement_gradient (P : UniformChartPartition g)
    {T α β : ℝ} {hpos : 0 < T} (hT : T ≤ P.radius ^ 2) (hβα : β ≤ α)
    (u : SchauderSpace P T α hpos) :
    gradientFun (schauderWeakenElement P hT hβα u) = gradientFun u := rfl

theorem schauderWeakenElement_hessian (P : UniformChartPartition g)
    {T α β : ℝ} {hpos : 0 < T} (hT : T ≤ P.radius ^ 2) (hβα : β ≤ α)
    (u : SchauderSpace P T α hpos) :
    hessianFun (schauderWeakenElement P hT hβα u) = hessianFun u := rfl

theorem schauderWeakenElement_time (P : UniformChartPartition g)
    {T α β : ℝ} {hpos : 0 < T} (hT : T ≤ P.radius ^ 2) (hβα : β ≤ α)
    (u : SchauderSpace P T α hpos) :
    timeFun (schauderWeakenElement P hT hβα u) = timeFun u := rfl

theorem schauderWeakenElement_norm_le (P : UniformChartPartition g)
    {T α β : ℝ} {hpos : 0 < T} (hT : T ≤ P.radius ^ 2) (hβα : β ≤ α)
    (u : SchauderSpace P T α hpos) :
    ‖schauderWeakenElement P hT hβα u‖ ≤ (3 : ℝ) ^ (α - β) * ‖u‖ := by
  have hK := (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3) (α - β)).le
  have h0 : ‖u.val.1.1‖ ≤ ‖u‖ := (le_max_left _ _).trans (le_max_left _ _)
  have h1 : ‖u.val.1.2‖ ≤ ‖u‖ := (le_max_right _ _).trans (le_max_left _ _)
  have h2 : ‖u.val.2.1‖ ≤ ‖u‖ := (le_max_left _ _).trans (le_max_right _ _)
  have h3 : ‖u.val.2.2‖ ≤ ‖u‖ := (le_max_right _ _).trans (le_max_right _ _)
  change max (max ‖weakenElement P hT hβα u.val.1.1‖
    ‖localWeakenElement (D1 n) P hT hβα u.val.1.2‖)
    (max ‖localWeakenElement (D2 n) P hT hβα u.val.2.1‖
      ‖weakenElement P hT hβα u.val.2.2‖) ≤ _
  exact max_le
    (max_le ((weakenElement_norm_le P hT hβα _).trans (mul_le_mul_of_nonneg_left h0 hK))
      ((localWeakenElement_norm_le (D1 n) P hT hβα _).trans (mul_le_mul_of_nonneg_left h1 hK)))
    (max_le ((localWeakenElement_norm_le (D2 n) P hT hβα _).trans (mul_le_mul_of_nonneg_left h2 hK))
      ((weakenElement_norm_le P hT hβα _).trans (mul_le_mul_of_nonneg_left h3 hK)))

def schauderWeakenLinearMap (P : UniformChartPartition g) {T α β : ℝ} (hpos : 0 < T)
    (hT : T ≤ P.radius ^ 2) (hβα : β ≤ α) :
    SchauderSpace P T α hpos →ₗ[ℝ] SchauderSpace P T β hpos where
  toFun := schauderWeakenElement P hT hβα
  map_add' u v := by
    apply schauderFun_injective
    ext q
    rfl
  map_smul' c u := by
    apply schauderFun_injective
    ext q
    rfl

def schauderWeakenCLM (P : UniformChartPartition g) {T α β : ℝ} (hpos : 0 < T)
    (hT : T ≤ P.radius ^ 2) (hβα : β ≤ α) :
    SchauderSpace P T α hpos →L[ℝ] SchauderSpace P T β hpos :=
  (schauderWeakenLinearMap P hpos hT hβα).mkContinuous ((3 : ℝ) ^ (α - β))
    (schauderWeakenElement_norm_le P hT hβα)

theorem schauderWeakenCLM_function (P : UniformChartPartition g)
    {T α β : ℝ} (hpos : 0 < T) (hT : T ≤ P.radius ^ 2) (hβα : β ≤ α)
    (u : SchauderSpace P T α hpos) :
    schauderFun (schauderWeakenCLM P hpos hT hβα u) = schauderFun u := rfl

theorem schauderWeakenCLM_opNorm_le (P : UniformChartPartition g)
    {T α β : ℝ} (hpos : 0 < T) (hT : T ≤ P.radius ^ 2) (hβα : β ≤ α) :
    ‖schauderWeakenCLM P hpos hT hβα‖ ≤ (3 : ℝ) ^ (α - β) :=
  ContinuousLinearMap.opNorm_le_bound _ (Real.rpow_pos_of_pos (by norm_num) _).le
    (schauderWeakenElement_norm_le P hT hβα)

theorem schauderWeakenCLM_injective (P : UniformChartPartition g)
    {T α β : ℝ} (hpos : 0 < T) (hT : T ≤ P.radius ^ 2) (hβα : β ≤ α) :
    Function.Injective (schauderWeakenCLM P hpos hT hβα) := by
  intro u v huv
  apply schauderFun_injective
  exact congrArg (fun w : SchauderSpace P T β hpos => schauderFun w) huv

def alphaBetaSchauderEmbedding (P : UniformChartPartition g) {T : ℝ}
    (hpos : 0 < T) (hT : T ≤ P.radius ^ 2) :
    SchauderSpace P T (1 / 2) hpos →L[ℝ] SchauderSpace P T (1 / 4) hpos :=
  schauderWeakenCLM P hpos hT (by norm_num)

end Yau.LeafProofs.L17SchauderAux
