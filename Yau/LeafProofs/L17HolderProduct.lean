import Yau.LeafProofs.L17HolderSpace
import Mathlib.Analysis.Normed.Operator.Bilinear

/-! Actual scalar multiplication in the global atlas Holder space. -/

noncomputable section

namespace Yau.LeafProofs.L17HolderAux

open Yau.LeafProofs.L17Aux

variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}
variable {P : UniformChartPartition g} {T γ : ℝ}

theorem product_value_bound (u v : HolderSpace P T γ) (q : Cylinder M T) :
    |holderFun u q * holderFun v q| ≤ ‖u‖ * ‖v‖ := by
  rw [abs_mul]
  exact mul_le_mul (value_abs_le_norm u q) (value_abs_le_norm v q)
    (abs_nonneg _) (norm_nonneg _)

theorem product_weighted_difference_bound (u v : HolderSpace P T γ) (i : ChartPairs P T) :
    |pairWeight P T γ i * (holderFun u (chartRight P T i) * holderFun v (chartRight P T i) -
      holderFun u (chartLeft P T i) * holderFun v (chartLeft P T i))| ≤ 2 * ‖u‖ * ‖v‖ := by
  let x := chartLeft P T i
  let y := chartRight P T i
  let w := pairWeight P T γ i
  have hform : w * (holderFun u y * holderFun v y - holderFun u x * holderFun v x) =
      holderFun u y * (w * (holderFun v y - holderFun v x)) +
        holderFun v x * (w * (holderFun u y - holderFun u x)) := by ring
  change |w * (holderFun u y * holderFun v y - holderFun u x * holderFun v x)| ≤ _
  rw [hform]
  calc
    _ ≤ |holderFun u y * (w * (holderFun v y - holderFun v x))| +
        |holderFun v x * (w * (holderFun u y - holderFun u x))| := abs_add_le _ _
    _ = |holderFun u y| * |w * (holderFun v y - holderFun v x)| +
        |holderFun v x| * |w * (holderFun u y - holderFun u x)| := by
      rw [abs_mul (holderFun u y), abs_mul (holderFun v x)]
    _ ≤ ‖u‖ * ‖v‖ + ‖v‖ * ‖u‖ := add_le_add
      (mul_le_mul (value_abs_le_norm u y) (weighted_difference_abs_le_norm v i)
        (abs_nonneg _) (norm_nonneg _))
      (mul_le_mul (value_abs_le_norm v x) (weighted_difference_abs_le_norm u i)
        (abs_nonneg _) (norm_nonneg _))
    _ = _ := by ring

def productElement (u v : HolderSpace P T γ) : HolderSpace P T γ :=
  ofBounds P T γ (fun q => holderFun u q * holderFun v q)
    (u.val.1.continuous.mul v.val.1.continuous) (‖u‖ * ‖v‖) (2 * ‖u‖ * ‖v‖)
    (product_value_bound u v) (product_weighted_difference_bound u v)

theorem productElement_value (u v : HolderSpace P T γ) (q : Cylinder M T) :
    holderFun (productElement u v) q = holderFun u q * holderFun v q := rfl

theorem productElement_norm_le (u v : HolderSpace P T γ) :
    ‖productElement u v‖ ≤ 2 * ‖u‖ * ‖v‖ := by
  apply (ofBounds_norm_le P T γ _ _ _ _ (by positivity) (by positivity)
    (product_value_bound u v) (product_weighted_difference_bound u v)).trans
  exact max_le (by nlinarith [mul_nonneg (norm_nonneg u) (norm_nonneg v)]) le_rfl

def productLinearMap (P : UniformChartPartition g) (T γ : ℝ) :
    HolderSpace P T γ →ₗ[ℝ] HolderSpace P T γ →ₗ[ℝ] HolderSpace P T γ where
  toFun u := {
    toFun := productElement u
    map_add' := fun v w => by
      apply holderFun_injective P T γ
      ext q
      change holderFun u q * (holderFun v q + holderFun w q) = _
      exact mul_add _ _ _
    map_smul' := fun c v => by
      apply holderFun_injective P T γ
      ext q
      change holderFun u q * (c * holderFun v q) = c * (holderFun u q * holderFun v q)
      ring }
  map_add' u v := by
    apply LinearMap.ext
    intro w
    apply holderFun_injective P T γ
    ext q
    change (holderFun u q + holderFun v q) * holderFun w q = _
    exact add_mul _ _ _
  map_smul' c u := by
    apply LinearMap.ext
    intro v
    apply holderFun_injective P T γ
    ext q
    change (c * holderFun u q) * holderFun v q = c * (holderFun u q * holderFun v q)
    ring

def productCLM (P : UniformChartPartition g) (T γ : ℝ) :
    HolderSpace P T γ →L[ℝ] HolderSpace P T γ →L[ℝ] HolderSpace P T γ :=
  (productLinearMap P T γ).mkContinuous₂ 2 productElement_norm_le

theorem productCLM_value (P : UniformChartPartition g) (T γ : ℝ)
    (u v : HolderSpace P T γ) (q : Cylinder M T) :
    holderFun (productCLM P T γ u v) q = holderFun u q * holderFun v q := rfl

theorem productCLM_opNorm_le (P : UniformChartPartition g) (T γ : ℝ) :
    ‖productCLM P T γ‖ ≤ 2 :=
  (productLinearMap P T γ).mkContinuous₂_norm_le (by norm_num) productElement_norm_le

end Yau.LeafProofs.L17HolderAux
