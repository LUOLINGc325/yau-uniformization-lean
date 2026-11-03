import Yau.Proofs.C05InverseFieldJets

/-! Differentiate the actual inverse identity once more. The second
inverse jet has a budget in the first two genuine form jets. -/

noncomputable section
open Filter
open scoped Manifold Topology ContDiff Matrix

namespace Yau.Proofs.C05Aux
open Yau Yau.LeafProofs.L23Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false

theorem inverseFieldJet_two_word (k : HermitianField M) (hk : MetricSmooth k)
    (c : M.Carrier) (A : ComplexVector n → Matrix (RIdx n) (RIdx n) ℝ)
    (hA : ∀ a b, ContDiffOn ℝ ∞ (fun z => A z a b) (chartTarget c))
    (hdet : ∀ z ∈ chartTarget c, (A z).det ≠ 0)
    {z : ComplexVector n} (hz : z ∈ chartTarget c) :
    let C := inverseFieldJet k c A 0
    let B := covariantD k c (fun w => matrixCovTensor (A w))
    let P := fun w => tensorConcatProduct (C w) (C w)
    inverseFieldJet k c A 2 z = fun v =>
      -(inverseCompositionWord.dLeft.eval (realMetricFn k c z)⁻¹ (covariantD k c P z) (B z) v +
        inverseCompositionWord.dRight.eval (realMetricFn k c z)⁻¹ (P z) (covariantD k c B z) v) := by
  let C := inverseFieldJet k c A 0
  let B := covariantD k c (fun w => matrixCovTensor (A w))
  let P := fun w => tensorConcatProduct (C w) (C w)
  let F := fun w => inverseCompositionWord.eval (realMetricFn k c w)⁻¹ (P w) (B w)
  have hO := isOpen_extChartAt_target (I := ComplexModel n) c
  have hC (v : Fin 2 → RIdx n) : ContDiffOn ℝ ∞ (fun w => C w v) (chartTarget c) :=
    inverseFieldJet_zero_contDiffOn k hk c A hA hdet v
  have hP (v : Fin 4 → RIdx n) : ContDiffOn ℝ ∞ (fun w => P w v) (chartTarget c) :=
    (hC _).mul (hC _)
  have hB (v : Fin 3 → RIdx n) : ContDiffOn ℝ ∞ (fun w => B w v) (chartTarget c) :=
    covariantD_contDiffOn k hk c (fun w => matrixCovTensor (A w))
      (fun u => hA (u 0) (u 1)) v
  have hF (v : Fin 3 → RIdx n) : ContDiffOn ℝ ∞ (fun w => F w v) (chartTarget c) :=
    inverseCompositionWord.eval_contDiffOn k hk c P B hP hB v
  have he : inverseFieldJet k c A 1 =ᶠ[𝓝 z] (fun w v => (-1 : ℝ) * F w v) := by
    filter_upwards [hO.mem_nhds hz] with w hw
    have hAd (a b : RIdx n) := ((hA a b).contDiffAt (hO.mem_nhds hw)).differentiableAt (by simp)
    funext v
    have hh := congrFun (inverseFieldJet_one_word k hk c A hw hAd (hdet w hw)) v
    change inverseFieldJet k c A 1 w v = -(F w v) at hh
    rw [hh]
    ring
  have hd := covariantD_eventuallyEq k c _ _ z he
  rw [covariantD_const_mul_at k c F z
    (fun v => ((hF v).contDiffAt (hO.mem_nhds hz)).differentiableAt (by simp)) (-1)] at hd
  change inverseFieldJet k c A 2 z = fun v =>
    -(inverseCompositionWord.dLeft.eval (realMetricFn k c z)⁻¹ (covariantD k c P z) (B z) v +
      inverseCompositionWord.dRight.eval (realMetricFn k c z)⁻¹ (P z) (covariantD k c B z) v)
  funext v
  change covariantD k c (inverseFieldJet k c A 1) z v = _
  rw [hd]
  have hv : Fin.cons (v 0) (fun j => v j.succ) = v := by
    funext j
    exact Fin.cases rfl (fun _ => rfl) j
  have hh := inverseCompositionWord.covariantD_eval k hk c P B hP hB hz (v 0) (fun j => v j.succ)
  rw [hv] at hh
  change covariantD k c F z v = _ at hh
  change (-1 : ℝ) * covariantD k c F z v = _
  rw [hh]
  ring

theorem inverseFieldJet_two_norm_le (k : HermitianField M) (hk : MetricSmooth k)
    (c : M.Carrier) (A : ComplexVector n → Matrix (RIdx n) (RIdx n) ℝ)
    (hA : ∀ a b, ContDiffOn ℝ ∞ (fun z => A z a b) (chartTarget c))
    (hdet : ∀ z ∈ chartTarget c, (A z).det ≠ 0)
    {z : ComplexVector n} (hz : z ∈ chartTarget c) :
    let G := realMetricFn k c z
    let C := inverseFieldJet k c A 0
    let B := covariantD k c (fun w => matrixCovTensor (A w))
    metricTensorNorm G (inverseFieldJet k c A 2 z) ≤
      (2 * n : ℕ) * (2 * metricTensorNorm G (C z) * metricTensorNorm G (inverseFieldJet k c A 1 z)) *
        metricTensorNorm G (B z) +
      (2 * n : ℕ) * metricTensorNorm G (C z) ^ 2 * metricTensorNorm G (covariantD k c B z) := by
  dsimp only
  let G := realMetricFn k c z
  let C := inverseFieldJet k c A 0
  let B := covariantD k c (fun w => matrixCovTensor (A w))
  let P := fun w => tensorConcatProduct (C w) (C w)
  have hG : G.PosDef := Yau.LeafProofs.L12Aux.realMetricFn_posDef k c z hz
  have hCd (v : Fin 2 → RIdx n) := ((inverseFieldJet_zero_contDiffOn k hk c A hA hdet v).contDiffAt
    ((isOpen_extChartAt_target (I := ComplexModel n) c).mem_nhds hz)).differentiableAt (by simp)
  have hp := covariantD_concatProduct_norm_le k c C C z G hG hCd hCd
  have hp' : metricTensorNorm G (covariantD k c P z) ≤
      2 * metricTensorNorm G (C z) * metricTensorNorm G (inverseFieldJet k c A 1 z) := by
    change metricTensorNorm G (covariantD k c P z) ≤ _ at hp
    apply hp.trans_eq
    change metricTensorNorm G (inverseFieldJet k c A 1 z) * metricTensorNorm G (C z) +
      metricTensorNorm G (C z) * metricTensorNorm G (inverseFieldJet k c A 1 z) = _
    ring
  have hpp : metricTensorNorm G (P z) = metricTensorNorm G (C z) ^ 2 := by
    dsimp only [P]
    rw [metricTensorNorm_concatProduct G hG, pow_two]
  have hL := inverseCompositionWord.dLeft.eval_norm_le G hG (covariantD k c P z) (B z)
  have hR := inverseCompositionWord.dRight.eval_norm_le G hG (P z) (covariantD k c B z)
  have hsum := sqrt_covTensorNormSq_add_le G hG
    (inverseCompositionWord.dLeft.eval G⁻¹ (covariantD k c P z) (B z))
    (inverseCompositionWord.dRight.eval G⁻¹ (P z) (covariantD k c B z))
  rw [inverseFieldJet_two_word k hk c A hA hdet hz, metricTensorNorm_neg]
  have hb := hsum.trans (add_le_add hL hR)
  change metricTensorNorm G _ ≤
    (2 * n : ℕ) * metricTensorNorm G (covariantD k c P z) * metricTensorNorm G (B z) +
      (2 * n : ℕ) * metricTensorNorm G (P z) * metricTensorNorm G (covariantD k c B z) at hb
  rw [hpp] at hb
  apply hb.trans
  apply add_le_add
  · apply mul_le_mul_of_nonneg_right _ (metricTensorNorm_nonneg G _)
    exact mul_le_mul_of_nonneg_left hp' (Nat.cast_nonneg _)
  · exact le_refl _

end Yau.Proofs.C05Aux
