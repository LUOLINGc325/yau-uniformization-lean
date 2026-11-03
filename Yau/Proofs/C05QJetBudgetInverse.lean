import Yau.Proofs.C05QJetBudgetProduct
import Yau.Proofs.C05InverseFieldSecondJet

/-! The third genuine lowered-inverse jet is controlled by a finite polynomial
in the first three actual form jets and the first two actual inverse jets. -/
noncomputable section
open Filter
open scoped Manifold Topology ContDiff Matrix
namespace Yau.Proofs.C05QJetBudgetAux
open Yau Yau.Proofs.C05Aux Yau.LeafProofs.L23Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false

theorem inverseFieldJet_three_word (k : HermitianField M) (hk : MetricSmooth k)
    (c : M.Carrier) (A : ComplexVector n → Matrix (RIdx n) (RIdx n) ℝ)
    (hA : ∀ a b, ContDiffOn ℝ ∞ (fun z => A z a b) (chartTarget c))
    (hdet : ∀ z ∈ chartTarget c, (A z).det ≠ 0)
    {z : ComplexVector n} (hz : z ∈ chartTarget c) :
    let C := inverseFieldJet k c A 0
    let B := covariantD k c (fun w => matrixCovTensor (A w))
    let P := fun w => tensorConcatProduct (C w) (C w)
    let H := (realMetricFn k c z)⁻¹
    inverseFieldJet k c A 3 z = fun v =>
      -(inverseCompositionWord.dLeft.dLeft.eval H
          (covariantD k c (covariantD k c P) z) (B z) v +
        inverseCompositionWord.dLeft.dRight.eval H
          (covariantD k c P z) (covariantD k c B z) v +
        inverseCompositionWord.dRight.dLeft.eval H
          (covariantD k c P z) (covariantD k c B z) v +
        inverseCompositionWord.dRight.dRight.eval H
          (P z) (covariantD k c (covariantD k c B) z) v) := by
  let C := inverseFieldJet k c A 0
  let B := covariantD k c (fun w => matrixCovTensor (A w))
  let P := fun w => tensorConcatProduct (C w) (C w)
  let F := fun w => inverseCompositionWord.dLeft.eval (realMetricFn k c w)⁻¹
    (covariantD k c P w) (B w)
  let L := fun w => inverseCompositionWord.dRight.eval (realMetricFn k c w)⁻¹
    (P w) (covariantD k c B w)
  have hO := isOpen_extChartAt_target (I := ComplexModel n) c
  have hC (v : Fin 2 → RIdx n) := inverseFieldJet_zero_contDiffOn k hk c A hA hdet v
  have hP (v : Fin 4 → RIdx n) : ContDiffOn ℝ ∞ (fun w => P w v) (chartTarget c) :=
    (hC _).mul (hC _)
  have hDP := covariantD_contDiffOn k hk c P hP
  have hB := covariantD_contDiffOn k hk c (fun w => matrixCovTensor (A w))
    (fun u => hA (u 0) (u 1))
  have hDB := covariantD_contDiffOn k hk c B hB
  have hF := inverseCompositionWord.dLeft.eval_contDiffOn k hk c (covariantD k c P) B hDP hB
  have hL := inverseCompositionWord.dRight.eval_contDiffOn k hk c P (covariantD k c B) hP hDB
  have hsum (v : Fin 4 → RIdx n) :
      DifferentiableAt ℝ (fun w => F w v+L w v) z :=
    ((hF v).contDiffAt (hO.mem_nhds hz)).differentiableAt (by simp) |>.add
      (((hL v).contDiffAt (hO.mem_nhds hz)).differentiableAt (by simp))
  have he : inverseFieldJet k c A 2 =ᶠ[𝓝 z] (fun w v => (-1 : ℝ)*(F w v+L w v)) := by
    filter_upwards [hO.mem_nhds hz] with w hw
    have hh := inverseFieldJet_two_word k hk c A hA hdet hw
    change inverseFieldJet k c A 2 w = fun v => -(F w v+L w v) at hh
    funext v
    rw [hh]
    ring
  have hd := covariantD_eventuallyEq k c _ _ z he
  rw [covariantD_const_mul_at k c (fun w v => F w v+L w v) z hsum (-1)] at hd
  have hadd := covariantD_add_at k c F L z
    (fun v => ((hF v).contDiffAt (hO.mem_nhds hz)).differentiableAt (by simp))
    (fun v => ((hL v).contDiffAt (hO.mem_nhds hz)).differentiableAt (by simp))
  funext v
  change covariantD k c (inverseFieldJet k c A 2) z v = _
  rw [hd]
  have hv : Fin.cons (v 0) (fun j => v j.succ)=v := by
    funext j
    exact Fin.cases rfl (fun _ => rfl) j
  have hDF := inverseCompositionWord.dLeft.covariantD_eval k hk c
    (covariantD k c P) B hDP hB hz (v 0) (fun j => v j.succ)
  have hDL := inverseCompositionWord.dRight.covariantD_eval k hk c
    P (covariantD k c B) hP hDB hz (v 0) (fun j => v j.succ)
  rw [hv] at hDF hDL
  change covariantD k c F z v = _ at hDF
  change covariantD k c L z v = _ at hDL
  change (-1 : ℝ)*covariantD k c (fun w => F w+L w) z v = _
  rw [hadd]
  change (-1 : ℝ)*(covariantD k c F z v+covariantD k c L z v)=_
  rw [hDF,hDL]
  ring


theorem inverseFieldJet_three_norm_le (k : HermitianField M) (hk : MetricSmooth k)
    (c : M.Carrier) (A : ComplexVector n → Matrix (RIdx n) (RIdx n) ℝ)
    (hA : ∀ a b, ContDiffOn ℝ ∞ (fun z => A z a b) (chartTarget c))
    (hdet : ∀ z ∈ chartTarget c, (A z).det ≠ 0)
    {z : ComplexVector n} (hz : z ∈ chartTarget c) :
    let G := realMetricFn k c z
    let C := inverseFieldJet k c A 0
    let B := covariantD k c (fun w => matrixCovTensor (A w))
    metricTensorNorm G (inverseFieldJet k c A 3 z) ≤ (2*n : ℕ) *
      ((2*metricTensorNorm G (C z)*metricTensorNorm G (inverseFieldJet k c A 2 z) +
        2*metricTensorNorm G (inverseFieldJet k c A 1 z)^2)*metricTensorNorm G (B z) +
      4*metricTensorNorm G (C z)*metricTensorNorm G (inverseFieldJet k c A 1 z)*
        metricTensorNorm G (covariantD k c B z) +
      metricTensorNorm G (C z)^2*metricTensorNorm G (covariantD k c (covariantD k c B) z)) := by
  dsimp only
  let G := realMetricFn k c z
  let d : ℝ := (2*n : ℕ)
  let C := inverseFieldJet k c A 0
  let B := covariantD k c (fun w => matrixCovTensor (A w))
  let P := fun w => tensorConcatProduct (C w) (C w)
  have hG : G.PosDef := Yau.LeafProofs.L12Aux.realMetricFn_posDef k c z hz
  have hd : 0 ≤ d := Nat.cast_nonneg _
  have hC (v : Fin 2 → RIdx n) := inverseFieldJet_zero_contDiffOn k hk c A hA hdet v
  have hCd (v : Fin 2 → RIdx n) := ((hC v).contDiffAt
    ((isOpen_extChartAt_target (I := ComplexModel n) c).mem_nhds hz)).differentiableAt (by simp)
  have hP0 : metricTensorNorm G (P z)=metricTensorNorm G (C z)^2 := by
    dsimp only [P]
    rw [metricTensorNorm_concatProduct G hG,pow_two]
  have hP1 : metricTensorNorm G (covariantD k c P z) ≤
      2*metricTensorNorm G (C z)*metricTensorNorm G (inverseFieldJet k c A 1 z) := by
    have H := covariantD_concatProduct_norm_le k c C C z G hG hCd hCd
    change metricTensorNorm G (covariantD k c P z) ≤ _ at H
    apply H.trans_eq
    change metricTensorNorm G (inverseFieldJet k c A 1 z)*metricTensorNorm G (C z) +
      metricTensorNorm G (C z)*metricTensorNorm G (inverseFieldJet k c A 1 z)=_
    ring
  have hP2 : metricTensorNorm G (covariantD k c (covariantD k c P) z) ≤
      2*metricTensorNorm G (C z)*metricTensorNorm G (inverseFieldJet k c A 2 z) +
        2*metricTensorNorm G (inverseFieldJet k c A 1 z)^2 := by
    have H := covariantD_twice_product_norm_le k hk c C C hC hC hz G hG
    change metricTensorNorm G (covariantD k c (covariantD k c P) z) ≤ _ at H
    apply H.trans_eq
    change metricTensorNorm G (inverseFieldJet k c A 2 z)*metricTensorNorm G (C z) +
      2*metricTensorNorm G (inverseFieldJet k c A 1 z)*metricTensorNorm G (inverseFieldJet k c A 1 z) +
      metricTensorNorm G (C z)*metricTensorNorm G (inverseFieldJet k c A 2 z)=_
    ring
  let U := inverseCompositionWord.dLeft.dLeft.eval G⁻¹
    (covariantD k c (covariantD k c P) z) (B z)
  let V := inverseCompositionWord.dLeft.dRight.eval G⁻¹
    (covariantD k c P z) (covariantD k c B z)
  let T := inverseCompositionWord.dRight.dLeft.eval G⁻¹
    (covariantD k c P z) (covariantD k c B z)
  let R := inverseCompositionWord.dRight.dRight.eval G⁻¹
    (P z) (covariantD k c (covariantD k c B) z)
  have h1 := inverseCompositionWord.dLeft.dLeft.eval_norm_le G hG
    (covariantD k c (covariantD k c P) z) (B z)
  have h2 := inverseCompositionWord.dLeft.dRight.eval_norm_le G hG
    (covariantD k c P z) (covariantD k c B z)
  have h3 := inverseCompositionWord.dRight.dLeft.eval_norm_le G hG
    (covariantD k c P z) (covariantD k c B z)
  have h4 := inverseCompositionWord.dRight.dRight.eval_norm_le G hG
    (P z) (covariantD k c (covariantD k c B) z)
  have hs1 := sqrt_covTensorNormSq_add_le G hG U V
  have hs2 := sqrt_covTensorNormSq_add_le G hG (U+V) T
  have hs3 := sqrt_covTensorNormSq_add_le G hG (U+V+T) R
  have H := hs3.trans (add_le_add
    (hs2.trans (add_le_add hs1 (le_refl _))) (le_refl _))
  have H' := H.trans (add_le_add (add_le_add (add_le_add h1 h2) h3) h4)
  change metricTensorNorm G (U+V+T+R) ≤
    d*metricTensorNorm G (covariantD k c (covariantD k c P) z)*metricTensorNorm G (B z) +
    d*metricTensorNorm G (covariantD k c P z)*metricTensorNorm G (covariantD k c B z) +
    d*metricTensorNorm G (covariantD k c P z)*metricTensorNorm G (covariantD k c B z) +
    d*metricTensorNorm G (P z)*metricTensorNorm G (covariantD k c (covariantD k c B) z) at H'
  have hl := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hP2 hd)
    (metricTensorNorm_nonneg G (B z))
  have hc := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hP1 hd)
    (metricTensorNorm_nonneg G (covariantD k c B z))
  rw [hP0] at H'
  have Hb := H'.trans (add_le_add (add_le_add (add_le_add hl hc) hc) (le_refl _))
  rw [inverseFieldJet_three_word k hk c A hA hdet hz,metricTensorNorm_neg]
  change metricTensorNorm G (U+V+T+R) ≤ _
  exact Hb.trans_eq (by dsimp only [d]; ring)

end Yau.Proofs.C05QJetBudgetAux
