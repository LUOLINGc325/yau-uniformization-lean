import Yau.Proofs.C05RicciCubicJetsWord
import Yau.Proofs.C05SingleTraceJetBounds

/-! The actual covariant matrix composition has first-two-jet quadratic bounds. -/
noncomputable section
open Filter
open scoped Topology Manifold ContDiff Matrix
namespace Yau.Proofs.C05RicciCubicJetsAux
open Yau Yau.Proofs.C05Aux Yau.LeafProofs.L12Aux Yau.LeafProofs.L23Aux
open Yau.Proofs.C05RicciSquareJetsAux.Generic
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false

def compositionWord : SingleTraceWord 4 2 where
  toFun := ![Sum.inr 0,Sum.inl 0,Sum.inl 1,Sum.inr 1]
  invFun := Sum.elim (fun i => if i = 0 then 1 else 2) (fun i => if i = 0 then 0 else 3)
  left_inv i := by fin_cases i <;> rfl
  right_inv s := by cases s with
    | inl i => fin_cases i <;> rfl
    | inr i => fin_cases i <;> rfl

def compositionField (k : HermitianField M) (c : M.Carrier)
    (A : ComplexVector n → CovTensor n 2) : ComplexVector n → CovTensor n 2 :=
  singleTraceField compositionWord k c (fun z => tensorConcatProduct (A z) (A z))

theorem compositionField_contDiffOn (k : HermitianField M) (hk : MetricSmooth k)
    (c : M.Carrier) (A : ComplexVector n → CovTensor n 2)
    (hA : ∀ v, ContDiffOn ℝ ∞ (fun z => A z v) (chartTarget c))
    (v : Fin 2 → RIdx n) :
    ContDiffOn ℝ ∞ (fun z => compositionField k c A z v) (chartTarget c) := by
  have hAA (u : Fin 4 → RIdx n) : ContDiffOn ℝ ∞
      (fun z => tensorConcatProduct (A z) (A z) u) (chartTarget c) := (hA _).mul (hA _)
  exact singleTraceEval_contDiffOn compositionWord k hk c
    (fun z => tensorConcatProduct (A z) (A z)) hAA v

theorem metricTensorNorm_concatProduct {r s : ℕ}
    (G : Matrix (RIdx n) (RIdx n) ℝ) (hG : G.PosDef)
    (A : CovTensor n r) (B : CovTensor n s) :
    metricTensorNorm G (tensorConcatProduct A B) = metricTensorNorm G A * metricTensorNorm G B := by
  unfold metricTensorNorm
  rw [covTensorNormSq_concatProduct, Real.sqrt_mul (covTensorNormSq_nonneg G hG A)]

theorem composition_jet_norm_le_two (k : HermitianField M) (hk : MetricSmooth k)
    (c : M.Carrier) (A : ComplexVector n → CovTensor n 2)
    (hA : ∀ v, ContDiffOn ℝ ∞ (fun z => A z v) (chartTarget c))
    {z : ComplexVector n} (hz : z ∈ chartTarget c) {B : ℝ} (hB : 0 ≤ B)
    (hJA : ∀ j ≤ 2, metricTensorNorm (realMetricFn k c z) (jet k c A j z) ≤ B)
    (j : ℕ) (hj : j ≤ 2) :
    metricTensorNorm (realMetricFn k c z) (jet k c (compositionField k c A) j z) ≤
      4 * Real.sqrt (2*n:ℕ) * B ^ 2 := by
  let G := realMetricFn k c z
  have hG : G.PosDef := realMetricFn_posDef k c z hz
  have hp (i j : ℕ) (hi : i ≤ 2) (hj : j ≤ 2) :
      metricTensorNorm G (jet k c A i z) * metricTensorNorm G (jet k c A j z) ≤ B ^ 2 := by
    exact (mul_le_mul (hJA i hi) (hJA j hj)
      (metricTensorNorm_nonneg G _) hB).trans_eq (pow_two B).symm
  have hs := Real.sqrt_nonneg (2*n:ℕ)
  interval_cases j
  · have H := metricTensorNorm_singleTraceEval_le compositionWord G hG
      (tensorConcatProduct (A z) (A z))
    rw [metricTensorNorm_concatProduct G hG] at H
    have hp00 := hp 0 0 (by omega) (by omega)
    change metricTensorNorm G (A z) * metricTensorNorm G (A z) ≤ B ^ 2 at hp00
    change metricTensorNorm G (singleTraceEval compositionWord G⁻¹
      (tensorConcatProduct (A z) (A z))) ≤ _
    apply H.trans
    have HH := mul_le_mul_of_nonneg_left hp00 hs
    nlinarith [mul_nonneg hs (sq_nonneg B)]
  · have H := covariantD_traceProduct_norm_le compositionWord k hk c A A hA hA hz
    have hp10 := hp 1 0 (by omega) (by omega)
    have hp01 := hp 0 1 (by omega) (by omega)
    dsimp only [jet] at hp10 hp01
    have hsum : metricTensorNorm G (covariantD k c A z) * metricTensorNorm G (A z) +
        metricTensorNorm G (A z) * metricTensorNorm G (covariantD k c A z) ≤ 4 * B ^ 2 := by
      nlinarith [sq_nonneg B]
    change metricTensorNorm G (covariantD k c (compositionField k c A) z) ≤ _
    exact H.trans (by dsimp only [G] at hsum; nlinarith [mul_le_mul_of_nonneg_left hsum hs])
  · have H := covariantD_twice_traceProduct_norm_le compositionWord k hk c A A hA hA hz
    have hp20 := hp 2 0 (by omega) (by omega)
    have hp11 := hp 1 1 (by omega) (by omega)
    have hp02 := hp 0 2 (by omega) (by omega)
    dsimp only [jet] at hp20 hp11 hp02
    have hsum : metricTensorNorm G (covariantD k c (covariantD k c A) z) * metricTensorNorm G (A z) +
        2 * metricTensorNorm G (covariantD k c A z) * metricTensorNorm G (covariantD k c A z) +
        metricTensorNorm G (A z) * metricTensorNorm G (covariantD k c (covariantD k c A) z) ≤
          4 * B ^ 2 := by nlinarith
    change metricTensorNorm G (covariantD k c (covariantD k c (compositionField k c A)) z) ≤ _
    exact H.trans (by dsimp only [G] at hsum; nlinarith [mul_le_mul_of_nonneg_left hsum hs])

end Yau.Proofs.C05RicciCubicJetsAux
