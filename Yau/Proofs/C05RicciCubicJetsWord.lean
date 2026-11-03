import Yau.Proofs.C05RicciSquareJetsGeneric

/-! The genuine two-trace Leibniz list needs only the first two input jets. -/
noncomputable section
open Filter
open scoped Topology Manifold ContDiff Matrix
namespace Yau.Proofs.C05RicciCubicJetsAux
open Yau Yau.Proofs.C05Aux Yau.LeafProofs.L12Aux Yau.LeafProofs.L23Aux
open Yau.Proofs.C05RicciSquareJetsAux.Generic
variable {n r s q m : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false

theorem word_term_norm_le_two (e : Term r s q m) (w : Word2 r s q) (hm : m ≤ 2)
    (k : HermitianField M) (c : M.Carrier)
    (A : ComplexVector n → CovTensor n r) (B : ComplexVector n → CovTensor n s)
    {z : ComplexVector n} (hz : z ∈ chartTarget c) {CA CB : ℝ} (hCA : 0 ≤ CA) (hCB : 0 ≤ CB)
    (hA : ∀ j ≤ 2, metricTensorNorm (realMetricFn k c z) (jet k c A j z) ≤ CA)
    (hB : ∀ j ≤ 2, metricTensorNorm (realMetricFn k c z) (jet k c B j z) ≤ CB) :
    metricTensorNorm (realMetricFn k c z) (e.eval k c A B z) ≤ (2*n:ℕ)*CA*CB := by
  have hl : e.leftOrder ≤ 2 := by have H := e.total w; omega
  have hr : e.rightOrder ≤ 2 := by have H := e.total w; omega
  have H := e.word.eval_norm_le (realMetricFn k c z) (realMetricFn_posDef k c z hz)
    (jet k c A e.leftOrder z) (jet k c B e.rightOrder z)
  have hp := mul_le_mul (hA _ hl) (hB _ hr)
    (metricTensorNorm_nonneg (realMetricFn k c z) (jet k c B e.rightOrder z)) hCA
  change metricTensorNorm _ (e.eval k c A B z) ≤
    (2*n:ℕ)*metricTensorNorm _ (jet k c A e.leftOrder z)*metricTensorNorm _ (jet k c B e.rightOrder z) at H
  calc
    _ ≤ _ := H
    _ = (2*n:ℕ)*(metricTensorNorm (realMetricFn k c z) (jet k c A e.leftOrder z)*
      metricTensorNorm (realMetricFn k c z) (jet k c B e.rightOrder z)) := by ring
    _ ≤ (2*n:ℕ)*(CA*CB) := mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg _)
    _ = _ := by ring

theorem word_covariantJet_norm_le_two (w : Word2 r s q) (k : HermitianField M)
    (hk : MetricSmooth k) (c : M.Carrier)
    (A : ComplexVector n → CovTensor n r) (B : ComplexVector n → CovTensor n s)
    (hA : ∀ v, ContDiffOn ℝ ∞ (fun z => A z v) (chartTarget c))
    (hB : ∀ v, ContDiffOn ℝ ∞ (fun z => B z v) (chartTarget c))
    {z : ComplexVector n} (hz : z ∈ chartTarget c) {CA CB : ℝ} (hCA : 0 ≤ CA) (hCB : 0 ≤ CB)
    (hJA : ∀ j ≤ 2, metricTensorNorm (realMetricFn k c z) (jet k c A j z) ≤ CA)
    (hJB : ∀ j ≤ 2, metricTensorNorm (realMetricFn k c z) (jet k c B j z) ≤ CB)
    (m : ℕ) (hm : m ≤ 2) :
    metricTensorNorm (realMetricFn k c z)
      (jet k c (fun u => w.eval (realMetricFn k c u)⁻¹ (A u) (B u)) m z) ≤
        4 * (2*n:ℕ) * CA * CB := by
  have hl (l : List (Term r s q m)) :
      metricTensorNorm (realMetricFn k c z) (evalTerms l k c A B z) ≤
        (l.length:ℝ)*(2*n:ℕ)*CA*CB := by
    induction l with
    | nil => simp [evalTerms,metricTensorNorm,sqrt_covTensorNormSq_zero]
    | cons e l ih =>
        have H := sqrt_covTensorNormSq_add_le (realMetricFn k c z) (realMetricFn_posDef k c z hz)
          (e.eval k c A B z) (evalTerms l k c A B z)
        change metricTensorNorm _ (_ + _) ≤ metricTensorNorm _ _ + metricTensorNorm _ _ at H
        calc
          _ ≤ _ := H
          _ ≤ (2*n:ℕ)*CA*CB+(l.length:ℝ)*(2*n:ℕ)*CA*CB :=
            add_le_add (word_term_norm_le_two e w hm k c A B hz hCA hCB hJA hJB) ih
          _ = _ := by simp only [List.length_cons,Nat.cast_add,Nat.cast_one]; ring
  rw [jet_word_eval w k hk c A B hA hB m hz]
  have hc : ((terms w m).length:ℝ) ≤ 4 := by rw [terms_length]; interval_cases m <;> norm_num
  have H := mul_le_mul_of_nonneg_right hc
    (mul_nonneg (mul_nonneg (Nat.cast_nonneg (2*n)) hCA) hCB)
  exact (hl (terms w m)).trans (by simpa only [mul_assoc] using H)

end Yau.Proofs.C05RicciCubicJetsAux
