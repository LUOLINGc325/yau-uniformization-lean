import Yau.LeafProofs.L23TensorCalculus

/-! Finite tensor inner products and the weak, local coefficient calculus.
All smoothness hypotheses in this module concern the actual Hermitian field. -/

noncomputable section
open scoped Topology ContDiff Matrix

namespace Yau.LeafProofs.L23Aux

variable {n : ℕ} {M : ComplexManifold n}

def covTensorPair {r : ℕ} (G : Matrix (RIdx n) (RIdx n) ℝ)
    (A B : CovTensor n r) : ℝ :=
  ∑ v : Fin r → RIdx n, ∑ w : Fin r → RIdx n,
    A v * B w * ∏ j : Fin r, G⁻¹ (v j) (w j)

theorem covTensorPair_self {r : ℕ} (G : Matrix (RIdx n) (RIdx n) ℝ)
    (A : CovTensor n r) : covTensorPair G A A = covTensorNormSq G A := rfl

theorem covTensorPair_sq_le {r : ℕ} (G : Matrix (RIdx n) (RIdx n) ℝ)
    (hG : G.PosDef) (A B : CovTensor n r) :
    covTensorPair G A B ^ 2 ≤ covTensorNormSq G A * covTensorNormSq G B := by
  obtain ⟨D, hD⟩ := inverseMetric_exists_gram_factor G hG
  unfold covTensorPair covTensorNormSq
  simp only [tensor_contraction_eq_frame_sum _ D hD]
  simpa only [pow_two] using
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (tensorFrameTransform D A) (tensorFrameTransform D B)

theorem covTensorPair_le_sqrt {r : ℕ} (G : Matrix (RIdx n) (RIdx n) ℝ)
    (hG : G.PosDef) (A B : CovTensor n r) :
    covTensorPair G A B ≤ Real.sqrt (covTensorNormSq G A) *
      Real.sqrt (covTensorNormSq G B) := by
  obtain ⟨D, hD⟩ := inverseMetric_exists_gram_factor G hG
  unfold covTensorPair covTensorNormSq
  simp only [tensor_contraction_eq_frame_sum _ D hD]
  simpa only [pow_two] using
    Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
      (tensorFrameTransform D A) (tensorFrameTransform D B)

theorem realMetricFn_inverse_contDiffOn (h : HermitianField M) (hh : MetricSmooth h)
    (x : M.Carrier) (a b : RIdx n) :
    ContDiffOn ℝ ∞ (fun z => (realMetricFn h x z)⁻¹ a b) (chartTarget x) :=
  L12Aux.contDiffOn_matrix_inv (hh x)
    (fun z hz => (L12Aux.realMetricFn_posDef h x z hz).det_pos.ne') a b

theorem christoffel_contDiffOn (h : HermitianField M) (hh : MetricSmooth h)
    (x : M.Carrier) (c a b : RIdx n) :
    ContDiffOn ℝ ∞ (fun z => christoffel h x z c a b) (chartTarget x) := by
  apply contDiffOn_const.mul
  apply ContDiffOn.sum
  intro d _
  apply (realMetricFn_inverse_contDiffOn h hh x c d).mul
  have hO := isOpen_extChartAt_target (I := ComplexModel n) x
  exact ((L12Aux.rDeriv_contDiffOn hO (hh x b d) a).add
    (L12Aux.rDeriv_contDiffOn hO (hh x a d) b)).sub
      (L12Aux.rDeriv_contDiffOn hO (hh x a b) d)

theorem riemannCoeff_contDiffOn (h : HermitianField M) (hh : MetricSmooth h)
    (x : M.Carrier) (i j k l : RIdx n) :
    ContDiffOn ℝ ∞ (fun z => riemannCoeff h x z i j k l) (chartTarget x) := by
  have hO := isOpen_extChartAt_target (I := ComplexModel n) x
  apply ((L12Aux.rDeriv_contDiffOn hO (christoffel_contDiffOn h hh x l j k) i).sub
    (L12Aux.rDeriv_contDiffOn hO (christoffel_contDiffOn h hh x l i k) j)).add
  apply ContDiffOn.sum
  intro m _
  exact ((christoffel_contDiffOn h hh x m j k).mul
    (christoffel_contDiffOn h hh x l i m)).sub
    ((christoffel_contDiffOn h hh x m i k).mul
      (christoffel_contDiffOn h hh x l j m))

theorem covariantD_contDiffOn {r : ℕ} (h : HermitianField M) (hh : MetricSmooth h)
    (x : M.Carrier) (A : ComplexVector n → CovTensor n r)
    (hA : ∀ v, ContDiffOn ℝ ∞ (fun z => A z v) (chartTarget x))
    (v : Fin (r+1) → RIdx n) :
    ContDiffOn ℝ ∞ (fun z => covariantD h x A z v) (chartTarget x) := by
  apply (L12Aux.rDeriv_contDiffOn (isOpen_extChartAt_target (I := ComplexModel n) x)
    (hA (fun i => v i.succ)) (v 0)).sub
  apply ContDiffOn.sum
  intro j _
  apply ContDiffOn.sum
  intro b _
  exact (christoffel_contDiffOn h hh x b (v 0) (v j.succ)).mul
    (hA (Function.update (fun i => v i.succ) j b))

theorem rmTensor_contDiffOn (h : HermitianField M) (hh : MetricSmooth h)
    (x : M.Carrier) (v : Fin 4 → RIdx n) :
    ContDiffOn ℝ ∞ (fun z => rmTensor h x z v) (chartTarget x) := by
  apply ContDiffOn.sum
  intro l _
  exact (hh x l (v 3)).mul (riemannCoeff_contDiffOn h hh x (v 0) (v 1) (v 2) l)

theorem rmJet_contDiffOn (h : HermitianField M) (hh : MetricSmooth h)
    (x : M.Carrier) (k : ℕ) (v : Fin (4+k) → RIdx n) :
    ContDiffOn ℝ ∞ (fun z => rmJet h x k z v) (chartTarget x) := by
  induction k with
  | zero => exact rmTensor_contDiffOn h hh x v
  | succ k ih => exact covariantD_contDiffOn h hh x (rmJet h x k) ih v

theorem chartJetSq_contDiffOn (h : HermitianField M) (hh : MetricSmooth h)
    (x : M.Carrier) (k : ℕ) :
    ContDiffOn ℝ ∞ (fun z => covTensorNormSq (realMetricFn h x z) (rmJet h x k z))
      (chartTarget x) := by
  apply ContDiffOn.sum
  intro v _
  apply ContDiffOn.sum
  intro w _
  apply ((rmJet_contDiffOn h hh x k v).mul (rmJet_contDiffOn h hh x k w)).mul
  apply contDiffOn_prod
  intro j _
  exact realMetricFn_inverse_contDiffOn h hh x (v j) (w j)

end Yau.LeafProofs.L23Aux
