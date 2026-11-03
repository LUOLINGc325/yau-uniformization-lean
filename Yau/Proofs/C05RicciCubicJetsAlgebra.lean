import Yau.Proofs.C05RicciCubicJetsComposition
import Yau.Proofs.C05MetricTracePowers

/-! The same single and double traces compute the actual cubic Ricci invariant. -/
noncomputable section
open Filter
open scoped Topology Manifold ContDiff Matrix
namespace Yau.Proofs.C05RicciCubicJetsAux
open Yau Yau.Proofs.C05Aux Yau.LeafProofs.L12Aux Yau.LeafProofs.L23Aux
open Yau.Proofs.C05RicciSquareJetsAux
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {M : ComplexManifold n}

theorem compositionWord_matrix (G A : Matrix (RIdx n) (RIdx n) ℝ)
    (v : Fin 2 → RIdx n) :
    singleTraceEval compositionWord G⁻¹
      (tensorConcatProduct (matrixCovTensor A) (matrixCovTensor A)) v =
        matrixCovTensor (A * G⁻¹ * A) v := by
  unfold singleTraceEval tensorConcatProduct matrixCovTensor
  change (∑ a : RIdx n, ∑ b : RIdx n, G⁻¹ a b * (A (v 0) a * A b (v 1))) =
    (A * G⁻¹ * A) (v 0) (v 1)
  rw [Matrix.mul_assoc]
  simp only [Matrix.mul_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem ricciSquareWord_eval_pair (G : Matrix (RIdx n) (RIdx n) ℝ)
    (C A : CovTensor n 2) (v : Fin 0 → RIdx n) :
    ricciSquareWord.eval G⁻¹ C A v = covTensorPair G C A := by
  unfold Word2.eval covTensorPair
  rw [← (pairFunctionEquiv (RIdx n)).symm.sum_comp]
  simp only [Fintype.sum_prod_type, pairFunctionEquiv, ricciSquareWord, Equiv.coe_fn_symm_mk,
    Sum.elim_inr, Fin.cases_zero, Fin.cases_succ, Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one]
  rfl

def cubicField (k : HermitianField M) (c : M.Carrier) (z : ComplexVector n) : CovTensor n 0 :=
  ricciSquareWord.eval (realMetricFn k c z)⁻¹
    (compositionField k c (realRicciJet k c 0) z) (realRicciJet k c 0 z)

theorem cubicField_contDiffOn (k : HermitianField M) (hk : MetricSmooth k)
    (c : M.Carrier) (v : Fin 0 → RIdx n) :
    ContDiffOn ℝ ∞ (fun z => cubicField k c z v) (chartTarget c) :=
  ricciSquareWord.eval_contDiffOn k hk c _ _
    (compositionField_contDiffOn k hk c _ (realRicciJet_contDiffOn k hk c 0))
    (realRicciJet_contDiffOn k hk c 0) v

theorem cubicField_eq_tracePower (k : HermitianField M) (hk : MetricSmooth k)
    (c : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget c)
    (v : Fin 0 → RIdx n) : cubicField k c z v = realRicciTracePower k c 3 z := by
  let G := realMetricFn k c z
  let A := Matrix.of (realRicciCoeff k c z)
  have hA : realRicciJet k c 0 z = matrixCovTensor A := by funext u; rfl
  have hC : compositionField k c (realRicciJet k c 0) z = matrixCovTensor (A * G⁻¹ * A) := by
    funext u
    change singleTraceEval compositionWord G⁻¹
      (tensorConcatProduct (realRicciJet k c 0 z) (realRicciJet k c 0 z)) u = _
    rw [hA]
    exact compositionWord_matrix G A u
  have hAsym : A.IsSymm := by
    apply Matrix.IsSymm.ext
    intro a b
    exact (realRicciCoeff_symm k hk c hz a b).symm
  unfold cubicField
  rw [ricciSquareWord_eval_pair, hC, hA,
    covTensorPair_matrix G (A * G⁻¹ * A) A (Yau.LeafProofs.L18Aux.realMetricFn_isSymm k c z) hAsym]
  change (G⁻¹ * (A * G⁻¹ * A) * G⁻¹ * A).trace = ((G⁻¹ * A)^3).trace
  simp only [pow_succ, pow_zero, Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc]

def cubicJet (k : HermitianField M) (c : M.Carrier) :
    (m : ℕ) → ComplexVector n → CovTensor n m
  | 0 => cubicField k c
  | m+1 => covariantD k c (cubicJet k c m)

theorem cubicJet_contDiffOn (k : HermitianField M) (hk : MetricSmooth k)
    (c : M.Carrier) (m : ℕ) (v : Fin m → RIdx n) :
    ContDiffOn ℝ ∞ (fun z => cubicJet k c m z v) (chartTarget c) := by
  induction m with
  | zero => exact cubicField_contDiffOn k hk c v
  | succ m ih => exact covariantD_contDiffOn k hk c _ ih v

theorem scalarJet_ricciCube_eq (k : HermitianField M) (hk : MetricSmooth k)
    (hK : KahlerClosed k) (c : M.Carrier) (m : ℕ)
    {z : ComplexVector n} (hz : z ∈ chartTarget c) :
    scalarJet k (ricciCube k) c m z = fun v => (1/2:ℝ) * cubicJet k c m z v := by
  induction m generalizing z with
  | zero =>
      funext v
      change inChart c (ricciCube k) z = (1/2:ℝ) * cubicField k c z v
      rw [ricciCube_inChart k hk hK c hz, cubicField_eq_tracePower k hk c hz]
  | succ m ih =>
      have he : scalarJet k (ricciCube k) c m =ᶠ[𝓝 z]
          (fun u v => (1/2:ℝ) * cubicJet k c m u v) := by
        filter_upwards [(isOpen_extChartAt_target (I := ComplexModel n) c).mem_nhds hz] with u hu
        exact ih hu
      have hFd (v : Fin m → RIdx n) := ((cubicJet_contDiffOn k hk c m v).contDiffAt
        ((isOpen_extChartAt_target (I := ComplexModel n) c).mem_nhds hz)).differentiableAt (by simp)
      change covariantD k c (scalarJet k (ricciCube k) c m) z = _
      rw [covariantD_eventuallyEq k c _ _ z he, covariantD_const_mul_at k c _ z hFd]
      rfl

end Yau.Proofs.C05RicciCubicJetsAux
