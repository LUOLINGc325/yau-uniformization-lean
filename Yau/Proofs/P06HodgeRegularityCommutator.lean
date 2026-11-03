import Yau.Proofs.P06HodgeRegularityProlongationRows
import Yau.Proofs.P06HodgeRegularityWordOperator

/-! The exact transposed-test commutator. Only smooth coefficients and
tests are differentiated; the later weak-field argument uses integration. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff

namespace Yau.NodeProofs.P06Aux

variable {E ι α : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Fintype ι] [Fintype α] [DecidableEq ι] [DecidableEq α]

theorem regularityDirection_fun_neg {u : E → ℝ} (hu : ContDiff ℝ ∞ u) (e : E) :
    regularityDirection e (fun z => -u z) = fun z => -regularityDirection e u z := by
  change regularityDirection e (-u) = -regularityDirection e u
  exact regularityDirection_neg hu e

theorem regularityDoubleTranspose_derivative
    (v : ι → E) (q : ι → ι → E → ℝ) (hq : ∀ i j, ContDiff ℝ ∞ (q i j))
    {φ : E → ℝ} (hφ : ContDiff ℝ ∞ φ) (ell : ι) :
    regularityDirection (v ell) (fun z => ∑ i, ∑ j,
      regularityDirection (v j) (regularityDirection (v i) (fun y => q i j y * φ y)) z) =
    fun z => (∑ i, ∑ j, regularityDirection (v j) (regularityDirection (v i)
      (fun y => regularityDirection (v ell) (q i j) y * φ y)) z) +
      ∑ i, ∑ j, regularityDirection (v j) (regularityDirection (v i)
        (fun y => q i j y * regularityDirection (v ell) φ y)) z := by
  have h := regularityWordOperator_derivative v (fun p : ι × ι => q p.1 p.2)
    (fun p => [p.2,p.1]) (fun p => hq p.1 p.2) hφ ell
  unfold regularityWordOperator at h
  simpa only [regularityCoefficientWord, Fintype.sum_prod_type] using h

theorem regularitySingleTranspose_derivative
    (v : ι → E) (a : ι → E → ℝ) (ha : ∀ i, ContDiff ℝ ∞ (a i))
    {φ : E → ℝ} (hφ : ContDiff ℝ ∞ φ) (ell : ι) :
    regularityDirection (v ell) (fun z => ∑ i,
      regularityDirection (v i) (fun y => a i y * φ y) z) =
    fun z => (∑ i, regularityDirection (v i)
      (fun y => regularityDirection (v ell) (a i) y * φ y) z) +
      ∑ i, regularityDirection (v i) (fun y => a i y * regularityDirection (v ell) φ y) z := by
  have h := regularityWordOperator_derivative v a (fun i => [i]) ha hφ ell
  unfold regularityWordOperator at h
  simpa only [regularityCoefficientWord] using h

theorem regularityProlongK_divergence
    (v : ι → E) (q : ι → ι → E → ℝ) (e1 : α → α → ι → E → ℝ)
    (hq : ∀ i j, ContDiff ℝ ∞ (q i j)) (he1 : ∀ r c i, ContDiff ℝ ∞ (e1 r c i))
    {φ : E → ℝ} (hφ : ContDiff ℝ ∞ φ) (ell : ι) (r c : α) (z : E) :
    (∑ j, regularityDirection (v j) (regularityProlongK v q e1 φ ell r c j) z) =
      (if r = c then ∑ i, ∑ j, regularityDirection (v j) (regularityDirection (v i)
        (fun y => regularityDirection (v ell) (q i j) y * φ y)) z else 0) +
      ∑ j, regularityDirection (v j)
        (fun y => regularityDirection (v ell) (e1 r c j) y * φ y) z := by
  have hq' i j := (regularityDirection_contDiff (hq i j) (v ell)).mul hφ
  have he' j := (regularityDirection_contDiff (he1 r c j) (v ell)).mul hφ
  unfold regularityProlongK
  by_cases hrc : r = c
  · simp only [if_pos hrc]
    simp_rw [regularityDirection_add
      (ContDiff.sum fun i _ => regularityDirection_contDiff (hq' i _) (v i)) (he' _) (v _)]
    rw [Finset.sum_add_distrib]
    congr 1
    simp_rw [regularityDirection_sum _
      (fun i => regularityDirection_contDiff (hq' i _) (v i)) (v _)]
    exact Finset.sum_comm
  · simp only [if_neg hrc, zero_add]

theorem regularityTranspose_commutator
    (v : ι → E) (q : ι → ι → E → ℝ)
    (e1 : α → α → ι → E → ℝ) (e0 : α → α → E → ℝ)
    (hq : ∀ i j, ContDiff ℝ ∞ (q i j)) (he1 : ∀ r c i, ContDiff ℝ ∞ (e1 r c i))
    (he0 : ∀ r c, ContDiff ℝ ∞ (e0 r c))
    {φ : E → ℝ} (hφ : ContDiff ℝ ∞ φ) (ell : ι) (r c : α) (z : E) :
    regularityProlongH v e0 φ ell r c z -
      regularityDirection (v ell) (fun y => regularityScalarTranspose v q e1 e0 φ y r c) z -
      (∑ j, regularityDirection (v j) (regularityProlongK v q e1 φ ell r c j) z) =
      -regularityScalarTranspose v q e1 e0 (regularityDirection (v ell) φ) z r c := by
  have hP : ContDiff ℝ ∞ (fun z => ∑ i, ∑ j,
      regularityDirection (v j) (regularityDirection (v i) (fun y => q i j y * φ y)) z) :=
    ContDiff.sum fun i _ => ContDiff.sum fun j _ =>
      regularityDirection_contDiff (regularityDirection_contDiff ((hq i j).mul hφ) (v i)) (v j)
  have hL : ContDiff ℝ ∞ (fun z => ∑ i,
      regularityDirection (v i) (fun y => e1 r c i y * φ y) z) :=
    ContDiff.sum fun i _ => regularityDirection_contDiff ((he1 r c i).mul hφ) (v i)
  rw [regularityProlongK_divergence v q e1 hq he1 hφ]
  unfold regularityScalarTranspose
  by_cases hrc : r = c
  · simp only [if_pos hrc]
    rw [regularityDirection_add (hP.neg.sub hL) ((he0 r c).mul hφ),
      regularityDirection_sub hP.neg hL, regularityDirection_fun_neg hP,
      regularityDoubleTranspose_derivative v q hq hφ,
      regularitySingleTranspose_derivative v (e1 r c) (he1 r c) hφ,
      regularityDirection_mul (he0 r c) hφ]
    unfold regularityProlongH
    ring
  · simp only [if_neg hrc, neg_zero, zero_sub]
    rw [regularityDirection_add hL.neg ((he0 r c).mul hφ),
      regularityDirection_fun_neg hL,
      regularitySingleTranspose_derivative v (e1 r c) (he1 r c) hφ,
      regularityDirection_mul (he0 r c) hφ]
    unfold regularityProlongH
    ring

end Yau.NodeProofs.P06Aux
