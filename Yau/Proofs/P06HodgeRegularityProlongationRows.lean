import Yau.Proofs.P06HodgeRegularityScalarTranspose
import Yau.Proofs.P06HodgeRegularityTestAlgebra

/-! The actual transposed rows of the prolonged finite system. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff

namespace Yau.NodeProofs.P06Aux

variable {E ι α : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Fintype ι] [Fintype α] [DecidableEq ι] [DecidableEq α]

@[simp] theorem regularityDirection_zero (e : E) :
    regularityDirection e (fun _ : E => (0 : ℝ)) = 0 := by
  funext z
  simp [regularityDirection]

theorem regularityDirection_sub {u w : E → ℝ}
    (hu : ContDiff ℝ ∞ u) (hw : ContDiff ℝ ∞ w) (e : E) :
    regularityDirection e (fun z => u z - w z) =
      fun z => regularityDirection e u z - regularityDirection e w z := by
  funext z
  rw [regularityDirection, fderiv_fun_sub (hu.differentiable (by simp) z) (hw.differentiable (by simp) z)]
  rfl

theorem regularityProlongE1_test_derivative
    (v : ι → E) (q : ι → ι → E → ℝ) (e1 : α → α → ι → E → ℝ)
    (hq : ∀ i j, ContDiff ℝ ∞ (q i j)) (he1 : ∀ r c i, ContDiff ℝ ∞ (e1 r c i))
    (φ : E → ℝ) (hφ : ContDiff ℝ ∞ φ) (r c : α) (ell j i : ι) (z : E) :
    regularityDirection (v i)
      (fun y => regularityProlongE1 v q e1 (r,some ell) (c,some j) i y * φ y) z =
      (if j = ell then regularityDirection (v i) (fun y => e1 r c i y * φ y) z else 0) -
        if r = c then regularityDirection (v i)
          (fun y => regularityDirection (v ell) (q i j) y * φ y) z else 0 := by
  let a := fun y => if j = ell then e1 r c i y else 0
  let b := fun y => if r = c then regularityDirection (v ell) (q i j) y else 0
  have ha : ContDiff ℝ ∞ a := by
    by_cases h : j = ell
    · simpa only [a, h, ite_true] using he1 r c i
    · simp only [a, h, ite_false]
      exact contDiff_const
  have hb : ContDiff ℝ ∞ b := by
    by_cases h : r = c
    · simpa only [b, h, ite_true] using regularityDirection_contDiff (hq i j) (v ell)
    · simp only [b, h, ite_false]
      exact contDiff_const
  have hfun : (fun y => regularityProlongE1 v q e1 (r,some ell) (c,some j) i y * φ y) =
      fun y => a y * φ y - b y * φ y := by
    funext y
    simp only [regularityProlongE1, a, b]
    ring
  rw [hfun, regularityDirection_sub (ha.mul hφ) (hb.mul hφ) (v i)]
  by_cases hj : j = ell <;> by_cases hr : r = c <;>
    simp only [a, b, hj, hr, ite_true, ite_false, zero_mul, regularityDirection_zero,
      Pi.zero_apply, sub_zero, zero_sub]

theorem regularityProlongTranspose_some_some
    (v : ι → E) (q : ι → ι → E → ℝ)
    (e1 : α → α → ι → E → ℝ) (e0 : α → α → E → ℝ)
    (hq : ∀ i j, ContDiff ℝ ∞ (q i j)) (he1 : ∀ r c i, ContDiff ℝ ∞ (e1 r c i))
    (φ : E → ℝ) (hφ : ContDiff ℝ ∞ φ) (z : E) (r c : α) (ell j : ι) :
    regularityScalarTranspose v q (regularityProlongE1 v q e1) (regularityProlongE0 v e1 e0)
      φ z (r,some ell) (c,some j) =
      (if j = ell then regularityScalarTranspose v q e1 e0 φ z r c else 0) +
        regularityProlongK v q e1 φ ell r c j z := by
  classical
  have hcond : ((r,some ell) : α × Option ι) = (c,some j) ↔ r = c ∧ j = ell := by
    simp only [Prod.mk.injEq, Option.some.injEq, eq_comm (a := ell) (b := j)]
  unfold regularityScalarTranspose
  simp_rw [regularityProlongE1_test_derivative v q e1 hq he1 φ hφ r c ell j]
  simp only [hcond, regularityProlongE0, regularityProlongK]
  by_cases hr : r = c <;> by_cases hj : j = ell <;>
    simp only [hr, hj, ite_true, ite_false, and_true, and_false, true_and, false_and,
      Finset.sum_sub_distrib, Finset.sum_neg_distrib, Finset.sum_const_zero,
      zero_sub, sub_zero, zero_add, add_zero, zero_mul] <;> ring

variable [MeasurableSpace E] [BorelSpace E]

theorem regularityProlongH_test
    (v : ι → E) (e0 : α → α → E → ℝ) (he0 : ∀ r c, ContDiff ℝ ∞ (e0 r c))
    {O : Set E} {φ : E → ℝ} (hφ : regularityTest O φ) (ell : ι) (r c : α) :
    regularityTest O (regularityProlongH v e0 φ ell r c) :=
  regularityTest_coeff_mul hφ (regularityDirection_contDiff (he0 r c) (v ell))

theorem regularityProlongK_test
    (v : ι → E) (q : ι → ι → E → ℝ) (e1 : α → α → ι → E → ℝ)
    (hq : ∀ i j, ContDiff ℝ ∞ (q i j)) (he1 : ∀ r c i, ContDiff ℝ ∞ (e1 r c i))
    {O : Set E} {φ : E → ℝ} (hφ : regularityTest O φ) (ell : ι) (r c : α) (j : ι) :
    regularityTest O (regularityProlongK v q e1 φ ell r c j) := by
  unfold regularityProlongK
  apply regularityTest_add
  · by_cases hrc : r = c
    · simp only [hrc, ite_true]
      apply regularityTest_sum
      intro i
      exact regularityTest_direction
        (regularityTest_coeff_mul hφ (regularityDirection_contDiff (hq i j) (v ell))) (v i)
    · simp only [hrc, ite_false]
      exact (regularityTestSpace O).zero_mem
  · exact regularityTest_coeff_mul hφ (regularityDirection_contDiff (he1 r c j) (v ell))

end Yau.NodeProofs.P06Aux
