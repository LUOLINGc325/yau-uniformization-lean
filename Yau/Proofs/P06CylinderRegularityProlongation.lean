import Yau.Proofs.P06HodgeRegularityProlongationCoefficients
import Yau.Proofs.P06HodgeRegularityWordCalculus

/-! Classical prolongation of the computed scalar-principal system. All
derivatives in this module are actual derivatives of smooth functions. -/
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
open MeasureTheory Filter
open scoped Topology ContDiff

namespace Yau.NodeProofs.P06Aux.CylinderReg

variable {E ι α : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Fintype ι] [Fintype α] [DecidableEq ι] [DecidableEq α]

theorem direction_fun_neg (e : E) (u : E → ℝ) :
    regularityDirection e (fun z => -u z) = fun z => -regularityDirection e u z := by
  funext z
  simp only [regularityDirection, fderiv_fun_neg, ContinuousLinearMap.neg_apply]

def systemOperator (v : ι → E) (q : ι → ι → E → ℝ)
    (e1 : α → α → ι → E → ℝ) (e0 : α → α → E → ℝ)
    (U : E → α → ℝ) (z : E) (r : α) : ℝ :=
  -(∑ i, ∑ j, q i j z * regularityDirection (v i)
    (regularityDirection (v j) (fun y => U y r)) z) +
  (∑ c, ∑ i, e1 r c i z * regularityDirection (v i) (fun y => U y c) z) +
    ∑ c, e0 r c z * U z c

theorem systemOperator_contDiff (v : ι → E) (q : ι → ι → E → ℝ)
    (e1 : α → α → ι → E → ℝ) (e0 : α → α → E → ℝ) (U : E → α → ℝ)
    (hq : ∀ i j, ContDiff ℝ ∞ (q i j))
    (he1 : ∀ r c i, ContDiff ℝ ∞ (e1 r c i))
    (he0 : ∀ r c, ContDiff ℝ ∞ (e0 r c))
    (hU : ∀ c, ContDiff ℝ ∞ (fun z => U z c)) (r : α) :
    ContDiff ℝ ∞ (fun z => systemOperator v q e1 e0 U z r) := by
  exact ((ContDiff.sum fun i _ => ContDiff.sum fun j _ =>
    (hq i j).mul (regularityDirection_contDiff (regularityDirection_contDiff (hU r)
      (v j)) (v i))).neg.add
    (ContDiff.sum fun c _ => ContDiff.sum fun i _ =>
      (he1 r c i).mul (regularityDirection_contDiff (hU c) (v i)))).add
    (ContDiff.sum fun c _ => (he0 r c).mul (hU c))

theorem direction_second_commute (v : ι → E) {u : E → ℝ}
    (hu : ContDiff ℝ ∞ u) (ell i j : ι) :
    regularityDirection (v ell) (regularityDirection (v i) (regularityDirection (v j) u)) =
      regularityDirection (v i) (regularityDirection (v j) (regularityDirection (v ell) u)) := by
  rw [regularityDirection_commute (regularityDirection_contDiff hu (v j)) (v ell) (v i),
    regularityDirection_commute hu (v ell) (v j)]

theorem systemOperator_derivative (v : ι → E) (q : ι → ι → E → ℝ)
    (e1 : α → α → ι → E → ℝ) (e0 : α → α → E → ℝ) (U : E → α → ℝ)
    (hq : ∀ i j, ContDiff ℝ ∞ (q i j))
    (he1 : ∀ r c i, ContDiff ℝ ∞ (e1 r c i))
    (he0 : ∀ r c, ContDiff ℝ ∞ (e0 r c))
    (hU : ∀ c, ContDiff ℝ ∞ (fun z => U z c)) (ell : ι) (r : α) :
    regularityDirection (v ell) (fun z => systemOperator v q e1 e0 U z r) =
      fun z => systemOperator v q e1 e0
        (fun y c => regularityDirection (v ell) (fun s => U s c) y) z r -
      (∑ i, ∑ j, regularityDirection (v ell) (q i j) z * regularityDirection (v i)
        (regularityDirection (v j) (fun y => U y r)) z) +
      (∑ c, ∑ i, regularityDirection (v ell) (e1 r c i) z *
        regularityDirection (v i) (fun y => U y c) z) +
      ∑ c, regularityDirection (v ell) (e0 r c) z * U z c := by
  have hSecond (i j : ι) : ContDiff ℝ ∞
      (fun z => q i j z * regularityDirection (v i)
        (regularityDirection (v j) (fun y => U y r)) z) :=
    (hq i j).mul (regularityDirection_contDiff (regularityDirection_contDiff (hU r) (v j)) (v i))
  have hFirst (c : α) (i : ι) : ContDiff ℝ ∞
      (fun z => e1 r c i z * regularityDirection (v i) (fun y => U y c) z) :=
    (he1 r c i).mul (regularityDirection_contDiff (hU c) (v i))
  have hZeroth (c : α) : ContDiff ℝ ∞ (fun z => e0 r c z * U z c) :=
    (he0 r c).mul (hU c)
  have hS : ContDiff ℝ ∞ (fun z => ∑ i, ∑ j, q i j z * regularityDirection (v i)
      (regularityDirection (v j) (fun y => U y r)) z) :=
    ContDiff.sum fun i _ => ContDiff.sum fun j _ => hSecond i j
  have hF : ContDiff ℝ ∞ (fun z => ∑ c, ∑ i, e1 r c i z *
      regularityDirection (v i) (fun y => U y c) z) :=
    ContDiff.sum fun c _ => ContDiff.sum fun i _ => hFirst c i
  have hZ : ContDiff ℝ ∞ (fun z => ∑ c, e0 r c z * U z c) :=
    ContDiff.sum fun c _ => hZeroth c
  change regularityDirection (v ell)
    (fun z => -(∑ i, ∑ j, q i j z * regularityDirection (v i)
      (regularityDirection (v j) (fun y => U y r)) z) +
    (∑ c, ∑ i, e1 r c i z * regularityDirection (v i) (fun y => U y c) z) +
      ∑ c, e0 r c z * U z c) = _
  rw [regularityDirection_add (hS.neg.add hF) hZ (v ell),
    regularityDirection_add hS.neg hF (v ell), direction_fun_neg,
    regularityDirection_sum _ (fun i => ContDiff.sum fun j _ => hSecond i j) (v ell),
    regularityDirection_sum _ (fun c => ContDiff.sum fun i _ => hFirst c i) (v ell),
    regularityDirection_sum _ hZeroth (v ell)]
  simp_rw [regularityDirection_sum _ (fun j => hSecond _ j) (v ell),
    regularityDirection_sum _ (fun i => hFirst _ i) (v ell),
    regularityDirection_mul (hq _ _)
      (regularityDirection_contDiff (regularityDirection_contDiff (hU r) _) _) (v ell),
    regularityDirection_mul (he1 _ _ _) (regularityDirection_contDiff (hU _) _) (v ell),
    regularityDirection_mul (he0 _ _) (hU _) (v ell),
    direction_second_commute v (hU r) ell,
    regularityDirection_commute (hU _) (v ell)]
  funext z
  simp only [systemOperator, Pi.add_apply, Pi.neg_apply, Finset.sum_add_distrib]
  ring

theorem systemOperator_prolong_none (v : ι → E) (q : ι → ι → E → ℝ)
    (e1 : α → α → ι → E → ℝ) (e0 : α → α → E → ℝ) (U : E → α → ℝ)
    (z : E) (r : α) :
    systemOperator v q (regularityProlongE1 v q e1) (regularityProlongE0 v e1 e0)
      (regularityProlongValue v U) z (r, none) = systemOperator v q e1 e0 U z r := by
  simp [systemOperator, regularityProlongValue, regularityProlongE1, regularityProlongE0,
    Fintype.sum_prod_type, Fintype.sum_option]

theorem systemOperator_prolong_some (v : ι → E) (q : ι → ι → E → ℝ)
    (e1 : α → α → ι → E → ℝ) (e0 : α → α → E → ℝ) (U : E → α → ℝ)
    (hq : ∀ i j, ContDiff ℝ ∞ (q i j))
    (he1 : ∀ r c i, ContDiff ℝ ∞ (e1 r c i))
    (he0 : ∀ r c, ContDiff ℝ ∞ (e0 r c))
    (hU : ∀ c, ContDiff ℝ ∞ (fun z => U z c)) (z : E) (r : α) (ell : ι) :
    systemOperator v q (regularityProlongE1 v q e1) (regularityProlongE0 v e1 e0)
      (regularityProlongValue v U) z (r, some ell) =
        regularityDirection (v ell) (fun y => systemOperator v q e1 e0 U y r) z := by
  rw [systemOperator_derivative v q e1 e0 U hq he1 he0 hU ell r]
  simp only [systemOperator, Fintype.sum_prod_type, Fintype.sum_option,
    regularityProlongValue, regularityProlongE1, regularityProlongE0,
    zero_mul, Finset.sum_const_zero, zero_add, sub_mul, add_mul,
    Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.sum_ite_eq,
    Finset.mem_univ, if_true]
  have hE1 : (∑ c, ∑ j, ∑ i, if j = ell then e1 r c i z *
      regularityDirection (v i) (fun y => regularityDirection (v j) (fun s => U s c) y) z else 0) =
      ∑ c, ∑ i, e1 r c i z * regularityDirection (v i)
        (fun y => regularityDirection (v ell) (fun s => U s c) y) z := by
    apply Finset.sum_congr rfl
    intro c _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have hQ : (∑ c, ∑ j, ∑ i, if r = c then regularityDirection (v ell) (q i j) z *
      regularityDirection (v i) (fun y => regularityDirection (v j) (fun s => U s c) y) z else 0) =
      ∑ i, ∑ j, regularityDirection (v ell) (q i j) z * regularityDirection (v i)
        (regularityDirection (v j) (fun y => U y r)) z := by
    rw [Finset.sum_eq_single r]
    · simp only [ite_true]
      exact Finset.sum_comm
    · intro c _ hcr
      simp only [Ne.symm hcr, ite_false, Finset.sum_const_zero]
    · simp
  rw [hE1, hQ]
  ring

end Yau.NodeProofs.P06Aux.CylinderReg
