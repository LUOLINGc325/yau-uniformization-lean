import Yau.Proofs.P06HodgeRegularityScalarSystem

/-! Exact forward divergence conversion for scalar-principal systems.
The divergence correction is included in the first-order matrix. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff

namespace Yau.NodeProofs.P06Aux
open Yau.LeafProofs.L03

variable {E ι α : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Fintype ι] [Fintype α] [DecidableEq α]

def regularityScalarBeta (v : ι → E) (q : ι → ι → E → ℝ)
    (e1 : α → α → ι → E → ℝ) (r c : α) (i : ι) (z : E) : ℝ :=
  e1 r c i z + if r = c then ∑ j, regularityDirection (v j) (q j i) z else 0

theorem regularityScalarBeta_eq_forward (v : ι → E) (q : ι → ι → E → ℝ)
    (e1 : α → α → ι → E → ℝ) :
    regularityScalarBeta v q e1 = hodgeForwardB v (regularityScalarSystemA q) e1 := by
  funext r c i z
  by_cases hrc : r = c <;>
    simp only [regularityScalarBeta, hodgeForwardB, regularityScalarSystemA,
      hrc, ite_true, ite_false, fderiv_zero, Pi.zero_apply, zero_apply,
      Finset.sum_const_zero, regularityDirection]

theorem regularityScalarBeta_contDiff (v : ι → E) (q : ι → ι → E → ℝ)
    (e1 : α → α → ι → E → ℝ)
    (hq : ∀ i j, ContDiff ℝ ∞ (q i j))
    (he1 : ∀ r c i, ContDiff ℝ ∞ (e1 r c i)) (r c : α) (i : ι) :
    ContDiff ℝ ∞ (regularityScalarBeta v q e1 r c i) := by
  unfold regularityScalarBeta
  apply (he1 r c i).add
  by_cases hrc : r = c
  · simp only [hrc, ite_true]
    exact ContDiff.sum fun j _ => regularityDirection_contDiff (hq j i) (v j)
  · simpa only [hrc, ite_false] using
      (contDiff_const : ContDiff ℝ ∞ (fun _ : E => (0 : ℝ)))

theorem regularityScalarBeta_compact (v : ι → E) (q : ι → ι → E → ℝ)
    (e1 : α → α → ι → E → ℝ)
    (hcq : ∀ i j, HasCompactSupport (q i j))
    (hce1 : ∀ r c i, HasCompactSupport (e1 r c i)) (r c : α) (i : ι) :
    HasCompactSupport (regularityScalarBeta v q e1 r c i) := by
  classical
  unfold regularityScalarBeta
  apply (hce1 r c i).add
  by_cases hrc : r = c
  · simp only [hrc, ite_true]
    have h := HasCompactSupport.finset_sum (fun j (_ : j ∈ Finset.univ) =>
      (hcq j i).fderiv_apply ℝ (v j))
    convert h using 1
    funext z
    simp only [Finset.sum_apply, regularityDirection]
  · simp only [hrc, ite_false]
    exact HasCompactSupport.zero

theorem regularityScalarSystem_nondivergence
    (v : ι → E) (q : ι → ι → E → ℝ)
    (e1 : α → α → ι → E → ℝ) (e0 : α → α → E → ℝ) (U : E → α → ℝ)
    (hq : ∀ i j, ContDiff ℝ ∞ (q i j))
    (he1 : ∀ r c i, ContDiff ℝ ∞ (e1 r c i))
    (hU : ∀ c, ContDiff ℝ ∞ (fun z => U z c)) (z : E) (r : α) :
    regularityScalarSystem v q (regularityScalarBeta v q e1) e0 U z r =
      -(∑ i, ∑ j, q i j z * regularityDirection (v i)
        (regularityDirection (v j) (fun y => U y r)) z) +
      (∑ c, ∑ i, e1 r c i z * regularityDirection (v i) (fun y => U y c) z) +
      ∑ c, e0 r c z * U z c := by
  classical
  have ha (r c : α) (i j : ι) : ContDiff ℝ ∞ (regularityScalarSystemA q r c i j) := by
    by_cases hrc : r = c
    · simpa only [regularityScalarSystemA, hrc, ite_true] using hq i j
    · simp only [regularityScalarSystemA, hrc, ite_false]
      exact contDiff_const
  have hβ := regularityScalarBeta_contDiff v q e1 hq he1
  rw [← regularityScalarSystem_divergence v q (regularityScalarBeta v q e1) e0 U hβ hU]
  rw [regularityScalarBeta_eq_forward]
  change divergenceSystemApply v (regularityScalarSystemA q)
      (hodgeForwardB v (regularityScalarSystemA q) e1) (hodgeForwardC v (regularityScalarSystemA q) e1 e0) U z r = _
  rw [hodgeForward_divergence_eq v (regularityScalarSystemA q) e1 e0 U ha he1 hU]
  unfold hodgeForwardPrincipal
  simp only [Finset.sum_add_distrib]
  congr 2
  simp only [Finset.sum_neg_distrib]
  congr 1
  rw [Finset.sum_eq_single r]
  · simp only [regularityScalarSystemA, ite_true]
    rfl
  · intro c _ hcr
    simp only [regularityScalarSystemA, Ne.symm hcr, ite_false, Pi.zero_apply,
      zero_mul, Finset.sum_const_zero]
  · simp

end Yau.NodeProofs.P06Aux
