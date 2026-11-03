import Yau.LeafProofs.L03DivergenceEnergy

/-! The forward divergence coefficients of a finite second-order system.
They retain the original zeroth-order term; no deficiency shift is added. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff

namespace Yau.NodeProofs.P06Aux
open Yau.LeafProofs.L03

section ForwardSystem
variable {E ι α : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Fintype ι] [Fintype α]

/-- Nondivergence second-order expression, with arbitrary finite fiber rank. -/
def hodgeForwardPrincipal (v : ι → E)
    (a : α → α → ι → ι → E → ℝ) (e1 : α → α → ι → E → ℝ)
    (e0 : α → α → E → ℝ) (U : E → α → ℝ) (z : E) (r : α) : ℝ :=
  ∑ c, (-(∑ i, ∑ j, a r c i j z *
      fderiv ℝ (fun y => fderiv ℝ (fun t => U t c) y (v j)) z (v i)) +
    (∑ i, e1 r c i z * fderiv ℝ (fun y => U y c) z (v i)) + e0 r c z * U z c)

/-- The first-order forward flux includes exactly the principal divergence. -/
def hodgeForwardB (v : ι → E) (a : α → α → ι → ι → E → ℝ)
    (e1 : α → α → ι → E → ℝ) (r c : α) (i : ι) (z : E) : ℝ :=
  e1 r c i z + ∑ j, fderiv ℝ (a r c j i) z (v j)

/-- The forward potential cancels the derivative of the first-order flux. -/
def hodgeForwardC (v : ι → E) (a : α → α → ι → ι → E → ℝ)
    (e1 : α → α → ι → E → ℝ) (e0 : α → α → E → ℝ)
    (r c : α) (z : E) : ℝ :=
  e0 r c z - ∑ i, fderiv ℝ (hodgeForwardB v a e1 r c i) z (v i)

theorem hodgeForwardB_contDiff
    (v : ι → E) (a : α → α → ι → ι → E → ℝ)
    (e1 : α → α → ι → E → ℝ)
    (ha : ∀ r c i j, ContDiff ℝ ∞ (a r c i j))
    (he1 : ∀ r c i, ContDiff ℝ ∞ (e1 r c i)) (r c : α) (i : ι) :
    ContDiff ℝ ∞ (hodgeForwardB v a e1 r c i) := by
  exact (he1 r c i).add (ContDiff.sum fun j _ =>
    ((ha r c j i).fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const)

theorem hodgeForwardC_contDiff
    (v : ι → E) (a : α → α → ι → ι → E → ℝ)
    (e1 : α → α → ι → E → ℝ) (e0 : α → α → E → ℝ)
    (ha : ∀ r c i j, ContDiff ℝ ∞ (a r c i j))
    (he1 : ∀ r c i, ContDiff ℝ ∞ (e1 r c i))
    (he0 : ∀ r c, ContDiff ℝ ∞ (e0 r c)) (r c : α) :
    ContDiff ℝ ∞ (hodgeForwardC v a e1 e0 r c) := by
  exact (he0 r c).sub (ContDiff.sum fun i _ =>
    ((hodgeForwardB_contDiff v a e1 ha he1 r c i).fderiv_right
      (m := ∞) (by simp)).clm_apply contDiff_const)

/-- Exact conversion to forward divergence form for smooth actual functions.
This algebraic identity does not use self-adjointness in a chosen fiber metric. -/
theorem hodgeForward_divergence_eq
    (v : ι → E) (a : α → α → ι → ι → E → ℝ)
    (e1 : α → α → ι → E → ℝ) (e0 : α → α → E → ℝ)
    (U : E → α → ℝ)
    (ha : ∀ r c i j, ContDiff ℝ ∞ (a r c i j))
    (he1 : ∀ r c i, ContDiff ℝ ∞ (e1 r c i))
    (hU : ∀ c, ContDiff ℝ ∞ (fun z => U z c)) (z : E) (r : α) :
    divergenceSystemApply v a (hodgeForwardB v a e1) (hodgeForwardC v a e1 e0) U z r =
      hodgeForwardPrincipal v a e1 e0 U z r := by
  classical
  unfold divergenceSystemApply hodgeForwardPrincipal
  apply Finset.sum_congr rfl
  intro c _
  have hProd (i j : ι) :
      fderiv ℝ (fun y => a r c i j y * fderiv ℝ (fun t => U t c) y (v j)) z (v i) =
      a r c i j z * fderiv ℝ (fun y => fderiv ℝ (fun t => U t c) y (v j)) z (v i) +
        fderiv ℝ (a r c i j) z (v i) * fderiv ℝ (fun t => U t c) z (v j) := by
    rw [fderiv_fun_mul ((ha r c i j).differentiable (by simp) z)
      ((((hU c).fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).differentiable (by simp) z)]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring
  have hFlux (i : ι) :
      fderiv ℝ (fun y => hodgeForwardB v a e1 r c i y * U y c) z (v i) =
      hodgeForwardB v a e1 r c i z * fderiv ℝ (fun y => U y c) z (v i) +
        fderiv ℝ (hodgeForwardB v a e1 r c i) z (v i) * U z c := by
    rw [fderiv_fun_mul
      ((hodgeForwardB_contDiff v a e1 ha he1 r c i).differentiable (by simp) z)
      ((hU c).differentiable (by simp) z)]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring
  simp_rw [hProd, hFlux]
  simp only [hodgeForwardC, hodgeForwardB, Finset.sum_add_distrib, add_mul,
    Finset.sum_mul, sub_mul]
  have hSwap :
      (∑ i, ∑ j, fderiv ℝ (a r c i j) z (v i) *
        fderiv ℝ (fun t => U t c) z (v j)) =
      ∑ i, ∑ j, fderiv ℝ (a r c j i) z (v j) *
        fderiv ℝ (fun t => U t c) z (v i) := Finset.sum_comm
  rw [hSwap]
  ring

end ForwardSystem

end Yau.NodeProofs.P06Aux
