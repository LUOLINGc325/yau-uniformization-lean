import Yau.LeafProofs.L14TwoAdjointGreen

set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Manifold Topology ContDiff Matrix ComplexOrder ENNReal
open MeasureTheory Bundle Filter Module
namespace Yau.LeafProofs.L14Aux
open BundleDbar
variable {n r : ℕ} {M : ComplexManifold n}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)] [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

def twoTensorCoordinates (a x : M.Carrier) (hx : x ∈ bundleChartSource (r := r) E a) :
    (antiComplexSubmodule E x 2) →ₗ[ℂ] EuclideanSpace ℂ (TwoCoefficientIndex n r) where
  toFun A := WithLp.toLp 2 (fun p => (localTriv (r := r) E a).continuousLinearMapAt ℂ x
    (((A.1 ![chartFrameBasis a x hx.1 p.1.2,chartFrameBasis a x hx.1 p.2]) (chartFrameBasis a x hx.1))) p.1.1)
  map_add' A B := by
    ext p
    simp only [Submodule.coe_add, WithLp.ofLp_toLp, AlternatingMap.add_apply, map_add, PiLp.add_apply]
  map_smul' c A := by
    ext p
    simp only [Submodule.coe_smul, WithLp.ofLp_toLp, AlternatingMap.smul_apply, map_smul, PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]

theorem twoTensorCoordinates_injective (a x : M.Carrier) (hx : x ∈ bundleChartSource (r := r) E a) :
    Function.Injective (twoTensorCoordinates (r := r) E a x hx) := by
  intro A B hAB
  let b := chartFrameBasis a x hx.1
  apply Subtype.ext
  apply AlternatingMap.ext
  intro vv
  have hvv : vv = ![vv 0,vv 1] := by ext t; fin_cases t <;> rfl
  rw [hvv, antiTwo_apply_basis_expansion b A.1 A.2, antiTwo_apply_basis_expansion b B.1 B.2]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  apply sub_eq_zero.mp
  apply alternating_eq_zero_of_apply_basis_eq_zero (bundleFrameBasis (r := r) E a x hx.2) b
  simp only [sub_apply]
  apply sub_eq_zero.mpr
  apply ((localTriv (r := r) E a).continuousLinearEquivAt ℂ x hx.2).injective
  rw [(localTriv (r := r) E a).coe_continuousLinearEquivAt_eq (R := ℂ) hx.2]
  apply PiLp.ext
  intro α
  have hc := congrArg (fun v : EuclideanSpace ℂ (TwoCoefficientIndex n r) => v ((α,i),j)) hAB
  exact hc

theorem twoTensorCoordinates_at_chartPt (W : NQForm E 2) (a x : M.Carrier)
    (hx : x ∈ bundleChartSource (r := r) E a) (i j : Fin n) (α : Fin r) :
    twoTensorCoordinates (r := r) E a x hx (W x) ((α,i),j) =
      coefficients (r := r) E W a (chartPt a x) ![i,j] α := by
  rw [coefficients_at_chartPt E W a x hx.1]
  change (localTriv (r := r) E a).continuousLinearMapAt ℂ x
    (((W x).1 ![chartFrameBasis a x hx.1 i,chartFrameBasis a x hx.1 j]) (chartFrameBasis a x hx.1)) α = _
  have ha : ![chartFrameBasis a x hx.1 i,chartFrameBasis a x hx.1 j] =
      (fun t : Fin 2 => chartVec a x (stdVec (![i,j] t))) := by
    ext t
    fin_cases t
    · exact chartFrameBasis_apply a x hx.1 i
    · exact chartFrameBasis_apply a x hx.1 j
  have hh : (chartFrameBasis a x hx.1 : Fin n → TangentVector M x) = fun k => chartVec a x (stdVec k) :=
    funext fun k => chartFrameBasis_apply a x hx.1 k
  rw [ha, hh]

theorem twoForm_eq_of_chart_coefficients (u v : NQForm E 2) (a : M.Carrier)
    (hzero : ∀ x, x ∉ bundleChartSource (r := r) E a → u x = v x)
    (hcoeff : ∀ z ∈ localDomain (r := r) E a, ∀ i j α,
      coefficients (r := r) E u a z ![i,j] α = coefficients (r := r) E v a z ![i,j] α) : u = v := by
  funext x
  by_cases hx : x ∈ bundleChartSource (r := r) E a
  · have hz : chartPt a x ∈ localDomain (r := r) E a := by
      refine ⟨(extChartAt (ComplexModel n) a).map_source hx.1, ?_⟩
      change chartInv a (chartPt a x) ∈ (localTriv (r := r) E a).baseSet
      rw [chartInv_chartPt_of_mem a x (by simpa only [extChartAt_source] using hx.1)]
      exact hx.2
    apply twoTensorCoordinates_injective E a x hx
    ext p
    rcases p with ⟨⟨α,i⟩,j⟩
    rw [twoTensorCoordinates_at_chartPt E u a x hx i j α, twoTensorCoordinates_at_chartPt E v a x hx i j α]
    exact hcoeff (chartPt a x) hz i j α
  · exact hzero x hx

theorem coefficients_two_skew (W : NQForm E 2) (a : M.Carrier) (z : ComplexVector n)
    (i j : Fin n) (α : Fin r) :
    coefficients (r := r) E W a z ![j,i] α = -coefficients (r := r) E W a z ![i,j] α := by
  let x := chartInv a z
  let vv := fun t : Fin 2 => chartVec a x (stdVec (![i,j] t))
  have hv : vv ∘ Equiv.swap (0 : Fin 2) 1 = fun t : Fin 2 => chartVec a x (stdVec (![j,i] t)) := by
    ext t
    fin_cases t <;> rfl
  have he := (W x).1.map_swap vv (by decide : (0 : Fin 2) ≠ 1)
  rw [hv] at he
  have hh := congrArg (fun T : (TangentVector M x) [⋀^Fin n]→ₗ[ℂ] E x =>
    (localTriv (r := r) E a).continuousLinearMapAt ℂ x (T (fun k => chartVec a x (stdVec k))) α) he
  simpa only [coefficients, vv, x, AlternatingMap.neg_apply, map_neg, PiLp.neg_apply] using hh

end Yau.LeafProofs.L14Aux
