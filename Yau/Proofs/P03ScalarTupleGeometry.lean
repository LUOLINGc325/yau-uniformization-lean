import Yau.Proofs.P03ChartDifferentials
import Yau.Proofs.P03DerivativeEvaluation

open scoped Manifold Topology
open Set

noncomputable section

namespace Yau.NodeProofs.P03Aux

variable {n N : ℕ} {M : ComplexManifold n}

def scalarTupleMap (f : Fin N → holomorphicFunctions M) (x : M.Carrier) : ComplexVector N :=
  WithLp.toLp 2 (fun j => (f j).1 x)

theorem scalarTupleMap_holomorphic (f : Fin N → holomorphicFunctions M) :
    IsHolomorphicVecMap (scalarTupleMap f) := by
  apply (mdifferentiable_iff_chartDifferentiable (scalarTupleMap f)).mpr
  intro a
  apply (differentiableOn_piLp 2).mpr
  intro j
  exact (mdifferentiable_iff_chartDifferentiable
    ((f j).1 : M.Carrier → ℂ)).mp (f j).2 a

theorem scalarTupleMap_chart_hasFDerivAt (f : Fin N → holomorphicFunctions M)
    (a : M.Carrier) (z : ComplexVector n) (hz : z ∈ chartTarget a) :
    HasFDerivAt (inChart a (scalarTupleMap f))
      (((PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin N => ℂ)).symm.toContinuousLinearMap).comp
        (tupleDerivativeCLM a f z)) z := by
  have hD : HasFDerivAt (fun w j => (f j).1 (chartInv a w))
      (tupleDerivativeCLM a f z) z := by
    apply hasFDerivAt_pi.mpr
    intro j
    exact (((mdifferentiable_iff_chartDifferentiable
      ((f j).1 : M.Carrier → ℂ)).mp (f j).2 a).differentiableAt
        ((isOpen_extChartAt_target a).mem_nhds hz)).hasFDerivAt
  exact (PiLp.hasFDerivAt_toLp (𝕜 := ℂ) 2 _).comp z hD

theorem scalarTupleMap_chart_derivative_injective (f : Fin N → holomorphicFunctions M)
    (a : M.Carrier) (z : ComplexVector n) (hz : z ∈ chartTarget a)
    (hinj : Function.Injective (tupleDerivativeCLM a f z)) :
    Function.Injective (fderiv ℂ (inChart a (scalarTupleMap f)) z) := by
  rw [(scalarTupleMap_chart_hasFDerivAt f a z hz).fderiv]
  exact (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin N => ℂ)).symm.injective.comp hinj

theorem scalarTupleMap_intrinsic_derivative_injective (f : Fin N → holomorphicFunctions M)
    (a x : M.Carrier) (hx : x ∈ (extChartAt (ComplexModel n) a).source)
    (hinj : Function.Injective (tupleDerivativeCLM a f (chartPt a x))) :
    Function.Injective (mfderiv (ComplexModel n) (ComplexModel N) (scalarTupleMap f) x) := by
  have hDF := scalarTupleMap_chart_derivative_injective f a (chartPt a x)
    ((extChartAt (ComplexModel n) a).map_source hx) hinj
  rw [chartDerivative_eq_intrinsic_comp (scalarTupleMap f) (scalarTupleMap_holomorphic f)
    a x hx] at hDF
  intro v w hvw
  obtain ⟨v', rfl⟩ := (chartFrameEquiv a x hx).surjective v
  obtain ⟨w', rfl⟩ := (chartFrameEquiv a x hx).surjective w
  exact congrArg (chartFrameEquiv a x hx) (hDF hvw)

end Yau.NodeProofs.P03Aux
