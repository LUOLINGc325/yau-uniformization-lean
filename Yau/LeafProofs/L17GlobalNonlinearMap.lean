import Yau.LeafProofs.L17LocalNonlinearMap
import Yau.LeafProofs.L17LocalScalarAssembly

open Set Metric
open scoped Matrix.Norms.Frobenius ContDiff
noncomputable section
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17Aux
open L17HolderAux L17SchauderAux L17LocalHolderBanachAlgebraAux L17LocalScalarAssemblyAux
local instance globalNonlinearTopology (n : ℕ) : TopologicalSpace (Matrix (Fin n) (Fin n) ℂ) := leviMatrixTopology n
variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}
variable (P : UniformChartPartition g) (T γ : ℝ) (hT : 0<T)
variable (hTime : T≤P.radius^2) (hγ : 0≤γ) (hγ1 : γ≤1) (hr : P.radius≤1)

def nonlinearAssemblyCLM (J : LocalHolderSpace ℝ P T γ →L[ℝ] HolderSpace P T γ) :
    LocalHolderBanach ℝ P T γ →L[ℝ] HolderSpace P T γ :=
  J.comp (valueContinuousLinearEquiv ℝ P T γ).toContinuousLinearMap

theorem nonlinearAssemblyCLM_norm_le
    (J : LocalHolderSpace ℝ P T γ →L[ℝ] HolderSpace P T γ)
    (v : LocalHolderBanach ℝ P T γ) :
    ‖nonlinearAssemblyCLM P T γ J v‖≤(‖J‖/2)*‖v‖ := by
  change ‖J v.value‖≤_
  calc
    _ ≤ ‖J‖*‖v.value‖ := J.le_opNorm _
    _ = (‖J‖/2)*‖v‖ := by rw [norm_eq_twice]; ring

theorem nonlinearAssemblyCLM_opNorm_le
    (J : LocalHolderSpace ℝ P T γ →L[ℝ] HolderSpace P T γ) :
    ‖nonlinearAssemblyCLM P T γ J‖≤‖J‖/2 :=
  (nonlinearAssemblyCLM P T γ J).opNorm_le_bound (by positivity)
    (nonlinearAssemblyCLM_norm_le P T γ J)

def globalNonlinearMap (J : LocalHolderSpace ℝ P T γ →L[ℝ] HolderSpace P T γ)
    (u : SchauderSpace P T γ hT) : HolderSpace P T γ :=
  nonlinearAssemblyCLM P T γ J (localNonlinearMap P T γ hT hTime hγ hγ1 hr u)

theorem globalNonlinearMap_contDiffAt
    (J : LocalHolderSpace ℝ P T γ →L[ℝ] HolderSpace P T γ)
    {u : SchauderSpace P T γ hT}
    (hu : ‖normalizedMetricPerturbation P T γ hT hTime hγ hγ1 hr u‖<1) :
    ContDiffAt ℝ ∞ (globalNonlinearMap P T γ hT hTime hγ hγ1 hr J) u :=
  (nonlinearAssemblyCLM P T γ J).contDiff.contDiffAt.comp u
    (localNonlinearMap_contDiffAt P T γ hT hTime hγ hγ1 hr hu)

theorem globalNonlinearMap_sub_norm_le
    (J : LocalHolderSpace ℝ P T γ →L[ℝ] HolderSpace P T γ)
    {r : ℝ} (hr0 : 0≤r) (hr4 : r≤1/4)
    {u v : SchauderSpace P T γ hT}
    (hu : ‖normalizedMetricPerturbation P T γ hT hTime hγ hγ1 hr u‖≤r)
    (hv : ‖normalizedMetricPerturbation P T γ hT hTime hγ hγ1 hr v‖≤r) :
    ‖globalNonlinearMap P T γ hT hTime hγ hγ1 hr J u-
      globalNonlinearMap P T γ hT hTime hγ hγ1 hr J v‖≤
      (4*‖J‖*‖matrixRealTraceCLM n‖*r*normalizedPotentialBudget P.charts γ)*‖u-v‖ := by
  change ‖nonlinearAssemblyCLM P T γ J _-nonlinearAssemblyCLM P T γ J _‖≤_
  rw [← (nonlinearAssemblyCLM P T γ J).map_sub]
  exact (nonlinearAssemblyCLM_norm_le P T γ J _).trans
    ((mul_le_mul_of_nonneg_left
      (localNonlinearMap_sub_norm_le P T γ hT hTime hγ hγ1 hr hr0 hr4 hu hv)
      (by positivity : 0≤‖J‖/2)).trans_eq (by ring))

theorem globalNonlinearMap_zero_norm_le
    (J : LocalHolderSpace ℝ P T γ →L[ℝ] HolderSpace P T γ)
    (hF : ‖timeRicciBanach P hT hTime hγ hγ1 hr‖≤1/4) :
    ‖globalNonlinearMap P T γ hT hTime hγ hγ1 hr J 0‖≤
      (3*‖J‖*‖matrixRealTraceCLM n‖*normalizedRicciBudget P.charts γ)*T^(1-γ/2) := by
  calc
    _ ≤ (‖J‖/2)*‖localNonlinearMap P T γ hT hTime hγ hγ1 hr 0‖ :=
      nonlinearAssemblyCLM_norm_le P T γ J _
    _ ≤ (‖J‖/2)*(3*‖matrixRealTraceCLM n‖*‖timeRicciBanach P hT hTime hγ hγ1 hr‖) :=
      mul_le_mul_of_nonneg_left
        (localNonlinearMap_zero_norm_le P T γ hT hTime hγ hγ1 hr hF) (by positivity)
    _ = ((‖J‖/2)*(3*‖matrixRealTraceCLM n‖))*‖timeRicciBanach P hT hTime hγ hγ1 hr‖ := by ring
    _ ≤ ((‖J‖/2)*(3*‖matrixRealTraceCLM n‖))*
        ((2*normalizedRicciBudget P.charts γ)*T^(1-γ/2)) :=
      mul_le_mul_of_nonneg_left (timeRicciBanach_norm_le P hT hTime hγ hγ1 hr) (by positivity)
    _ = _ := by ring

theorem globalNonlinearMap_value_of_compatible
    (J : LocalHolderSpace ℝ P T γ →L[ℝ] HolderSpace P T γ)
    (hJ : ∀ v, holderFun (J v)=scalarAssemblyFunction P v)
    (u : SchauderSpace P T γ hT) (F : Cylinder M T → ℝ)
    (hF : ∀ (p : P.centers) (zt : ChartCylinder P T),
      localNonlinearMap P T γ hT hTime hγ hγ1 hr u ⟨p,zt⟩=F (chartPoint P T p zt)) :
    holderFun (globalNonlinearMap P T γ hT hTime hγ hγ1 hr J u)=F ∧ Continuous F := by
  have he : holderFun (globalNonlinearMap P T γ hT hTime hγ hγ1 hr J u)=F :=
    (hJ _).trans (scalarAssemblyFunction_of_compatible P _ F hF)
  refine ⟨he,?_⟩
  rw [← he]
  exact (globalNonlinearMap P T γ hT hTime hγ hγ1 hr J u).val.1.continuous

end Yau.LeafProofs.L17Aux
