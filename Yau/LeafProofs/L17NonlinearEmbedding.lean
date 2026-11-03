import Yau.LeafProofs.L17NonlinearPointValues
import Yau.LeafProofs.L17ScalarInverseCompatibility

open Set Metric
open scoped Matrix ComplexOrder ContDiff Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17NonlinearEmbeddingAux
open L17Aux L17HolderAux L17SchauderAux
local instance nonlinearEmbeddingTopology (n : ℕ) : TopologicalSpace (Matrix (Fin n) (Fin n) ℂ) := leviMatrixTopology n
variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}
variable {P : UniformChartPartition g} {T α β : ℝ} {hT : 0<T}

theorem potentialMetricMatrix_eq_of_function_eq
    {u : SchauderSpace P T α hT} {v : SchauderSpace P T β hT}
    (huv : schauderFun u=schauderFun v) : potentialMetricMatrix u=potentialMetricMatrix v := by
  funext q
  have ht : (fun y => schauderFun u (y,q.2))=fun y => schauderFun v (y,q.2) :=
    funext fun y => congrFun huv (y,q.2)
  simp only [potentialMetricMatrix,ht]

theorem potentialNonlinearFunction_eq_of_function_eq
    {u : SchauderSpace P T α hT} {v : SchauderSpace P T β hT}
    (huv : schauderFun u=schauderFun v) : potentialNonlinearFunction u=potentialNonlinearFunction v := by
  funext q
  have ht : (fun y => schauderFun u (y,q.2))=fun y => schauderFun v (y,q.2) :=
    funext fun y => congrFun huv (y,q.2)
  rw [potentialNonlinearFunction,potentialNonlinearFunction,
    potentialMetricMatrix_eq_of_function_eq huv]
  change _-laplacian g (fun y => schauderFun u (y,q.2)) q.1=
    _-laplacian g (fun y => schauderFun v (y,q.2)) q.1
  rw [ht]

theorem globalNonlinearMap_weaken (hg : MetricSmooth g) (hTime : T≤P.radius^2)
    (hα : 0≤α) (hα1 : α≤1) (hβ : 0≤β) (hβα : β≤α) (hr : P.radius≤1)
    (Ja : LocalHolderSpace ℝ P T α →L[ℝ] HolderSpace P T α)
    (Jb : LocalHolderSpace ℝ P T β →L[ℝ] HolderSpace P T β)
    (hJa : ∀ w,holderFun (Ja w)=L17LocalScalarAssemblyAux.scalarAssemblyFunction P w)
    (hJb : ∀ w,holderFun (Jb w)=L17LocalScalarAssemblyAux.scalarAssemblyFunction P w)
    (u : SchauderSpace P T α hT)
    (hZa : ‖normalizedMetricPerturbation P T α hT hTime hα hα1 hr u‖<1)
    (hZb : ‖normalizedMetricPerturbation P T β hT hTime hβ (hβα.trans hα1) hr
      (schauderWeakenCLM P hT hTime hβα u)‖<1)
    (hSa : ‖u‖+T*backgroundLogDetHessianBudget P.charts≤(P.charts.bound 0)⁻¹)
    (hSb : ‖schauderWeakenCLM P hT hTime hβα u‖+T*backgroundLogDetHessianBudget P.charts≤(P.charts.bound 0)⁻¹) :
    weakenCLM P hTime hβα (globalNonlinearMap P T α hT hTime hα hα1 hr Ja u)=
      globalNonlinearMap P T β hT hTime hβ (hβα.trans hα1) hr Jb
        (schauderWeakenCLM P hT hTime hβα u) := by
  apply holderFun_injective P T β
  rw [weakenCLM_value,
    (globalNonlinearMap_value P T α hT hTime hα hα1 hr hg Ja hJa u hZa hSa).1,
    (globalNonlinearMap_value P T β hT hTime hβ (hβα.trans hα1) hr hg Jb hJb
      (schauderWeakenCLM P hT hTime hβα u) hZb hSb).1]
  exact potentialNonlinearFunction_eq_of_function_eq
    (schauderWeakenCLM_function P hT hTime hβα u).symm

end Yau.LeafProofs.L17NonlinearEmbeddingAux
