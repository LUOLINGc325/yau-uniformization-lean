import Yau.Proofs.F03MinimalKernelJointSmooth
import Yau.Proofs.F03KernelSmoothTransport
import Yau.Proofs.F03OrderedKernelUniqueness
import Yau.Proofs.F03MinimalKernelRows
import Yau.Proofs.F03WholeKernelNativeAction

/-! Native heat equality and one positive L² row identify the same original ciSup pointwise. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff
namespace Yau.Proofs.F03Aux
open Yau HeatConcreteBindings LeafProofs.L12Aux LeafProofs.L19Aux LeafProofs.L18Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000

theorem dirichletMinimalKernelCandidate_eq_whole
    (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (O : ℕ → Set M.Carrier) (hO : SmoothExhaustion O) {t : ℝ} (ht : 0 < t)
    (x y : M.Carrier) :
    dirichletMinimalKernelCandidate g hK μ hμ O hO t x y=
      dirichletKernelCandidate g hK μ hμ univ isOpen_univ t x y := by
  let H := dirichletMinimalKernelCandidate g hK μ hμ O hO
  let K := dirichletKernelCandidate g hK μ hμ univ isOpen_univ
  have hHS : KernelSmoothOn univ H := dirichletMinimalKernelCandidate_joint_smooth g hK μ hμ O hO
  have hKS : KernelSmoothOn univ K := dirichletKernelCandidate_smooth g hK μ hμ univ isOpen_univ
  have hRow := dirichletMinimalKernelCandidate_row_scalarL2 g hK μ hμ O hO zero_lt_one x
  let f := scalarToLp hRow
  have hf : ScalarL2 μ (f : M.Carrier → ℝ) := (scalarL2_iff_memLp _ _).mpr (Lp.memLp f)
  have hfU : ScalarL2 (μ.restrict univ) (f : M.Carrier → ℝ) :=
    (scalarL2_iff_memLp _ _).mpr ((Lp.memLp f).restrict univ)
  have hPos : ∀ᵐ z ∂μ,0 < f z := by
    filter_upwards [scalarToLp_coe hRow] with z hz
    rw [hz]
    exact dirichletMinimalKernelCandidate_strict_pos g hK μ hμ O hO zero_lt_one x z
  have hAction : (fun p => ∫ z,H t p z*f z ∂μ) =ᵐ[μ] (fun p => ∫ z,K t p z*f z ∂μ) :=
    (dirichletMinimalKernelCandidate_native_heat_ae g hK μ hμ O hO f ht).trans
      (dirichletWholeKernelCandidate_native_heat_ae g hK μ hμ f ht).symm
  letI : μ.IsOpenPosMeasure := riemannianVolume_isOpenPosMeasure g μ hμ
  have hEq : H t=K t := ordered_kernels_eq_of_positive_action μ (H t) (K t) f
    (fun p z => dirichletMinimalKernelCandidate_le_univ g hK μ hμ O hO ht p z)
    (fun z => kernelSmooth_univ_continuous_left H hHS ht z)
    (fun z => kernelSmooth_univ_continuous_left K hKS ht z)
    (fun p => kernelSmooth_univ_continuous_right H hHS ht p)
    (fun p => kernelSmooth_univ_continuous_right K hKS ht p) hPos
    (fun p => dirichletMinimalKernelCandidate_l2_source_integrable g hK μ hμ O hO f hf ht p)
    (fun p => dirichletKernelCandidate_source_integrable g hK μ hμ univ isOpen_univ ht p (mem_univ p) f hfU)
    hAction
  exact congrFun (congrFun hEq x) y

end Yau.Proofs.F03Aux
