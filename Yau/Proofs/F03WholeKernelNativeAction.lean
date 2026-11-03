import Yau.Proofs.F03DirichletKernelEvolution
import Yau.Proofs.F03DirichletClassicalPairing
import Yau.Proofs.F03UnivHeatEquality

/-! The actual whole-domain kernel represents the same native L² heat operator. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace Yau.Proofs.F03Aux
open Yau HeatConcreteBindings HeatTargetCandidates LeafProofs.L19Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1400000

theorem dirichletWholeKernelCandidate_native_heat_ae
    (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (f : Lp ℝ 2 μ) {t : ℝ} (ht : 0 < t) :
    (fun x => ∫ y,dirichletKernelCandidate g hK μ hμ univ isOpen_univ t x y*f y ∂μ) =ᵐ[μ]
      (scalarHeatFamily g μ hμ t f : M.Carrier → ℝ) := by
  have hf : ScalarL2 (μ.restrict univ) (f : M.Carrier → ℝ) :=
    (scalarL2_iff_memLp _ _).mpr ((Lp.memLp f).restrict univ)
  have hSource : scalarToLp hf=l2Restriction μ univ f := by
    apply Lp.ext
    filter_upwards [scalarToLp_coe hf,restrictL2_coe μ univ f] with y hy hz
    exact hy.trans hz.symm
  have hEq := dirichletKernelCandidate_evolution_eq g hK μ hμ univ isOpen_univ ht f hf
  rw [hSource] at hEq
  have hAE := dirichletClassicalHeat_ambient_ae g hK μ hμ univ isOpen_univ (l2Restriction μ univ f) ht
  rw [dirichletHeat_univ g μ hμ t ht f] at hAE
  filter_upwards [hAE] with x hx
  have hEx := congrFun hEq x
  simp only [boundedKernelEvolution,if_neg ht.ne'] at hEx
  exact hEx.trans hx

end Yau.Proofs.F03Aux
