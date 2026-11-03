import Yau.Proofs.F04CompactDifferentialProfiles
import Yau.Proofs.F04EnergyGraphTopology
import Yau.Proofs.F04EnergyCoreTests

open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold InnerProductSpace

noncomputable section

namespace Yau.F04Proof

open Yau.Blueprint Yau.Proofs.F03Aux Yau.HeatConcreteBindings Yau.LeafProofs.L03

variable {n : ℕ} {M : ComplexManifold n}

def supportedProfileCore (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) {S : ℝ} (hS : 0 < S)
    (v : M.Carrier → ℝ → ℝ) (hv : SmoothSpaceTime v (Icc 0 S))
    (hc : ∀ t ∈ Icc 0 S, HasCompactSupport (v · t))
    (hSupp : ∀ t ∈ Icc 0 S, tsupport (v · t) ⊆ O) (t : ℝ) : dirichletCore g μ hμ O :=
  ⟨⟨(fun x => v x (timeClamp S hS.le t)),
    (fun c => (hv c).comp (contDiffOn_id.prodMk contDiffOn_const)
      (fun _ hz => ⟨hz, timeClamp_mem S hS.le t⟩)), hc _ (timeClamp_mem S hS.le t)⟩,
    hSupp _ (timeClamp_mem S hS.le t)⟩

theorem supportedProfileCore_L2 (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) {S : ℝ} (hS : 0 < S)
    (v : M.Carrier → ℝ → ℝ) (hv : SmoothSpaceTime v (Icc 0 S))
    (hc : ∀ t ∈ Icc 0 S, HasCompactSupport (v · t))
    (hSupp : ∀ t ∈ Icc 0 S, tsupport (v · t) ⊆ O)
    (hf : ∀ t, MemLp (fun x => v x (timeClamp S hS.le t)) 2 (μ.restrict O)) (t : ℝ) :
    dirichletL2 g μ hμ O
      (dirichletCoreToEnergy g μ hμ O (supportedProfileCore g μ hμ O hS v hv hc hSupp t)) =
      (hf t).toLp (fun x => v x (timeClamp S hS.le t)) := by
  rw [dirichletL2_core_eq_scalarToLp g μ hμ O _ ((scalarL2_iff_memLp _ _).mpr (hf t))]
  rfl

/-- Joint smooth supported scalar profiles are continuous in the actual
 supported d-graph norm, using both genuine scalar and differential classes. -/
theorem continuous_supportedProfileCore
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (O K : Set M.Carrier) (hO : MeasurableSet O) (hK : IsCompact K) (hOK : O ⊆ K)
    {S : ℝ} (hS : 0 < S) (v : M.Carrier → ℝ → ℝ) (hv : SmoothSpaceTime v (Icc 0 S))
    (hc : ∀ t ∈ Icc 0 S, HasCompactSupport (v · t))
    (hSupp : ∀ t ∈ Icc 0 S, tsupport (v · t) ⊆ O) :
    Continuous (fun t => dirichletCoreToEnergy g μ hμ O
      (supportedProfileCore g μ hμ O hS v hv hc hSupp t)) := by
  let F := fun t => dirichletCoreToEnergy g μ hμ O (supportedProfileCore g μ hμ O hS v hv hc hSupp t)
  obtain ⟨hf, hfc⟩ := compact_scalar_profile_L2 g μ hμ O K hO hK hOK hS.le v
    (smoothSpaceTime_continuousOn hv)
  obtain ⟨hD, hDc⟩ := compact_scalar_differential_profile_L2 g μ hμ O K hO hK hOK hS v hv
  have hJ : Continuous (fun t => dirichletL2 g μ hμ O (F t)) := by
    apply hfc.congr
    intro t
    exact (supportedProfileCore_L2 g μ hμ O hS v hv hc hSupp hf t).symm
  have hDEq (t : ℝ) : dirichletD g μ hμ O (F t) =
      realizeL2Form g (μ.restrict O)
        (L2FormSpace.ofSection (scalarExterior (fun x => v x (timeClamp S hS.le t))) (hD t)) := by
    rw [dirichletD_core]
    rfl
  have hDC : Continuous (fun t => dirichletD g μ hμ O (F t)) := hDc.congr (fun t => (hDEq t).symm)
  apply continuous_iff_continuousAt.mpr
  intro t
  exact dirichlet_tendsto_of_graph_tendsto g μ hμ O F (F t) (hJ.tendsto t) (hDC.tendsto t)

end Yau.F04Proof
