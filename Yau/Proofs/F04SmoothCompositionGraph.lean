import Yau.Proofs.F04SmoothCompositionCore
import Yau.Proofs.F04EnergyGraphTopology

open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold InnerProductSpace

noncomputable section

namespace Yau.F04Proof

open Yau.Proofs.F03Aux Yau.LeafProofs.L03

variable {n : ℕ} {M : ComplexManifold n}

/-- The smooth composition is constructed by closing the actual scalar and
actual exterior-derivative graph of supported smooth core approximations. -/
theorem dirichlet_smooth_comp_graph (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier)
    (β : ℝ → ℝ) (hβ : ContDiff ℝ ∞ β) (hβ0 : β 0 = 0)
    (C : ℝ) (hC : 0 ≤ C) (hβC : ∀ s, |deriv β s| ≤ C)
    (u : DirichletEnergy g μ hμ O) :
    ∃ v : DirichletEnergy g μ hμ O,
      dirichletL2 g μ hμ O v =
        scalarSmoothCompL2 (μ.restrict O) β hβ hβ0 C hC hβC (dirichletL2 g μ hμ O u) ∧
      dirichletD g μ hμ O v =
        continuousFormMultiplier g (μ.restrict O) (deriv β)
          (contDiff_infty_iff_deriv.mp hβ).2.continuous C hC hβC
          (dirichletL2 g μ hμ O u) (dirichletD g μ hμ O u) := by
  obtain ⟨fs, hfs⟩ := exists_dirichletCore_tendsto g μ hμ O u
  let vs (j : ℕ) := smoothCompositionCore g μ hμ O β hβ hβ0 (fs j)
  have hJ := ((dirichletL2 g μ hμ O).continuous.tendsto u).comp hfs
  have hD := ((dirichletD g μ hμ O).continuous.tendsto u).comp hfs
  have hJlim : Tendsto (fun j => dirichletL2 g μ hμ O (dirichletCoreToEnergy g μ hμ O (vs j)))
      atTop (𝓝 (scalarSmoothCompL2 (μ.restrict O) β hβ hβ0 C hC hβC
        (dirichletL2 g μ hμ O u))) := by
    simpa only [Function.comp_def, vs, smoothCompositionCore_L2 g μ hμ O β hβ hβ0 C hC hβC, scalarSmoothCompL2] using
      ((smoothScalar_lipschitz β hβ C hC hβC).continuous_compLp hβ0
        |>.tendsto (dirichletL2 g μ hμ O u) |>.comp hJ)
  have hDlim : Tendsto (fun j => dirichletD g μ hμ O (dirichletCoreToEnergy g μ hμ O (vs j)))
      atTop (𝓝 (continuousFormMultiplier g (μ.restrict O) (deriv β)
        (contDiff_infty_iff_deriv.mp hβ).2.continuous C hC hβC
        (dirichletL2 g μ hμ O u) (dirichletD g μ hμ O u))) := by
    simpa only [vs, smoothCompositionCore_D g μ hμ O β hβ hβ0 C hC hβC] using
      continuousFormMultiplier_tendsto g (μ.restrict O) (deriv β)
        (contDiff_infty_iff_deriv.mp hβ).2.continuous C hC hβC
        (fun j => dirichletL2 g μ hμ O (dirichletCoreToEnergy g μ hμ O (fs j)))
        (dirichletL2 g μ hμ O u) hJ
        (fun j => dirichletD g μ hμ O (dirichletCoreToEnergy g μ hμ O (fs j)))
        (dirichletD g μ hμ O u) hD
  have hm := (dirichletGraphMap_isClosed_range g μ hμ O).mem_of_tendsto
    (hJlim.prodMk_nhds hDlim) (Eventually.of_forall fun j =>
      show (dirichletL2 g μ hμ O (dirichletCoreToEnergy g μ hμ O (vs j)),
        dirichletD g μ hμ O (dirichletCoreToEnergy g μ hμ O (vs j))) ∈
        range (dirichletGraphMap g μ hμ O) from ⟨dirichletCoreToEnergy g μ hμ O (vs j), rfl⟩)
  obtain ⟨v, hv⟩ := hm
  exact ⟨v, congrArg Prod.fst hv, congrArg Prod.snd hv⟩

def dirichletSmoothComp (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier)
    (β : ℝ → ℝ) (hβ : ContDiff ℝ ∞ β) (hβ0 : β 0 = 0)
    (C : ℝ) (hC : 0 ≤ C) (hβC : ∀ s, |deriv β s| ≤ C)
    (u : DirichletEnergy g μ hμ O) : DirichletEnergy g μ hμ O :=
  Classical.choose (dirichlet_smooth_comp_graph g μ hμ O β hβ hβ0 C hC hβC u)

theorem dirichletSmoothComp_spec (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier)
    (β : ℝ → ℝ) (hβ : ContDiff ℝ ∞ β) (hβ0 : β 0 = 0)
    (C : ℝ) (hC : 0 ≤ C) (hβC : ∀ s, |deriv β s| ≤ C)
    (u : DirichletEnergy g μ hμ O) :
    dirichletL2 g μ hμ O (dirichletSmoothComp g μ hμ O β hβ hβ0 C hC hβC u) =
        scalarSmoothCompL2 (μ.restrict O) β hβ hβ0 C hC hβC (dirichletL2 g μ hμ O u) ∧
      dirichletD g μ hμ O (dirichletSmoothComp g μ hμ O β hβ hβ0 C hC hβC u) =
        continuousFormMultiplier g (μ.restrict O) (deriv β)
          (contDiff_infty_iff_deriv.mp hβ).2.continuous C hC hβC
          (dirichletL2 g μ hμ O u) (dirichletD g μ hμ O u) :=
  Classical.choose_spec (dirichlet_smooth_comp_graph g μ hμ O β hβ hβ0 C hC hβC u)

end Yau.F04Proof
