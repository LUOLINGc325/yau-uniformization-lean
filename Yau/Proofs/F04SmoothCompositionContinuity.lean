import Yau.Proofs.F04SmoothCompositionGraph

open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold InnerProductSpace

noncomputable section

namespace Yau.F04Proof

open Yau.Proofs.F03Aux Yau.LeafProofs.L03

variable {n : ℕ} {M : ComplexManifold n}

theorem continuous_dirichletSmoothComp (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier)
    (β : ℝ → ℝ) (hβ : ContDiff ℝ ∞ β) (hβ0 : β 0 = 0)
    (C : ℝ) (hC : 0 ≤ C) (hβC : ∀ s, |deriv β s| ≤ C) :
    Continuous (dirichletSmoothComp g μ hμ O β hβ hβ0 C hC hβC) := by
  apply continuous_iff_seqContinuous.mpr
  intro seq u hu
  have hJ := ((dirichletL2 g μ hμ O).continuous.tendsto u).comp hu
  have hD := ((dirichletD g μ hμ O).continuous.tendsto u).comp hu
  have hJc (v : DirichletEnergy g μ hμ O) := (dirichletSmoothComp_spec g μ hμ O β hβ hβ0 C hC hβC v).1
  have hDc (v : DirichletEnergy g μ hμ O) := (dirichletSmoothComp_spec g μ hμ O β hβ hβ0 C hC hβC v).2
  apply dirichlet_tendsto_of_graph_tendsto g μ hμ O
  · rw [hJc]
    simpa only [hJc, scalarSmoothCompL2, Function.comp_def] using
      ((smoothScalar_lipschitz β hβ C hC hβC).continuous_compLp hβ0
        |>.tendsto (dirichletL2 g μ hμ O u) |>.comp hJ)
  · rw [hDc]
    simpa only [hDc, Function.comp_def] using continuousFormMultiplier_tendsto g (μ.restrict O)
      (deriv β) (contDiff_infty_iff_deriv.mp hβ).2.continuous C hC hβC
      (fun j => dirichletL2 g μ hμ O (seq j)) (dirichletL2 g μ hμ O u)
      (by simpa only [Function.comp_def] using hJ)
      (fun j => dirichletD g μ hμ O (seq j)) (dirichletD g μ hμ O u)
      (by simpa only [Function.comp_def] using hD)

theorem dirichletSmoothComp_core (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (O : Set M.Carrier) (hO : MeasurableSet O)
    (β : ℝ → ℝ) (hβ : ContDiff ℝ ∞ β) (hβ0 : β 0 = 0)
    (C : ℝ) (hC : 0 ≤ C) (hβC : ∀ s, |deriv β s| ≤ C)
    (f : dirichletCore g μ hμ O) :
    dirichletSmoothComp g μ hμ O β hβ hβ0 C hC hβC (dirichletCoreToEnergy g μ hμ O f) =
      dirichletCoreToEnergy g μ hμ O (smoothCompositionCore g μ hμ O β hβ hβ0 f) := by
  apply dirichletL2_injective g hK μ hμ O hO
  rw [(dirichletSmoothComp_spec g μ hμ O β hβ hβ0 C hC hβC _).1,
    smoothCompositionCore_L2 g μ hμ O β hβ hβ0 C hC hβC]

end Yau.F04Proof
