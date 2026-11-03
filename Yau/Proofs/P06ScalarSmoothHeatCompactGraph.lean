import Yau.Proofs.P06ScalarSmoothHeatGraphChain
import Yau.Proofs.P06CompactInitial

/-! The actual compact-data heat error converges to zero in every finite
original graph norm, including at the initial face. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology InnerProductSpace

namespace Yau.NodeProofs.P06Aux.ScalarSmooth
open Yau Yau.LeafProofs.L03
variable {n k : ℕ} {M : ComplexManifold n}

def compactInitialGraphChain (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (A : RealForm M k)
    (hA : SmoothRealForm A) (hcA : CompactlySupportedRealForm A) (N : ℕ) (t : ℝ) :
    hodgeGraphChains g μ hμ k N :=
  hodgeGraphChain g μ hμ N
    (fun j => hodgeHeatHilbert g μ hμ k t (compactHodgeIterateHilbert g μ hμ A hA hcA j) -
      compactHodgeIterateHilbert g μ hμ A hA hcA j)
    (fun j _ => compactHodgeHeat_initial_graph g μ hμ A hA hcA t j)

theorem compactInitialGraphChain_tendsto_zero (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (A : RealForm M k)
    (hA : SmoothRealForm A) (hcA : CompactlySupportedRealForm A) (N : ℕ) :
    Tendsto (compactInitialGraphChain g μ hμ A hA hcA N) (𝓝[≥] (0 : ℝ)) (𝓝 0) := by
  apply graphChain_tendsto
  intro j
  exact compactHodgeHeat_initial g μ hμ A hA hcA j

theorem compactInitialGraphJet_tendsto_zero {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (A : RealForm M k)
    (hA : SmoothRealForm A) (hcA : CompactlySupportedRealForm A) (N : ℕ)
    (L : hodgeGraphChains g μ hμ k N →L[ℝ] E) :
    Tendsto (fun t => L (compactInitialGraphChain g μ hμ A hA hcA N t))
      (𝓝[≥] (0 : ℝ)) (𝓝 0) := by
  simpa only [map_zero,Function.comp_def] using (L.continuous.tendsto 0).comp
    (compactInitialGraphChain_tendsto_zero g μ hμ A hA hcA N)

end Yau.NodeProofs.P06Aux.ScalarSmooth
