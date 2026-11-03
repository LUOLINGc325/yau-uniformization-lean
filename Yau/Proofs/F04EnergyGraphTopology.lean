import Yau.Proofs.F03DirichletClosedGraph

open MeasureTheory Filter Set
open scoped Topology InnerProductSpace

noncomputable section

namespace Yau.F04Proof

open Yau.Proofs.F03Aux

variable {n : ℕ} {M : ComplexManifold n}

/-- Convergence of the genuine scalar and exterior-derivative components is
strong convergence in the original supported energy norm. -/
theorem dirichlet_tendsto_of_graph_tendsto
    (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier)
    {ι : Type*} {l : Filter ι} (u : ι → DirichletEnergy g μ hμ O)
    (v : DirichletEnergy g μ hμ O)
    (hJ : Tendsto (fun j => dirichletL2 g μ hμ O (u j)) l (𝓝 (dirichletL2 g μ hμ O v)))
    (hD : Tendsto (fun j => dirichletD g μ hμ O (u j)) l (𝓝 (dirichletD g μ hμ O v))) :
    Tendsto u l (𝓝 v) := by
  have hg : Tendsto (fun j => dirichletGraphMap g μ hμ O (u j)) l
      (𝓝 (dirichletGraphMap g μ hμ O v)) := hJ.prodMk_nhds hD
  have he : Tendsto (fun j => dirichletGraphMap g μ hμ O (u j - v)) l (𝓝 0) := by
    simpa only [map_sub, sub_self] using hg.sub (tendsto_const_nhds : Tendsto (fun _ : ι => dirichletGraphMap g μ hμ O v)
      l (𝓝 (dirichletGraphMap g μ hμ O v)))
  have hu : Tendsto (fun j => u j - v) l (𝓝 0) := by
    apply squeeze_zero_norm (fun j => dirichletGraphMap_bound g μ hμ O (u j - v))
    simpa only [norm_zero, mul_zero] using he.norm.const_mul 2
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [norm_zero] using hu.norm

end Yau.F04Proof
