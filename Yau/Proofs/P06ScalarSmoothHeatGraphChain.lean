import Yau.Proofs.P06HodgeRegularityHilbertJets
import Mathlib.Topology.Algebra.Module.ClosedSubmodule

/-! Finite chains in the original closed operator graph form a genuine
Banach space with the inherited finite product norm. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff InnerProductSpace

namespace Yau.NodeProofs.P06Aux.ScalarSmooth

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

def graphChains (G : Submodule ℝ (H × H)) (hG : IsClosed (G : Set (H × H))) (N : ℕ) :
    ClosedSubmodule ℝ (Fin (N+1) → H) where
  carrier := {u | ∀ j : Fin N, (u j.castSucc,u j.succ) ∈ G}
  zero_mem' := fun _ => G.zero_mem
  add_mem' := by
    intro u v hu hv j
    exact G.add_mem (hu j) (hv j)
  smul_mem' := by
    intro c u hu j
    exact G.smul_mem c (hu j)
  isClosed' := by
    have hh : IsClosed (⋂ j : Fin N, {u : Fin (N+1) → H | (u j.castSucc,u j.succ) ∈ G}) :=
      isClosed_iInter (fun j => hG.preimage ((continuous_apply j.castSucc).prodMk
        (continuous_apply j.succ)))
    convert hh using 1
    ext u
    simp

def graphChainEval (G : Submodule ℝ (H × H)) (hG : IsClosed (G : Set (H × H)))
    (N : ℕ) (j : Fin (N+1)) : graphChains G hG N →L[ℝ] H :=
  (ContinuousLinearMap.proj j).comp (graphChains G hG N).toSubmodule.subtypeL

@[simp] theorem graphChainEval_apply (G : Submodule ℝ (H × H))
    (hG : IsClosed (G : Set (H × H))) (N : ℕ) (j : Fin (N+1))
    (u : graphChains G hG N) : graphChainEval G hG N j u = u.val j := rfl

theorem graphChain_tendsto {ι : Type*} {l : Filter ι}
    (G : Submodule ℝ (H × H)) (hG : IsClosed (G : Set (H × H))) (N : ℕ)
    (u : ι → graphChains G hG N) (v : graphChains G hG N)
    (hu : ∀ j, Tendsto (fun i => (u i).val j) l (𝓝 (v.val j))) :
    Tendsto u l (𝓝 v) := by
  exact tendsto_subtype_rng.mpr (tendsto_pi_nhds.mpr hu)

open Yau Yau.LeafProofs.L03
variable {n k : ℕ} {M : ComplexManifold n}

abbrev hodgeGraphChains (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (k N : ℕ) :=
  graphChains (hodgeCoreOperator g μ hμ k).closure.graph
    (hodgeCoreOperator_closable g μ hμ k).closure_isClosed N

def hodgeGraphChain (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (N : ℕ)
    (u : ℕ → L2FormHilbert g μ k)
    (hu : ∀ j < N, (u j,u (j+1)) ∈ (hodgeCoreOperator g μ hμ k).closure.graph) :
    hodgeGraphChains g μ hμ k N :=
  ⟨fun j => u j,fun j => hu j j.isLt⟩

@[simp] theorem hodgeGraphChain_apply (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (N : ℕ)
    (u : ℕ → L2FormHilbert g μ k)
    (hu : ∀ j < N, (u j,u (j+1)) ∈ (hodgeCoreOperator g μ hμ k).closure.graph)
    (j : Fin (N+1)) : (hodgeGraphChain g μ hμ N u hu).val j = u j := rfl

def hodgeGraphChainExtend (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (N : ℕ)
    (u : hodgeGraphChains g μ hμ k N) (j : ℕ) : L2FormHilbert g μ k :=
  if hj : j ≤ N then u.val ⟨j,by omega⟩ else 0

theorem hodgeGraphChainExtend_edge (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (N : ℕ)
    (u : hodgeGraphChains g μ hμ k N) (j : ℕ) (hj : j < N) :
    (hodgeGraphChainExtend g μ hμ N u j,hodgeGraphChainExtend g μ hμ N u (j+1)) ∈
      (hodgeCoreOperator g μ hμ k).closure.graph := by
  have he := u.property ⟨j,hj⟩
  change (u.val ⟨j,by omega⟩,u.val ⟨j+1,by omega⟩) ∈ _ at he
  simpa only [hodgeGraphChainExtend,dite_eq_left (show j ≤ N by omega),
    dite_eq_left (show j+1 ≤ N by omega)] using he

end Yau.NodeProofs.P06Aux.ScalarSmooth
