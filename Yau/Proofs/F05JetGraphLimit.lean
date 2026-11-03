import Yau.Proofs.F05VectorHolderGraphLimit
import Yau.Proofs.F05ActualLocalFTC

/-! Uniform convergence of the four genuine jets and common original
Hölder control gives a limit in the closed native FTC graph at half the
exponent. The limiting differentiability constraints are preserved. -/

open Set Filter
open scoped Topology
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ}

theorem F05_bcf_cauchy_of_uniform {Z V : Type*} [TopologicalSpace Z]
    [NormedAddCommGroup V] {Q : Set Z} (u : ℕ → BoundedContinuousFunction Q V)
    (hCauchy : UniformCauchySeqOn (fun k => F05BCFFun (u k)) atTop Q) : CauchySeq u := by
  apply Metric.cauchySeq_iff.mpr
  intro ε hε
  obtain ⟨N,hN⟩ := Metric.uniformCauchySeqOn_iff.mp hCauchy (ε/2) (by positivity)
  refine ⟨N,?_⟩
  intro m hm k hk
  have hNorm : ‖u m-u k‖ ≤ ε/2 := by
    apply (BoundedContinuousFunction.norm_le (by positivity : 0 ≤ ε/2)).mpr
    intro p
    have h := hN m hm k hk p.val p.property
    rw [F05BCFFun_apply (u m) p,F05BCFFun_apply (u k) p,dist_eq_norm] at h
    exact h.le
  rw [dist_eq_norm]
  exact hNorm.trans_lt (by linarith)

theorem F05_jet_component_half_cauchy {α C : ℝ} {Q : Set (Point n)}
    (u : ℕ → F05JetComponent (α/2) Q)
    (hHBound : ∀ k, HolderBound α Q (vectorHolderFun (u k).2.2.1) C)
    (hTBound : ∀ k, HolderBound α Q (holderGraphFun (u k).2.2.2) C)
    (hValue : UniformCauchySeqOn (fun k => F05BCFFun (u k).1) atTop Q)
    (hGrad : UniformCauchySeqOn (fun k => F05BCFFun (u k).2.1) atTop Q)
    (hHess : UniformCauchySeqOn (fun k => vectorHolderFun (u k).2.2.1) atTop Q)
    (hTime : UniformCauchySeqOn (fun k => holderGraphFun (u k).2.2.2) atTop Q) : CauchySeq u := by
  have hV := F05_bcf_cauchy_of_uniform (fun k => (u k).1) hValue
  have hG := F05_bcf_cauchy_of_uniform (fun k => (u k).2.1) hGrad
  have hH := F05_vector_holder_graph_half_cauchy (fun k => (u k).2.2.1) hHBound hHess
  have hT := F05_holder_graph_half_cauchy (fun k => (u k).2.2.2) hTBound hTime
  exact hV.prodMk (hG.prodMk (hH.prodMk hT))

theorem F05_local_ftc_half_limit {M : ComplexManifold n} (A : AtlasData M) (i : Fin A.count)
    {α C T : ℝ} (hT : 0 ≤ T) (u : ℕ → F05LocalFTCGraph A i (α/2) hT)
    (hHBound : ∀ k, HolderBound α (F05Q A i T) (vectorHolderFun (u k).val.2.2.1) C)
    (hTBound : ∀ k, HolderBound α (F05Q A i T) (holderGraphFun (u k).val.2.2.2) C)
    (hValue : UniformCauchySeqOn (fun k => F05BCFFun (u k).val.1) atTop (F05Q A i T))
    (hGrad : UniformCauchySeqOn (fun k => F05BCFFun (u k).val.2.1) atTop (F05Q A i T))
    (hHess : UniformCauchySeqOn (fun k => vectorHolderFun (u k).val.2.2.1) atTop (F05Q A i T))
    (hTime : UniformCauchySeqOn (fun k => holderGraphFun (u k).val.2.2.2) atTop (F05Q A i T)) :
    ∃ uLim : F05LocalFTCGraph A i (α/2) hT, Tendsto u atTop (𝓝 uLim) := by
  obtain ⟨vLim,hv⟩ := cauchySeq_tendsto_of_complete
    (F05_jet_component_half_cauchy (fun k => (u k).val) hHBound hTBound hValue hGrad hHess hTime)
  have hMem : vLim ∈ F05LocalFTCGraph A i (α/2) hT :=
    (F05LocalFTCGraph_isClosed A i (α/2) hT).mem_of_tendsto hv (Eventually.of_forall (fun k => (u k).property))
  exact ⟨⟨vLim,hMem⟩,tendsto_subtype_rng.mpr hv⟩

end Yau.Proofs.F05Aux
