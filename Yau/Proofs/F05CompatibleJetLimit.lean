import Yau.Proofs.F05JetGraphLimit
import Yau.Proofs.F05JetCompatibility

/-! Actual homogeneous traces and every nonlinear coordinate Hessian
overlap survive the genuine Banach limit of the four-jet tuple. -/

open Set Filter
open scoped Topology
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem F05_local_zero_ftc_half_limit (A : AtlasData M) (i : Fin A.count)
    {α C T : ℝ} (hT : 0 ≤ T) (u : ℕ → F05LocalZeroFTCGraph A i (α/2) hT)
    (hHBound : ∀ k, HolderBound α (F05Q A i T) (vectorHolderFun (u k).val.2.2.1) C)
    (hTBound : ∀ k, HolderBound α (F05Q A i T) (holderGraphFun (u k).val.2.2.2) C)
    (hValue : UniformCauchySeqOn (fun k => F05BCFFun (u k).val.1) atTop (F05Q A i T))
    (hGrad : UniformCauchySeqOn (fun k => F05BCFFun (u k).val.2.1) atTop (F05Q A i T))
    (hHess : UniformCauchySeqOn (fun k => vectorHolderFun (u k).val.2.2.1) atTop (F05Q A i T))
    (hTime : UniformCauchySeqOn (fun k => holderGraphFun (u k).val.2.2.2) atTop (F05Q A i T)) :
    ∃ uLim : F05LocalZeroFTCGraph A i (α/2) hT, Tendsto u atTop (𝓝 uLim) := by
  obtain ⟨vLim,hv⟩ := cauchySeq_tendsto_of_complete
    (F05_jet_component_half_cauchy (fun k => (u k).val) hHBound hTBound hValue hGrad hHess hTime)
  have hMem : vLim ∈ F05LocalZeroFTCGraph A i (α/2) hT :=
    (F05LocalZeroFTCGraph_isClosed A i (α/2) hT).mem_of_tendsto hv
      (Eventually.of_forall (fun k => (u k).property))
  exact ⟨⟨vLim,hMem⟩,tendsto_subtype_rng.mpr hv⟩

theorem F05_compatible_jet_half_limit (A : AtlasData M) {α C T : ℝ} (hT : 0 ≤ T)
    (u : ℕ → F05CompatibleJetGraph A (α/2) hT)
    (hHBound : ∀ i k, HolderBound α (F05Q A i T) (vectorHolderFun ((u k).val i).val.2.2.1) C)
    (hTBound : ∀ i k, HolderBound α (F05Q A i T) (holderGraphFun ((u k).val i).val.2.2.2) C)
    (hValue : ∀ i, UniformCauchySeqOn (fun k => F05BCFFun ((u k).val i).val.1) atTop (F05Q A i T))
    (hGrad : ∀ i, UniformCauchySeqOn (fun k => F05BCFFun ((u k).val i).val.2.1) atTop (F05Q A i T))
    (hHess : ∀ i, UniformCauchySeqOn (fun k => vectorHolderFun ((u k).val i).val.2.2.1) atTop (F05Q A i T))
    (hTime : ∀ i, UniformCauchySeqOn (fun k => holderGraphFun ((u k).val i).val.2.2.2) atTop (F05Q A i T)) :
    ∃ uLim : F05CompatibleJetGraph A (α/2) hT, Tendsto u atTop (𝓝 uLim) := by
  classical
  letI : (i : Fin A.count) → TopologicalSpace (F05LocalZeroFTCGraph A i (α/2) hT) :=
    fun i => inferInstance
  have hEach (i : Fin A.count) := F05_local_zero_ftc_half_limit A i hT
    (fun k => (u k).val i) (hHBound i) (hTBound i) (hValue i) (hGrad i) (hHess i) (hTime i)
  choose v hv using hEach
  have hAmbient : Tendsto (fun k => (u k).val) atTop (𝓝 v) := tendsto_pi_nhds.mpr hv
  have hMem : v ∈ F05CompatibleJetGraph A (α/2) hT :=
    (F05CompatibleJetGraph_isClosed A (α/2) hT).mem_of_tendsto hAmbient
      (Eventually.of_forall (fun k => (u k).property))
  exact ⟨⟨v,hMem⟩,tendsto_subtype_rng.mpr hAmbient⟩

end Yau.Proofs.F05Aux
