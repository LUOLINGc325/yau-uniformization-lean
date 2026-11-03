import Yau.Blueprint.Nodes

/-! Patch locally constructed limits of the one original approximation
sequence. Equality on overlaps follows from uniqueness of actual limits. -/

open scoped Topology
open Filter

noncomputable section
namespace Yau.NodeProofs.U02Proof

open Yau

theorem patch_local_uniform_limits {n : ℕ} {T : Type*} [TopologicalSpace T]
    (seq : ℕ → T → ComplexVector n)
    (hlocal : ∀ x : T, ∃ V ∈ 𝓝 x, ∃ g : T → ComplexVector n,
      TendstoUniformlyOn seq g atTop V) :
    ∃ psi : T → ComplexVector n,
      (∀ x, Tendsto (fun k => seq k x) atTop (𝓝 (psi x))) ∧
      TendstoLocallyUniformly seq psi atTop ∧
      ∀ K : Set T, IsCompact K → TendstoUniformlyOn seq psi atTop K := by
  let psi : T → ComplexVector n := fun x => limUnder atTop (fun k => seq k x)
  have hlocal' : ∀ x : T, ∃ V ∈ 𝓝 x, TendstoUniformlyOn seq psi atTop V := by
    intro x
    obtain ⟨V, hV, g, hg⟩ := hlocal x
    refine ⟨V, hV, hg.congr_right ?_⟩
    intro y hy
    exact (hg.tendsto_at hy).limUnder_eq.symm
  have hlu := tendstoLocallyUniformly_of_forall_exists_nhds hlocal'
  refine ⟨psi, ?_, hlu, ?_⟩
  · intro x
    obtain ⟨V, hV, hlim⟩ := hlocal' x
    exact hlim.tendsto_at (mem_of_mem_nhds hV)
  · intro K hK
    exact (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hK).mp
      ((tendstoLocallyUniformlyOn_univ.mpr hlu).mono (Set.subset_univ K))

end Yau.NodeProofs.U02Proof
