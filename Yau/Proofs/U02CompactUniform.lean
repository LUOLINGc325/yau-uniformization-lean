import Yau.Blueprint.Nodes

/-! A finite subcover turns local eventual estimates into the original
uniform estimate on each compact set. -/

open scoped Topology
open Filter

namespace Yau.NodeProofs.U02Proof

theorem compact_eventually_of_local {T : Type*} [TopologicalSpace T]
    {P : ℕ → T → Prop}
    (hlocal : ∀ x : T, ∃ V ∈ 𝓝 x, ∀ᶠ k in atTop, ∀ y ∈ V, P k y)
    {K : Set T} (hK : IsCompact K) : ∀ᶠ k in atTop, ∀ y ∈ K, P k y := by
  classical
  choose V hV hPV using hlocal
  obtain ⟨t, _htK, hcover⟩ := hK.elim_nhds_subcover V (fun x _ => hV x)
  have hfinite : ∀ᶠ k in atTop, ∀ x ∈ t, ∀ y ∈ V x, P k y :=
    (eventually_all_finset t).mpr (fun x _ => hPV x)
  filter_upwards [hfinite] with k hk
  intro y hy
  obtain ⟨x, hx⟩ := Set.mem_iUnion.mp (hcover hy)
  obtain ⟨hxt, hyV⟩ := Set.mem_iUnion.mp hx
  exact hk x hxt y hyV

end Yau.NodeProofs.U02Proof
