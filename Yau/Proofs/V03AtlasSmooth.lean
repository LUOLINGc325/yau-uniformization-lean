import Yau.Proofs.V03Atlas

/-! The constructed induced cotangent atlas is a complex smooth manifold. -/

open scoped Manifold Topology ContDiff Matrix ComplexOrder

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

variable {n : ℕ}

instance nativeCotangentIsManifold (M : ComplexManifold n) :
    IsManifold 𝓘(ℂ, CotangentCoord n) ∞ (NativeCotangentPoint M) := by
  apply isManifold_of_contDiffOn 𝓘(ℂ, CotangentCoord n) ∞ (NativeCotangentPoint M)
  intro e e' he he'
  change e ∈ ⋃ (p : PartialEquiv (NativeCotangentPoint M) (CotangentCoord n))
    (hp : p ∈ (nativeCotangentCore M).atlas),
      {(nativeCotangentCore M).openPartialHomeomorph p hp} at he
  change e' ∈ ⋃ (p : PartialEquiv (NativeCotangentPoint M) (CotangentCoord n))
    (hp : p ∈ (nativeCotangentCore M).atlas),
      {(nativeCotangentCore M).openPartialHomeomorph p hp} at he'
  simp only [Set.mem_iUnion, Set.mem_singleton_iff] at he he'
  obtain ⟨p, hp, rfl⟩ := he
  obtain ⟨p', hp', rfl⟩ := he'
  obtain ⟨x, rfl⟩ := hp
  obtain ⟨x', rfl⟩ := hp'
  simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    Function.id_comp, Function.comp_id, Set.preimage_id, Set.range_id, Set.inter_univ]
  change ContDiffOn ℂ ∞ (fun z => cotangentChart x' (cotangentChartInv x z))
    {z : CotangentCoord n | z ∈ cotangentTarget x ∧
      chartInv x z.1 ∈ (extChartAt (ComplexModel n) x').source}
  intro z hz
  exact (cotangentChartTransition_contDiffAt x x' hz.1 hz.2).contDiffWithinAt

end Yau.Blueprint.V03Proof
