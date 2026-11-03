import Yau.Proofs.F05Partition

/-! Local smooth representatives of a profile glue to one genuine global
smooth function. Equality on the closed physical set is preserved exactly. -/

open Set
open scoped Topology ContDiff Manifold
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic
variable {n : ℕ} {M : ComplexManifold n}

theorem F05_smooth_profile_extension_of_local {C : Set M.Carrier} (hC : IsClosed C)
    (f : M.Carrier → ℝ)
    (hLocal : ∀ x ∈ C, ∃ (V : Set M.Carrier) (g : M.Carrier → ℝ),
      IsOpen V ∧ x ∈ V ∧ ContMDiffOn 𝓘(ℝ,Space n) 𝓘(ℝ,ℝ) ∞ g V ∧ EqOn g f (C∩V)) :
    ∃ g : M.Carrier → ℝ, SmoothFn g ∧ EqOn g f C := by
  classical
  letI := Yau.LeafProofs.L12Aux.manifold_realSmooth M
  letI : LocallyCompactSpace M.Carrier := Yau.LeafProofs.L12Aux.manifold_locallyCompact M
  let t : M.Carrier → Set ℝ := fun x => if x ∈ C then {f x} else univ
  have ht (x : M.Carrier) : Convex ℝ (t x) := by
    dsimp only [t]
    split_ifs
    · exact convex_singleton _
    · exact convex_univ
  obtain ⟨g,hg⟩ := exists_contMDiffMap_forall_mem_convex_of_local
    (I := 𝓘(ℝ,Space n)) ht (by
      intro x
      by_cases hx : x ∈ C
      · obtain ⟨V,g,hV,hxV,hSmooth,hEq⟩ := hLocal x hx
        refine ⟨V,hV.mem_nhds hxV,g,hSmooth,?_⟩
        intro y hy
        by_cases hyC : y ∈ C
        · simpa only [t,if_pos hyC,mem_singleton_iff] using hEq ⟨hyC,hy⟩
        · simp only [t,if_neg hyC,mem_univ]
      · refine ⟨Cᶜ,hC.isOpen_compl.mem_nhds hx,fun _ => 0,contMDiffOn_const,?_⟩
        intro y hy
        simp only [t,if_neg hy,mem_univ])
  refine ⟨g,Yau.LeafProofs.L18Aux.smoothFn_of_contMDiff_real g.contMDiff,?_⟩
  intro x hx
  simpa only [t,if_pos hx,mem_singleton_iff] using hg x

end Yau.Proofs.F05Aux
