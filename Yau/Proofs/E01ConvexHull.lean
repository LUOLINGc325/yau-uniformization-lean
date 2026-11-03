import Yau.Proofs.E01ConvexPadding
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Compactness of a compact set's finite-dimensional convex hull. -/

noncomputable section
open Set

namespace Yau.NodeProofs.E01Aux

theorem isCompact_convexHull_of_finiteDimensional
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {S : Set E} (hS : IsCompact S) : IsCompact (convexHull ℝ S) := by
  classical
  by_cases hSne : S.Nonempty
  · let N := Module.finrank ℝ E + 1
    let D : Set ((Fin N → E) × (Fin N → ℝ)) :=
      (Set.univ.pi fun _ => S) ×ˢ stdSimplex ℝ (Fin N)
    let F : ((Fin N → E) × (Fin N → ℝ)) → E :=
      fun p => ∑ i, p.2 i • p.1 i
    have hD : IsCompact D :=
      (isCompact_univ_pi fun _ : Fin N => hS).prod (isCompact_stdSimplex ℝ (Fin N))
    have hF : Continuous F := by
      dsimp only [F]
      fun_prop
    have hImage : F '' D = convexHull ℝ S := by
      ext A
      constructor
      · rintro ⟨⟨η, α⟩, hmem, rfl⟩
        change (∑ i, α i • η i) ∈ convexHull ℝ S
        exact (convex_convexHull ℝ S).sum_mem
          (fun i _ => hmem.2.1 i) hmem.2.2
          (fun i _ => subset_convexHull ℝ S (hmem.1 i (Set.mem_univ i)))
      · intro hA
        obtain ⟨ι, hι, η, α, hη, hind, hα, hα1, hrep⟩ :=
          eq_pos_convex_span_of_mem_convexHull hA
        letI : Fintype ι := hι
        have hcard : Fintype.card ι ≤ N :=
          hind.card_le_finrank_succ.trans
            (Nat.add_le_add_right (Submodule.finrank_le _) 1)
        obtain ⟨η', α', h', h1', hrep'⟩ :=
          pad_convex_combination hSne η α
            (fun i => hη ⟨i, rfl⟩) (fun i => (hα i).le) hα1 hcard
        refine ⟨(η', α'), ⟨?_, ⟨?_, h1'⟩⟩, ?_⟩
        · intro i _
          exact (h' i).1
        · exact fun i => (h' i).2
        · change (∑ i, α' i • η' i) = A
          exact hrep'.trans hrep
    rw [← hImage]
    exact hD.image hF
  · have hSe : S = ∅ := Set.not_nonempty_iff_eq_empty.mp hSne
    rw [hSe, convexHull_empty]
    exact isCompact_empty

end Yau.NodeProofs.E01Aux
