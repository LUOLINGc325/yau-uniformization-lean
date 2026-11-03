import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.StdSimplex

/-! Padding an actual finite convex combination to a fixed number of slots. -/

noncomputable section

namespace Yau.NodeProofs.E01Aux

theorem pad_convex_combination
    {E ι : Type*} [AddCommMonoid E] [Module ℝ E] [Fintype ι]
    {S : Set E} (hS : S.Nonempty) (η : ι → E) (α : ι → ℝ)
    (hη : ∀ i, η i ∈ S) (hα : ∀ i, 0 ≤ α i) (hα1 : ∑ i, α i = 1)
    {N : ℕ} (hN : Fintype.card ι ≤ N) :
    ∃ (η' : Fin N → E) (α' : Fin N → ℝ),
      (∀ j, η' j ∈ S ∧ 0 ≤ α' j) ∧
      ∑ j, α' j = 1 ∧ ∑ j, α' j • η' j = ∑ i, α i • η i := by
  classical
  obtain ⟨η₀, hη₀⟩ := hS
  let e : ι ↪ Fin N :=
    (Fintype.equivFin ι).toEmbedding.trans (Fin.castLEEmb hN)
  let η' : Fin N → E := Function.extend e η (fun _ => η₀)
  let α' : Fin N → ℝ := Function.extend e α 0
  refine ⟨η', α', ?_, ?_, ?_⟩
  · intro j
    by_cases hj : ∃ i, e i = j
    · obtain ⟨i, rfl⟩ := hj
      simpa only [η', α', e.injective.extend_apply] using And.intro (hη i) (hα i)
    · dsimp only [η', α']
      rw [Function.extend_apply' η (fun _ => η₀) j hj,
        Function.extend_apply' α (0 : Fin N → ℝ) j hj]
      exact ⟨hη₀, le_rfl⟩
  · calc
      ∑ j, α' j = ∑ i, α i :=
        Finset.sum_extend_zero_of_injective α e.injective (fun _ => Finset.mem_univ _)
      _ = 1 := hα1
  · have hext : (fun j => α' j • η' j) =
        Function.extend e (fun i => α i • η i) 0 := by
      funext j
      by_cases hj : ∃ i, e i = j
      · obtain ⟨i, rfl⟩ := hj
        simp only [η', α', e.injective.extend_apply]
      · dsimp only [η', α']
        rw [Function.extend_apply' η (fun _ => η₀) j hj,
          Function.extend_apply' α (0 : Fin N → ℝ) j hj,
          Function.extend_apply' (fun i => α i • η i) (0 : Fin N → E) j hj]
        exact zero_smul ℝ η₀
    change (∑ j, (fun j => α' j • η' j) j) = _
    rw [hext]
    exact Finset.sum_extend_zero_of_injective _ e.injective (fun _ => Finset.mem_univ _)

end Yau.NodeProofs.E01Aux
