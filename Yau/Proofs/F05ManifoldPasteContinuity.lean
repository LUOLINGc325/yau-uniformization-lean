import Yau.Proofs.F05ManifoldNonlinearPaste

/-! The actual time paste is continuous on the closed physical cylinder,
including its initial face and the joining slice. -/

open Set
noncomputable section
namespace Yau.Proofs.F05Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem F05_manifold_timePaste_continuous {O : Set M.Carrier} {τ T : ℝ}
    (hτ : 0 ≤ τ) (hτT : τ ≤ T) (u v : M.Carrier → ℝ → ℝ)
    (hu : ContinuousOn (fun z : M.Carrier × ℝ => u z.1 z.2) (closure O ×ˢ Icc 0 τ))
    (hv : ContinuousOn (fun z : M.Carrier × ℝ => v z.1 z.2) (closure O ×ˢ Icc τ T))
    (hTrace : ∀ x ∈ closure O, u x τ = v x τ) :
    ContinuousOn (fun z : M.Carrier × ℝ => F05ManifoldTimePaste τ u v z.1 z.2)
      (closure O ×ˢ Icc 0 T) := by
  have hLeft : ContinuousOn
      (fun z : M.Carrier × ℝ => F05ManifoldTimePaste τ u v z.1 z.2)
      (closure O ×ˢ Icc 0 τ) := by
    apply hu.congr
    intro z hz
    simp only [F05ManifoldTimePaste,hz.2.2,ite_true]
  have hRight : ContinuousOn
      (fun z : M.Carrier × ℝ => F05ManifoldTimePaste τ u v z.1 z.2)
      (closure O ×ˢ Icc τ T) := by
    apply hv.congr
    intro z hz
    by_cases ht : z.2 ≤ τ
    · have hEq := le_antisymm ht hz.2.1
      simp only [F05ManifoldTimePaste,hEq,le_refl,ite_true]
      exact hTrace z.1 hz.1
    · simp only [F05ManifoldTimePaste,ht,ite_false]
  have hCover : (closure O ×ˢ Icc 0 τ) ∪ (closure O ×ˢ Icc τ T) =
      closure O ×ˢ Icc 0 T := by
    ext z
    constructor
    · rintro (hz|hz)
      · exact ⟨hz.1,hz.2.1,hz.2.2.trans hτT⟩
      · exact ⟨hz.1,hτ.trans hz.2.1,hz.2.2⟩
    · intro hz
      by_cases ht : z.2 ≤ τ
      · exact Or.inl ⟨hz.1,hz.2.1,ht⟩
      · exact Or.inr ⟨hz.1,(not_le.mp ht).le,hz.2.2⟩
  rw [← hCover]
  exact hLeft.union_of_isClosed hRight (isClosed_closure.prod isClosed_Icc)
    (isClosed_closure.prod isClosed_Icc)

end Yau.Proofs.F05Aux
