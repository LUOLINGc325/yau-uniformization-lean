import Yau.Proofs.E01ConeMass
import Yau.Proofs.E01ConvexHull

/-! Compact mass slices prove closedness of the actual finite conic hull. -/

noncomputable section
open Set

namespace Yau.NodeProofs.E01Aux

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem isCompact_cone_hull_mass_slice
    {S : Set E} (hSne : S.Nonempty) (hS : IsCompact S)
    (τ : E →L[ℝ] ℝ) (hτ : ∀ x ∈ S, τ x = 1) (R : ℝ) :
    IsCompact {A : E | A ∈ PointedCone.hull ℝ S ∧ τ A ≤ R} := by
  have hImage :
      (fun p : ℝ × E => p.1 • p.2) '' (Icc 0 R ×ˢ convexHull ℝ S) =
        {A : E | A ∈ PointedCone.hull ℝ S ∧ τ A ≤ R} := by
    ext A
    constructor
    · rintro ⟨⟨r, B⟩, ⟨hr, hB⟩, rfl⟩
      refine ⟨nonnegative_smul_convexHull_mem_cone hB hr.1, ?_⟩
      have hτB : τ B = 1 := convexHull_functional_eq_one τ.toLinearMap hτ hB
      simpa only [map_smul, smul_eq_mul, hτB, mul_one] using hr.2
    · rintro ⟨hA, hR⟩
      obtain ⟨B, hB, heq⟩ :=
        cone_hull_normalized_representation hSne τ.toLinearMap hτ hA
      exact ⟨(τ A, B),
        ⟨⟨cone_hull_functional_nonneg τ.toLinearMap hτ hA, hR⟩, hB⟩, heq.symm⟩
  rw [← hImage]
  exact (isCompact_Icc.prod (isCompact_convexHull_of_finiteDimensional hS)).image
    (by fun_prop)

theorem isClosed_cone_hull_of_compact_normalized_base
    {S : Set E} (hS : IsCompact S) (τ : E →L[ℝ] ℝ)
    (hτ : ∀ x ∈ S, τ x = 1) :
    IsClosed (PointedCone.hull ℝ S : Set E) := by
  classical
  by_cases hSne : S.Nonempty
  · apply isClosed_of_closure_subset
    intro A hA
    let R := max (τ A) 0 + 1
    let U : Set E := {B | τ B < R}
    have hU : IsOpen U := isOpen_lt τ.continuous continuous_const
    have hAU : A ∈ U :=
      lt_of_le_of_lt (le_max_left (τ A) 0) (lt_add_one _)
    have hlocal : A ∈ closure ((PointedCone.hull ℝ S : Set E) ∩ U) := by
      rw [mem_closure_iff]
      intro O hO hAO
      obtain ⟨B, ⟨hBO, hBU⟩, hBC⟩ :=
        mem_closure_iff.mp hA (O ∩ U) (hO.inter hU) ⟨hAO, hAU⟩
      exact ⟨B, hBO, hBC, hBU⟩
    have hsub : (PointedCone.hull ℝ S : Set E) ∩ U ⊆
        {B : E | B ∈ PointedCone.hull ℝ S ∧ τ B ≤ R} :=
      fun B hB => ⟨hB.1, hB.2.le⟩
    exact (closure_minimal hsub
      (isCompact_cone_hull_mass_slice hSne hS τ hτ R).isClosed hlocal).1
  · have hSe : S = ∅ := Set.not_nonempty_iff_eq_empty.mp hSne
    simpa only [hSe, PointedCone.hull, Submodule.span_empty, Submodule.bot_coe] using
      (isClosed_singleton : IsClosed ({(0 : E)} : Set E))

end Yau.NodeProofs.E01Aux
