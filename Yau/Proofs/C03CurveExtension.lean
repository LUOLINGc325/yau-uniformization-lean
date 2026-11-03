import Yau.LeafProofs.L23LocalDistanceSupportSaturation

/-! Extend the source path and its parallel vector globally while preserving
all their actual germs along the closed unit interval. -/

noncomputable section
open Filter Set
open scoped Topology ContDiff

namespace Yau.Proofs.C03Aux
open Yau.LeafProofs L23Aux

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem exists_global_curve_pair_extension (γ W : ℝ → E) (δ : ℝ) (hδ : 0 < δ)
    (hγ : ContDiffOn ℝ 3 γ (Ioo (-δ) (1 + δ)))
    (hW : ContDiffOn ℝ 3 W (Ioo (-δ) (1 + δ))) :
    ∃ γ₀ W₀ : ℝ → E, ContDiff ℝ 3 γ₀ ∧ ContDiff ℝ 3 W₀ ∧
      ∀ t ∈ Icc (0 : ℝ) 1, γ₀ =ᶠ[𝓝 t] γ ∧ W₀ =ᶠ[𝓝 t] W := by
  obtain ⟨χ, hχ, hmap, heq⟩ := exists_smooth_unit_saturation hδ
  refine ⟨γ ∘ χ, W ∘ χ, ?_, ?_, ?_⟩
  · exact contDiffOn_univ.mp (hγ.comp ((hχ.of_le (by simp)).contDiffOn) hmap)
  · exact contDiffOn_univ.mp (hW.comp ((hχ.of_le (by simp)).contDiffOn) hmap)
  · intro t ht
    constructor
    · simpa only [Function.comp_def, id_eq] using (heq t ht).fun_comp γ
    · simpa only [Function.comp_def, id_eq] using (heq t ht).fun_comp W

end Yau.Proofs.C03Aux
