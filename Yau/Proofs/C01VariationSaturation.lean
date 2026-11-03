import Yau.Proofs.C01SmoothSaturation
import Yau.Proofs.C01FamilyPathEnergy

/-! Extending a local path family by a genuine smooth saturation
preserves its actual jets everywhere on the compact unit interval. -/

noncomputable section
open Filter
open scoped Topology ContDiff Manifold

namespace Yau.NodeProofs.C01Aux
open Yau Yau.Blueprint Yau.LeafProofs.L12Aux

theorem exists_smooth_saturation_into_open_unit
    (J : Set ℝ) (hJ : IsOpen J) (hunit : Set.Icc (0 : ℝ) 1 ⊆ J) :
    ∃ χ : ℝ → ℝ, ContDiff ℝ ∞ χ ∧ Set.MapsTo χ Set.univ J ∧
      ∀ u ∈ Set.Icc (0 : ℝ) 1, χ =ᶠ[𝓝 u] id := by
  obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhds_iff.mp
    (hJ.mem_nhds (hunit (by norm_num : (0 : ℝ) ∈ Set.Icc 0 1)))
  obtain ⟨s, hs, hssub⟩ := Metric.mem_nhds_iff.mp
    (hJ.mem_nhds (hunit (by norm_num : (1 : ℝ) ∈ Set.Icc 0 1)))
  let δ := min r s / 2
  have hδ : 0 < δ := half_pos (lt_min hr hs)
  have hδr : δ < r := by dsimp only [δ]; linarith [min_le_left r s]
  have hδs : δ < s := by dsimp only [δ]; linarith [min_le_right r s]
  have hsub : Set.Ioo (-δ) (1 + δ) ⊆ J := by
    intro u hu
    by_cases hu0 : u < 0
    · apply hrsub
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_neg hu0]
      linarith [hu.1]
    · by_cases hu1 : 1 < u
      · apply hssub
        rw [Metric.mem_ball, Real.dist_eq, abs_of_pos (sub_pos.mpr hu1)]
        linarith [hu.2]
      · exact hunit ⟨le_of_not_gt hu0, le_of_not_gt hu1⟩
  obtain ⟨χ, hχ, hmap, heq⟩ := exists_smooth_unit_saturation hδ
  exact ⟨χ, hχ, fun u hu => hsub (hmap hu), heq⟩

variable {n : ℕ} {M : ComplexManifold n}

theorem exists_saturated_path_family
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : E → ℝ → M.Carrier) (U : Set E) (J : Set ℝ)
    (hJ : IsOpen J) (hunit : Set.Icc (0 : ℝ) 1 ⊆ J) :
    letI := manifold_realSmooth M
    ContMDiffOn 𝓘(ℝ, E × ℝ) 𝓘(ℝ, ComplexVector n) 3
      (Function.uncurry F) (U ×ˢ J) →
    ∃ B : E → ℝ → M.Carrier,
      ContMDiffOn 𝓘(ℝ, E × ℝ) 𝓘(ℝ, ComplexVector n) 3
        (Function.uncurry B) (U ×ˢ Set.univ) ∧
      ∀ u ∈ Set.Icc (0 : ℝ) 1, ∀ᶠ s in 𝓝 u, ∀ v, B v s = F v s := by
  letI := manifold_realSmooth M
  intro hF
  obtain ⟨χ, hχ, hmap, heq⟩ := exists_smooth_saturation_into_open_unit J hJ hunit
  let B : E → ℝ → M.Carrier := fun v u => F v (χ u)
  have harg : ContDiff ℝ 3 (fun p : E × ℝ => (p.1, χ p.2)) :=
    contDiff_fst.prodMk ((hχ.of_le (by simp)).comp contDiff_snd)
  refine ⟨B, hF.comp harg.contMDiff.contMDiffOn (fun p hp => ⟨hp.1, hmap (Set.mem_univ _)⟩), ?_⟩
  intro u hu
  filter_upwards [heq u hu] with s hs
  intro v
  exact congrArg (F v) hs

end Yau.NodeProofs.C01Aux
