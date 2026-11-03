import Yau.Proofs.V03RadialFunctional
import Yau.Proofs.V03Infimum

/-! All three original initial-regularization clauses, including arbitrary
real penalties and EReal infinite infima and minimizing-sequence limits. -/

open scoped Manifold Topology ContDiff Matrix ComplexOrder
open Filter

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

variable {n q : ℕ} {X : KahlerManifold n}

theorem radial_approximation {d : VariationData X q} (hd : VariationSetup d)
    (j : ℕ) (ε : ℝ) (F : VariationDisc X) (hF : AdmissibleVariationDisc d j F)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧ AdmissibleVariationDisc d j (radialVariationDisc F r) ∧
      InitiallyExtendedVariationDisc (radialVariationDisc F r) ∧
      |(variationEnergy d j (radialVariationDisc F r)).toReal - (variationEnergy d j F).toReal| < δ ∧
      |penalizedFunctional d j ε (radialVariationDisc F r) - penalizedFunctional d j ε F| < δ := by
  have hpos : ∀ᶠ r : ℝ in 𝓝[<] 1, 0 < r :=
    mem_inf_of_left (Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have hIcc : ∀ᶠ r : ℝ in 𝓝[<] 1, r ∈ Set.Icc (0 : ℝ) 1 := by
    filter_upwards [hpos, self_mem_nhdsWithin] with r hr hr1
    exact ⟨hr.le, hr1.le⟩
  have hle : (𝓝[<] (1 : ℝ)) ≤ 𝓝[Set.Icc 0 1] 1 :=
    le_inf nhdsWithin_le_nhds (le_principal_iff.mpr hIcc)
  have he : ∀ᶠ r : ℝ in 𝓝[Set.Icc 0 1] 1,
      |(variationEnergy d j (radialVariationDisc F r)).toReal - (variationEnergy d j F).toReal| < δ := by
    have hh := (radial_energy_toReal_tendsto hd hF).eventually
      (Metric.ball_mem_nhds (variationEnergy d j F).toReal hδ)
    simpa only [Metric.mem_ball, Real.dist_eq] using hh
  have hc : ∀ᶠ r : ℝ in 𝓝[Set.Icc 0 1] 1,
      |penalizedFunctional d j ε (radialVariationDisc F r) - penalizedFunctional d j ε F| < δ := by
    have hh := (penalizedFunctional_radial_tendsto hd hF ε).eventually
      (Metric.ball_mem_nhds (penalizedFunctional d j ε F) hδ)
    simpa only [Metric.mem_ball, Real.dist_eq] using hh
  have hall : ∀ᶠ r : ℝ in 𝓝[<] 1, 0 < r ∧ r < 1 ∧
      AdmissibleVariationDisc d j (radialVariationDisc F r) ∧
      |(variationEnergy d j (radialVariationDisc F r)).toReal - (variationEnergy d j F).toReal| < δ ∧
      |penalizedFunctional d j ε (radialVariationDisc F r) - penalizedFunctional d j ε F| < δ := by
    filter_upwards [hpos, self_mem_nhdsWithin, (radial_admissible_eventually hd hF).filter_mono hle,
      he.filter_mono hle, hc.filter_mono hle] with r hr hr1 ha her hcr
    exact ⟨hr, hr1, ha, her, hcr⟩
  obtain ⟨r, hr, hr1, ha, her, hcr⟩ := hall.exists
  exact ⟨r, hr, hr1, ha, radial_initiallyExtended F hF.1 hF.2.1 hr hr1, her, hcr⟩

theorem initialDiscRegularization {d : VariationData X q} (hd : VariationSetup d) :
    InitialDiscRegularization d := by
  refine ⟨radial_approximation hd, ?_, ?_⟩
  · intro j ε
    apply ereal_iInf_eq_of_approximation
    intro F hF δ hδ
    obtain ⟨r, _, _, ha, hext, _, hc⟩ := radial_approximation hd j ε F hF δ hδ
    exact ⟨radialVariationDisc F r, ha, hext, hc⟩
  · intro j ε F hF
    have hchoose : ∀ ν : ℕ, ∃ r : ℝ, 0 < r ∧ r < 1 ∧
        AdmissibleVariationDisc d j (radialVariationDisc (F ν) r) ∧
        InitiallyExtendedVariationDisc (radialVariationDisc (F ν) r) ∧
        |(variationEnergy d j (radialVariationDisc (F ν) r)).toReal -
          (variationEnergy d j (F ν)).toReal| ≤ (ν + 1 : ℝ)⁻¹ ∧
        |penalizedFunctional d j ε (radialVariationDisc (F ν) r) -
          penalizedFunctional d j ε (F ν)| ≤ (ν + 1 : ℝ)⁻¹ := by
      intro ν
      obtain ⟨r, hr, hr1, ha, hext, he, hc⟩ :=
        radial_approximation hd j ε (F ν) (hF.1 ν) (ν + 1 : ℝ)⁻¹ (by positivity)
      exact ⟨r, hr, hr1, ha, hext, he.le, hc.le⟩
    choose r hr using hchoose
    refine ⟨r, ?_, ?_⟩
    · intro ν
      exact ⟨(hr ν).1, (hr ν).2.1, (hr ν).2.2.2.1, (hr ν).2.2.2.2.1⟩
    · refine ⟨fun ν => (hr ν).2.2.1, ?_⟩
      exact ereal_tendsto_of_abs_sub_le_inv hF.2 (fun ν => (hr ν).2.2.2.2.2)

end Yau.Blueprint.V03Proof
