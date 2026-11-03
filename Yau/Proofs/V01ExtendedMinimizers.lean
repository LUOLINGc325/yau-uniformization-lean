import Yau.Proofs.V01Minimizing

/-! The same minimizing family is regularized initially and given the one
frame selector from D05. No spectral parameter occurs in this family. -/

noncomputable section
open Set Filter
open scoped Topology
namespace Yau.Blueprint.V01Proof
variable {n q : ℕ} {X : KahlerManifold n}

theorem exists_extended_minimizingSequence
    (d : VariationData X q) (hReg : InitialDiscRegularization d)
    (j : ℕ) (ε : ℝ) (hne : ∃ F, AdmissibleVariationDisc d j F) :
    ∃ F : ℕ → VariationDisc X, MinimizingSequence d j ε F ∧
      ∀ ν, InitiallyExtendedVariationDisc (F ν) := by
  obtain ⟨F, hF⟩ := exists_minimizingSequence d j ε hne
  obtain ⟨r, hr, hRadial⟩ := hReg.2.2 j ε F hF
  exact ⟨fun ν => radialVariationDisc (F ν) (r ν), hRadial,
    fun ν => (hr ν).2.2.1⟩

theorem exists_extended_localizedMinimizers
    (d : VariationData X q) (hReg : InitialDiscRegularization d)
    (hne : ∀ᶠ j in atTop, ∃ F, AdmissibleVariationDisc d j F) :
    ∃ F : ℕ → ℝ → ℕ → VariationDisc X,
      ∀ᶠ j in atTop, ∀ᶠ ε in 𝓝[>] (0 : ℝ),
        MinimizingSequence d j ε (F j ε) ∧
          ∀ ν, InitiallyExtendedVariationDisc (F j ε ν) := by
  classical
  have hchoice (j : ℕ) (ε : ℝ) : ∃ F : ℕ → VariationDisc X,
      (∃ F₀, AdmissibleVariationDisc d j F₀) →
        MinimizingSequence d j ε F ∧ ∀ ν, InitiallyExtendedVariationDisc (F ν) := by
    by_cases hj : ∃ F₀, AdmissibleVariationDisc d j F₀
    · obtain ⟨F, hF⟩ := exists_extended_minimizingSequence d hReg j ε hj
      exact ⟨F, fun _ => hF⟩
    · exact ⟨fun _ => defaultVariationDisc d, fun h => (hj h).elim⟩
  choose F hF using hchoice
  refine ⟨F, ?_⟩
  filter_upwards [hne] with j hj
  exact Eventually.of_forall (fun ε => hF j ε hj)

theorem exists_master_minimizers_and_frames
    (d : VariationData X q) (hG : CotangentImmersion d.G)
    (hD05 : DiscFramesContract X.manifold)
    (hReg : InitialDiscRegularization d) (hLoc : LocalizationEstimates d) :
    ∃ (F : ℕ → ℝ → ℕ → VariationDisc X)
      (E : ℕ → ℝ → ℕ → ℂ → CotangentMatrix n),
      LocalizedMinimizers d F ∧
      ∀ᶠ j in atTop, ∀ᶠ ε in 𝓝[>] (0 : ℝ),
        MinimizingSequence d j ε (F j ε) ∧
          ∀ ν, InitiallyExtendedVariationDisc (F j ε ν) ∧
            NormalizedDiscFrame d.G (F j ε ν).f (E j ε ν) := by
  obtain ⟨F, hF⟩ := exists_extended_localizedMinimizers d hReg
    (hLoc.2.1.mono (fun _ hj => hj.1))
  obtain ⟨chooseE, hChooseE, _hBoundary, _hCenter⟩ := hD05 q d.G hG
  refine ⟨F, fun j ε ν => chooseE (F j ε ν).f,
    hF.mono (fun _ hj => hj.mono (fun _ h => h.1)), ?_⟩
  filter_upwards [hF] with j hj
  filter_upwards [hj] with ε hε
  refine ⟨hε.1, fun ν => ⟨hε.2 ν, ?_⟩⟩
  apply hChooseE
  obtain ⟨r, hr, hSpace, _hTime⟩ := hε.2 ν
  exact ⟨r, hr, hSpace⟩

end Yau.Blueprint.V01Proof
