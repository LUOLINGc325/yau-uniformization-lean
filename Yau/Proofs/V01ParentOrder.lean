import spec.CHAIN.CONTRACTS

/-! The actual V04 enlargement precedes V02 and V03. Every estimate refers
to the same enlarged localization and one common exponent. -/

noncomputable section
open Filter
namespace Yau.Blueprint.V01Proof
variable {n q : ℕ} {X : KahlerManifold n}

theorem exists_enlarged_variation_estimates
    (hV02 : V02Contract X) (hV03 : V03Contract X) (hV04 : V04Contract X)
    (d : VariationData X q) (hd : VariationSetup d) :
    ∃ (k : ClockData X) (B : ℕ → ℝ) (a : ℕ), (∀ j, d.B j ≤ B j) ∧
      let db := {d with B := B}
      VariationSetup db ∧ ClockCutoffs db k ∧ 4 ≤ a ∧
      InitialDiscRegularization db ∧ LocalizationEstimates db ∧ SymbolBounds db a ∧
      (∀ᶠ j in atTop, DeformationEstimate db j a ∧ DeformationRealization db j a) ∧
      FejerEstimates db a ∧ FrequencySelection db ∧ NegativePartEstimates db a ∧
      CenterMajorants db a ∧ SpectralFactorEstimates db a ∧ ClockEstimates db k a ∧
      (∀ᶠ j in atTop, BackwardClockRealization db k j a) ∧
      PositiveReplacement db k a ∧ SymplecticSubmean db k a := by
  obtain ⟨k, _hFiber, _hBase, B, hB, hdB, hCuts, a₄, ha₄, _hPower, _hDamping, hFour⟩ :=
    hV04 q d hd
  let db : VariationData X q := {d with B := B}
  obtain ⟨a₂, _ha₂, hTwo⟩ := hV02 q db hdB
  obtain ⟨hReg, hLoc, a₃, _ha₃, hThree⟩ := hV03 q db hdB
  let a := max a₄ (max a₂ a₃)
  have ha₄a : a₄ ≤ a := le_max_left _ _
  have ha₂a : a₂ ≤ a := (le_max_left _ _).trans (le_max_right _ _)
  have ha₃a : a₃ ≤ a := (le_max_right _ _).trans (le_max_right _ _)
  have hDefReal := hTwo a ha₂a
  have hDef : ∀ᶠ j in atTop, DeformationEstimate db j a :=
    hDefReal.mono (fun _ h => h.1)
  obtain ⟨hSym, _hEnergy⟩ := hThree a ha₃a
  obtain ⟨hFejer, hFreq, hNeg, hCenter, hSpectral, hClock, hBackward, hPos, hSubmean⟩ :=
    hFour a ha₄a hDef hSym hLoc
  exact ⟨k, B, a, hB, hdB, hCuts, ha₄.trans ha₄a, hReg, hLoc, hSym,
    hDefReal, hFejer, hFreq, hNeg, hCenter, hSpectral, hClock, hBackward, hPos, hSubmean⟩

end Yau.Blueprint.V01Proof
