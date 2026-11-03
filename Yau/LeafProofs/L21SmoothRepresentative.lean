import Yau.LeafProofs.L21CoordinateWeakJets

/-! A single actual smooth representative is selected from all finite weak
jets. Real and imaginary parts use the same literal original rough input. -/

open MeasureTheory Filter
open scoped ContDiff
noncomputable section
namespace Yau.LeafProofs.L21Aux

variable {n : ℕ}

theorem exists_complex_smooth_representative_of_finite_weak_jets
    (u : X n → ℂ) (hjets : ∀ N : ℕ, ∃ U : List (Yau.RIdx n) → X n → ℂ,
      FiniteComplexWeakJet N u U) :
    ∃ v : X n → ℂ, ContDiff ℝ ∞ v ∧ v =ᵐ[Yau.lebesgueC n] u := by
  have hj (ℓ : ℂ →L[ℝ] ℝ) : ∀ N : ℕ,
      ∃ V : List (Fin (realDimension n)) → (Fin (realDimension n) → ℝ) → ℝ,
        Yau.LeafProofs.L16Aux.FiniteCoordinateWeakJet N
          (fun y => ℓ (u ((realCoordinates n).symm y))) V := by
    intro N
    obtain ⟨U, hU⟩ := hjets N
    exact ⟨realCoordinateJet ℓ U, finiteComplexWeakJet_realCoordinates ℓ N u U hU⟩
  obtain ⟨r, hr, hrAE⟩ :=
    Yau.LeafProofs.L16Aux.smooth_representative_of_finite_coordinate_weak_jets (hj Complex.reCLM)
  obtain ⟨s, hs, hsAE⟩ :=
    Yau.LeafProofs.L16Aux.smooth_representative_of_finite_coordinate_weak_jets (hj Complex.imCLM)
  let v : X n → ℂ := fun x => (r (realCoordinates n x) : ℂ) + Complex.I * (s (realCoordinates n x) : ℂ)
  have hv : ContDiff ℝ ∞ v :=
    (Complex.ofRealCLM.contDiff.comp (hr.comp (realCoordinates n).contDiff)).add
      (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp (hs.comp (realCoordinates n).contDiff)))
  refine ⟨v, hv, ?_⟩
  have hR := (realCoordinates_measurePreserving n).quasiMeasurePreserving.ae hrAE
  have hI := (realCoordinates_measurePreserving n).quasiMeasurePreserving.ae hsAE
  filter_upwards [hR, hI] with x hRx hIx
  simp only [ContinuousLinearEquiv.symm_apply_apply] at hRx hIx
  change r (realCoordinates n x) = (u x).re at hRx
  change s (realCoordinates n x) = (u x).im at hIx
  change (r (realCoordinates n x) : ℂ) + Complex.I * (s (realCoordinates n x) : ℂ) = u x
  rw [hRx, hIx]
  simpa only [mul_comm] using Complex.re_add_im (u x)

theorem exists_smooth_cutoff_representative_of_dbarWeak {O : Set (X n)} (hO : IsOpen O)
    {A : X n → Matrix (Fin n) (Fin n) ℂ} (hA : MatrixSmoothOn A O)
    (hsmall : ∀ x ∈ O, Yau.LeafCandidates.matrixOpNorm (A x) ≤ 1 / 2)
    (f : X n → Fin n → ℂ) (hf : ∀ i, ContDiffOn ℝ ∞ (fun x => f x i) O)
    (u : X n → ℂ) (hu : LocallyL2On u O) (heq : DbarWeakOn A u f O)
    {V : Set (X n)} (hV : IsOpen V) (hcV : IsCompact (closure V)) (hVO : closure V ⊆ O)
    (χ : X n → ℂ) (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ) (hsχ : tsupport χ ⊆ V) :
    ∃ v : X n → ℂ, ContDiff ℝ ∞ v ∧ v =ᵐ[Yau.lebesgueC n] (fun x => χ x * u x) := by
  apply exists_complex_smooth_representative_of_finite_weak_jets
  intro N
  obtain ⟨U, hU⟩ := exists_finite_weak_graph_jet hO hA hsmall f hf u hu heq N hV hcV hVO
  exact ⟨cutoffWordJet χ U, (weakGraphJet_cutoff hV U N hU χ hχ hcχ hsχ).1⟩

theorem exists_inner_smooth_representative {O R : Set (X n)} (hO : IsOpen O)
    {A : X n → Matrix (Fin n) (Fin n) ℂ} (hA : MatrixSmoothOn A O)
    (hsmall : ∀ x ∈ O, Yau.LeafCandidates.matrixOpNorm (A x) ≤ 1 / 2)
    (f : X n → Fin n → ℂ) (hf : ∀ i, ContDiffOn ℝ ∞ (fun x => f x i) O)
    (u : X n → ℂ) (hu : LocallyL2On u O) (heq : DbarWeakOn A u f O)
    (hR : IsOpen R) (hcR : IsCompact (closure R)) (hRO : closure R ⊆ O) :
    ∃ v : X n → ℂ, ContDiff ℝ ∞ v ∧ v =ᵐ[(Yau.lebesgueC n).restrict R] u := by
  obtain ⟨V, hV, hRV, hVO, hcV⟩ := exists_open_between_and_isCompact_closure hcR hO hRO
  obtain ⟨χ, hχ, hcχ, hsχ, _hχrange, hχR⟩ :=
    Yau.LeafProofs.L14Aux.exists_model_open_cutoff hV hcR hRV
  obtain ⟨v, hv, hvAE⟩ := exists_smooth_cutoff_representative_of_dbarWeak hO hA hsmall f hf u hu heq
    hV hcV hVO (fun x => (χ x : ℂ)) (Complex.ofRealCLM.contDiff.comp hχ)
    (hcχ.comp_left Complex.ofReal_zero) ((tsupport_comp_subset Complex.ofReal_zero χ).trans hsχ)
  refine ⟨v, hv, ?_⟩
  filter_upwards [ae_restrict_of_ae hvAE, ae_restrict_mem hR.measurableSet] with x hx hxin
  rw [hx, (hχR x (subset_closure hxin)).1, Complex.ofReal_one, one_mul]

end Yau.LeafProofs.L21Aux
