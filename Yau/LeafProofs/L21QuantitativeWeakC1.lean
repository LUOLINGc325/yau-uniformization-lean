import Yau.LeafProofs.L21QuantitativeC1

/-! The quantitative derivative estimate holds for one actual smooth
representative of the original weak solution and retains its original L² mass. -/

open MeasureTheory Filter
open scoped ContDiff
noncomputable section
namespace Yau.LeafProofs.L21Aux

variable {n : ℕ}

theorem exists_inner_smooth_column_with_C1 {O R : Set (X n)}
    (hO : IsOpen O) (hR : IsOpen R) (hcR : IsCompact (closure R)) (hRO : closure R ⊆ O) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (A : X n → Matrix (Fin n) (Fin n) ℂ), MatrixSmoothOn A O →
      (∀ x ∈ O, Yau.LeafCandidates.matrixOpNorm (A x) ≤ 1 / 2) →
      JetBound (realDimension n + 1) 1 A O →
      ∀ δ : ℝ, 0 ≤ δ → JetBound (realDimension n + 1) δ A O →
      ∀ (u : X n → ℂ), MemLp u 2 ((Yau.lebesgueC n).restrict O) → ∀ k : Fin n,
      DbarWeakOn A u (fun x i => A x i k) O →
      ∃ v : X n → ℂ, ContDiff ℝ ∞ v ∧ v =ᵐ[(Yau.lebesgueC n).restrict R] u ∧
        (∀ x ∈ R, ∀ i, dbarA A i v x = A x i k) ∧
        ∀ x ∈ R, ‖fderiv ℝ v x‖ ^ 2 ≤
          C * ((∫ y in O, ‖u y‖ ^ 2 ∂Yau.lebesgueC n) + δ ^ 2) := by
  obtain ⟨V, hV, hRV, hVO, hcV⟩ := exists_open_between_and_isCompact_closure hcR hO hRO
  obtain ⟨C, hC, hBound⟩ := exists_inner_fderiv_norm_sq_bound hV hcV hR hcR hRV
  refine ⟨C, hC, ?_⟩
  intro A hA hsmall hJet δ hδ hSmallJet u hu k heq
  have huLocal : LocallyL2On u O := fun K _ hKO =>
    hu.mono_measure (Measure.restrict_mono hKO le_rfl)
  obtain ⟨v, hv, hAE, hvEq⟩ := exists_inner_smooth_solution hO hA hsmall
    (fun x i => A x i k) (fun i => hA i k) u huLocal heq hV hcV hVO
  have hV0 : V ⊆ O := subset_closure.trans hVO
  have hR0 : R ⊆ V := subset_closure.trans hRV
  have hAER : v =ᵐ[(Yau.lebesgueC n).restrict R] u := by
    filter_upwards [ae_restrict_of_ae ((ae_restrict_iff' hV.measurableSet).mp hAE),
      ae_restrict_mem hR.measurableSet] with x hx hxin
    exact hx (hR0 hxin)
  refine ⟨v, hv, hAER, fun x hx => hvEq x (hR0 hx), ?_⟩
  have hmass : (∫ y in V, ‖v y‖ ^ 2 ∂Yau.lebesgueC n) ≤
      ∫ y in O, ‖u y‖ ^ 2 ∂Yau.lebesgueC n := by
    have he : (∫ y in V, ‖v y‖ ^ 2 ∂Yau.lebesgueC n) =
        ∫ y in V, ‖u y‖ ^ 2 ∂Yau.lebesgueC n := by
      apply integral_congr_ae
      exact hAE.mono fun y hy => congrArg (fun z : ℂ => ‖z‖ ^ 2) hy
    rw [he]
    exact integral_mono_measure (Measure.restrict_mono hV0 le_rfl)
      (Eventually.of_forall fun y => sq_nonneg _) (hu.integrable_norm_pow (p := 2) (by decide))
  intro x hx
  exact (hBound A (fun i j => (hA i j).mono hV0) (fun y hy => hsmall y (hV0 hy))
    (jetBound_mono_domain hV0 hJet) δ hδ (jetBound_mono_domain hV0 hSmallJet) v hv k hvEq x hx).trans
    (mul_le_mul_of_nonneg_left (add_le_add hmass (le_refl _)) hC.le)

end Yau.LeafProofs.L21Aux
