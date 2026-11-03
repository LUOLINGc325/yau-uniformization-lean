import Yau.Proofs.F03ExhaustionKernelFamily

/-! Actual finite-mass monotone convergence for nonnegative real functions. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal
namespace Yau.Proofs.F03Aux
set_option maxHeartbeats 1000000

theorem integrable_monotone_limit_of_integral_le {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (f : ℕ → α → ℝ) (F : α → ℝ) (B : ℝ)
    (hi : ∀ j, Integrable (f j) μ) (hn : ∀ j x, 0 ≤ f j x)
    (hmono : ∀ x, Monotone (fun j => f j x))
    (hlim : ∀ x, Tendsto (fun j => f j x) atTop (𝓝 (F x)))
    (hbound : ∀ j, (∫ x, f j x ∂μ) ≤ B) :
    Integrable F μ ∧ (∫ x, F x ∂μ) ≤ B := by
  have hnF : ∀ x, 0 ≤ F x := fun x => ge_of_tendsto' (hlim x) (fun j => hn j x)
  have hlin : Tendsto (fun j => ∫⁻ x, ENNReal.ofReal (f j x) ∂μ) atTop
      (𝓝 (∫⁻ x, ENNReal.ofReal (F x) ∂μ)) := by
    apply lintegral_tendsto_of_tendsto_of_monotone
    · exact fun j => (hi j).aemeasurable.ennreal_ofReal
    · exact ae_of_all μ (fun x i j hij => ENNReal.ofReal_le_ofReal (hmono x hij))
    · exact ae_of_all μ (fun x => ENNReal.continuous_ofReal.continuousAt.tendsto.comp (hlim x))
  have hlinBound : (∫⁻ x, ENNReal.ofReal (F x) ∂μ) ≤ ENNReal.ofReal B := by
    apply le_of_tendsto' hlin
    intro j
    rw [← ofReal_integral_eq_lintegral_ofReal (hi j) (ae_of_all μ (hn j))]
    exact ENNReal.ofReal_le_ofReal (hbound j)
  have hF : Integrable F μ := by
    refine ⟨aestronglyMeasurable_of_tendsto_ae atTop (fun j => (hi j).1)
      (ae_of_all μ hlim),?_⟩
    apply (hasFiniteIntegral_iff_ofReal (ae_of_all μ hnF)).mpr
    exact hlinBound.trans_lt ENNReal.ofReal_lt_top
  refine ⟨hF,?_⟩
  apply le_of_tendsto' (integral_tendsto_of_tendsto_of_monotone hi hF
    (ae_of_all μ hmono) (ae_of_all μ hlim)) hbound

end Yau.Proofs.F03Aux
