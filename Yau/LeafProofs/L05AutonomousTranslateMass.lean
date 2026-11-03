import Yau.LeafProofs.L05AutonomousAveragePairing

noncomputable section
open Filter Set MeasureTheory Matrix
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
namespace Yau.LeafProofs.L05AutonomousAux
open Yau.Parabolic Yau.LeafProofs.L05Aux

/-- The product is genuinely integrable: every translated L¹ norm is the same actual Haar integral. -/
theorem auto_translation_average_integrable {n : ℕ} (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {a : ℝ → Space n} (ha : Measurable a) {f : Space n → ℝ} (hfm : Measurable f) (hf : Integrable f) :
    Integrable (fun p : Space n × ℝ => f (p.1+a p.2)) (volume.prod μ) := by
  have hm : Measurable (fun p : Space n × ℝ => f (p.1+a p.2)) :=
    hfm.comp (measurable_fst.add (ha.comp measurable_snd))
  apply (integrable_prod_iff' hm.stronglyMeasurable.aestronglyMeasurable).mpr
  constructor
  · exact ae_of_all μ fun s => (measurePreserving_add_right volume (a s)).integrable_comp hf.aestronglyMeasurable |>.mpr hf
  · have heq : (fun s : ℝ => ∫ x, ‖f (x+a s)‖)=(fun _ => ∫ x, ‖f x‖) := by
      funext s
      exact integral_add_right_eq_self (fun x => ‖f x‖) (a s)
    rw [heq]
    exact integrable_const _

/-- Actual spatial averaging by any probability of translations preserves the full L¹ mass. -/
theorem auto_translation_average_mass {n : ℕ} (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {a : ℝ → Space n} (ha : Measurable a) {f : Space n → ℝ} (hfm : Measurable f) (hf : Integrable f) :
    Integrable (fun x => ∫ s, f (x+a s) ∂μ) ∧
      (∫ x, (∫ s, f (x+a s) ∂μ))=∫ x, f x := by
  have hi := auto_translation_average_integrable μ ha hfm hf
  refine ⟨hi.integral_prod_left,?_⟩
  have hh : (∫ x, (∫ s, f (x+a s) ∂μ))=(∫ s, (∫ x, f (x+a s)) ∂μ) :=
    integral_integral_swap hi
  have hinner (s : ℝ) : (∫ x, f (x+a s))=∫ x, f x := integral_add_right_eq_self f (a s)
  simp_rw [hinner] at hh
  simpa only [integral_const,probReal_univ,one_smul] using hh

/-- Restricting the spatial integral can only reduce a nonnegative translated average. -/
theorem auto_translation_average_local_bound {n : ℕ} (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {a : ℝ → Space n} (ha : Measurable a) {f : Space n → ℝ} (hfm : Measurable f) (hf : Integrable f)
    (hf0 : ∀ x, 0≤ f x) (Q : Set (Space n)) :
    IntegrableOn (fun x => ∫ s, f (x+a s) ∂μ) Q ∧
      (∫ x in Q, (∫ s, f (x+a s) ∂μ))≤ ∫ x, f x := by
  obtain ⟨hi,heq⟩ := auto_translation_average_mass μ ha hfm hf
  exact ⟨hi.integrableOn,(setIntegral_le_integral hi (ae_of_all volume fun x => integral_nonneg fun s => hf0 _)).trans_eq heq⟩

end Yau.LeafProofs.L05AutonomousAux
