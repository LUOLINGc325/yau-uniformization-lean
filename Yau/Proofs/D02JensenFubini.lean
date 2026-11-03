import Yau.Proofs.D02JensenKernel

open MeasureTheory Filter Set
open scoped Topology ContDiff

noncomputable section
namespace Yau.NodeProofs.D02JensenAux

/-- A uniform area-integral bound for a nonnegative translated kernel gives
joint integrability against every finite positive measure supported in `D`. -/
theorem integrable_pair_kernel {S D : Set ℂ} {ν : Measure ℂ} [IsFiniteMeasure ν]
    {k : ℂ → ℝ} (hk : Measurable k) (hk0 : ∀ z, 0 ≤ k z) {C : ℝ}
    (hνD : ∀ᵐ w ∂ν, w ∈ D)
    (hkw : ∀ w ∈ D, IntegrableOn (fun z ↦ k (w - z)) S volume ∧
      (∫ z in S, k (w - z)) ≤ C) :
    Integrable (fun p : ℂ × ℂ ↦ k (p.2 - p.1)) ((volume.restrict S).prod ν) := by
  have hj : Measurable (fun p : ℂ × ℂ ↦ k (p.2 - p.1)) :=
    hk.comp (measurable_snd.sub measurable_fst)
  apply (integrable_prod_iff' hj.aestronglyMeasurable).mpr
  refine ⟨hνD.mono (fun w hw ↦ (hkw w hw).1), ?_⟩
  apply (integrable_const C).mono'
    hj.stronglyMeasurable.norm.integral_prod_left'.aestronglyMeasurable
  filter_upwards [hνD] with w hw
  have heq : (∫ z in S, ‖k (w - z)‖) = ∫ z in S, k (w - z) := by
    congr 1
    funext z
    exact Real.norm_of_nonneg (hk0 _)
  rw [heq, Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun z ↦ hk0 _)]
  exact (hkw w hw).2

/-- The corresponding integral estimate has exactly one factor of the total
mass. It will cancel the probability normalization in Jensen's inequality. -/
theorem integral_pair_kernel_le {S D : Set ℂ} {ν : Measure ℂ} [IsFiniteMeasure ν]
    {k : ℂ → ℝ} (hk : Measurable k) (hk0 : ∀ z, 0 ≤ k z) {C : ℝ}
    (hνD : ∀ᵐ w ∂ν, w ∈ D)
    (hkw : ∀ w ∈ D, IntegrableOn (fun z ↦ k (w - z)) S volume ∧
      (∫ z in S, k (w - z)) ≤ C) :
    (∫ z in S, ∫ w, k (w - z) ∂ν) ≤ C * (ν univ).toReal := by
  have hi := integrable_pair_kernel hk hk0 hνD hkw
  rw [integral_integral_swap hi]
  have hle : (∫ w, (∫ z in S, k (w - z)) ∂ν) ≤ ∫ _w, C ∂ν := by
    apply integral_mono_ae hi.integral_prod_right (integrable_const C)
    exact hνD.mono (fun w hw ↦ (hkw w hw).2)
  simpa only [integral_const, smul_eq_mul, measureReal_def, mul_comm] using hle

end Yau.NodeProofs.D02JensenAux
