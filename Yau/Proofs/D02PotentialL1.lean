import Yau.Proofs.D02DiscPotentialRegularity

/-! The actual EReal D04 limit gives a genuine real local L¹ limit.
Infinite values are excluded almost everywhere before taking toReal. -/

open scoped ENNReal Topology ContDiff
open MeasureTheory Set Filter

noncomputable section
namespace Yau.NodeProofs.D02Aux
open Yau Yau.Blueprint Yau.LeafProofs

theorem pshL1Limit_realLocalL1 {m : ℕ} {D : Set (ComplexVector m)}
    (us : ℕ → ComplexVector m → ℝ) (hus : ∀ j, ContinuousOn (us j) D)
    (φ : ℕ → ℕ) (hlim : PshL1Limit D (fun j z => (us j z : EReal)) φ) :
    ∃ v : ComplexVector m → EReal, IsPshOn v D ∧
      (∃ z ∈ D, v z ≠ ⊥) ∧ (∀ᵐ z ∂(lebesgueC m).restrict D, v z ≠ ⊥) ∧
      ∀ K : Set (ComplexVector m), IsCompact K → K ⊆ D →
        IntegrableOn (fun z => (v z).toReal) K (lebesgueC m) ∧
        Tendsto (fun j => ∫ z in K, |us (φ j) z - (v z).toReal| ∂lebesgueC m) atTop (𝓝 0) := by
  obtain ⟨v, hv, hvnontrivial, hvfinite, hKlim, hHartogs⟩ := hlim
  refine ⟨v, hv, hvnontrivial, hvfinite, fun K hK hKD => ?_⟩
  obtain ⟨hInt, hconv⟩ := hKlim K hKD hK
  have hfiniteK := ae_restrict_of_ae_restrict_of_subset hKD hvfinite
  have heq (j : ℕ) : (∫⁻ z in K, erealDist (us (φ j) z : EReal) (v z) ∂lebesgueC m).toReal =
      ∫ z in K, |us (φ j) z - (v z).toReal| ∂lebesgueC m := by
    have hIntj : IntegrableOn (us (φ j)) K (lebesgueC m) := by
      rw [lebesgueC_eq_volume]
      exact ((hus (φ j)).mono hKD).integrableOn_compact hK
    have hdiff : IntegrableOn (fun z => |us (φ j) z - (v z).toReal|) K (lebesgueC m) := by
      simpa only [IntegrableOn, Real.norm_eq_abs, Pi.sub_apply] using (hIntj.sub hInt).norm
    have hdist : (∫⁻ z in K, erealDist (us (φ j) z : EReal) (v z) ∂lebesgueC m) =
        ∫⁻ z in K, ENNReal.ofReal |us (φ j) z - (v z).toReal| ∂lebesgueC m := by
      apply lintegral_congr_ae
      filter_upwards [hfiniteK, ae_restrict_mem hK.measurableSet] with z hz hzK
      rw [Yau.Proofs.D04Aux.erealDist_eq_ofReal_of_finite (EReal.coe_ne_top _) (EReal.coe_ne_bot _)
        (hv.1 z (hKD hzK)).ne hz, EReal.toReal_coe]
    rw [hdist, ← ofReal_integral_eq_lintegral_ofReal hdiff
      (Eventually.of_forall fun _ => abs_nonneg _), ENNReal.toReal_ofReal
        (integral_nonneg fun _ => abs_nonneg _)]
  refine ⟨hInt, ?_⟩
  simpa only [Function.comp_def, heq, ENNReal.toReal_zero] using
    (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hconv

/-- Actual original disc potentials have a real local L¹ extracted limit
with ordinary planar area, ready for the internal Riesz construction. -/
theorem discPotential_realL1_subsequence {n N : ℕ} (X : KahlerManifold n)
    {F : Pt X → ComplexVector N} (hF : IsHolomorphicVecMap F) (hImm : IsImmersionMap F)
    {K : Set (Pt X)} (hK : IsCompact K) (A : ℝ) (fs : ℕ → ℂ → Pt X)
    (hfs : ∀ j, IsHolomorphicDisc (fs j) ∧
      (∀ z : ℂ, ‖z‖ = 1 → fs j z ∈ K) ∧ discArea X.metric.form (fs j) ≤ ENNReal.ofReal A) :
    ∃ (φ : ℕ → ℕ) (v : ComplexVector 1 → EReal) (u : ℂ → ℝ), StrictMono φ ∧
      IsPshOn v (Metric.ball (0 : ComplexVector 1) 1) ∧
      (∃ z ∈ Metric.ball (0 : ComplexVector 1) 1, v z ≠ ⊥) ∧
      (∀ z : ℂ, u z = (v (Yau.Proofs.B01Aux.complexOneEquiv z)).toReal) ∧
      ∀ S : Set ℂ, IsCompact S → S ⊆ Metric.ball (0 : ℂ) 1 →
        IntegrableOn u S volume ∧ Tendsto
          (fun j => ∫ z in S, |immersionPotential X.metric.form F (fs (φ j) z) - u z|) atTop (𝓝 0) := by
  obtain ⟨φ, hφ, hlim⟩ := discPotential_subsequence X hF hImm hK A fs hfs
  let e := Yau.Proofs.B01Aux.complexOneEquiv
  let ur : ℕ → ComplexVector 1 → ℝ := fun j w => immersionPotential X.metric.form F (discModelMap (fs j) w)
  have hcont : ∀ j, ContinuousOn (ur j) (Metric.ball (0 : ComplexVector 1) 1) := by
    intro j w hw
    exact (smoothLevi_disc_model (immersionPotential_smooth X.metric.form
      (L12Aux.metricSmooth_of_smoothMetric X.metric) hF hImm)
      (immersionPotential_levi_posSemidef X hF hImm) (hfs j).1 w hw).1.continuousAt.continuousWithinAt
  obtain ⟨v, hv, hvnontrivial, hvfinite, hlocal⟩ := pshL1Limit_realLocalL1 ur hcont φ hlim
  let u : ℂ → ℝ := fun z => (v (e z)).toReal
  refine ⟨φ, v, u, hφ, hv, hvnontrivial, fun _ => rfl, fun S hS hSD => ?_⟩
  have hSe : IsCompact (e '' S) := hS.image e.continuous
  have hSeD : e '' S ⊆ Metric.ball (0 : ComplexVector 1) 1 := by
    rintro w ⟨z, hz, rfl⟩
    simpa only [Metric.mem_ball, dist_zero_right, e.norm_map] using hSD hz
  obtain ⟨hInt, hconv⟩ := hlocal (e '' S) hSe hSeD
  rw [lebesgueC_eq_volume] at hInt hconv
  have hemb : MeasurableEmbedding e := e.toHomeomorph.measurableEmbedding
  have hpres := Yau.Proofs.B01Aux.complexOneEquiv_measurePreserving
  refine ⟨(hpres.integrableOn_image hemb).mp hInt, ?_⟩
  have heq (j : ℕ) : (∫ w in e '' S, |ur (φ j) w - (v w).toReal|) =
      ∫ z in S, |immersionPotential X.metric.form F (fs (φ j) z) - u z| := by
    have h := (hpres.restrict_image_emb hemb S).integral_comp hemb
      (fun w => |ur (φ j) w - (v w).toReal|)
    simpa only [ur, discModelMap, u, e,
      Yau.Proofs.B01Aux.complexOneEquiv.symm_apply_apply] using h.symm
  simpa only [heq] using hconv

/-- Every analytic input to the limiting Riesz construction is produced
from the original admissible family and the same extracted sequence. -/
theorem discPotential_rieszInputs {n N : ℕ} (X : KahlerManifold n)
    {F : Pt X → ComplexVector N} (hF : IsHolomorphicVecMap F) (hImm : IsImmersionMap F)
    {K : Set (Pt X)} (hK : IsCompact K) (A : ℝ) (fs : ℕ → ℂ → Pt X)
    (hfs : ∀ j, IsHolomorphicDisc (fs j) ∧
      (∀ z : ℂ, ‖z‖ = 1 → fs j z ∈ K) ∧ discArea X.metric.form (fs j) ≤ ENNReal.ofReal A) :
    ∃ (φ : ℕ → ℕ) (u : ℂ → ℝ), StrictMono φ ∧
      (∀ j, ContDiffOn ℝ ∞ (fun z => immersionPotential X.metric.form F (fs (φ j) z))
        (Metric.ball (0 : ℂ) 1) ∧ ∀ z ∈ Metric.ball (0 : ℂ) 1,
          0 ≤ LeafCandidates.realPlanarLaplacian
            (fun w => immersionPotential X.metric.form F (fs (φ j) w)) z) ∧
      ∀ S : Set ℂ, IsCompact S → S ⊆ Metric.ball (0 : ℂ) 1 →
        IntegrableOn u S volume ∧ Tendsto
          (fun j => ∫ z in S, |immersionPotential X.metric.form F (fs (φ j) z) - u z|) atTop (𝓝 0) := by
  obtain ⟨φ, v, u, hφ, hv, hvne, hueq, hlocal⟩ := discPotential_realL1_subsequence X hF hImm hK A fs hfs
  exact ⟨φ, u, hφ, fun j => ⟨immersionPotential_disc_contDiffOn X hF hImm (hfs (φ j)).1,
    fun z hz => immersionPotential_disc_laplacian_nonneg X hF hImm (hfs (φ j)).1 hz⟩, hlocal⟩

end Yau.NodeProofs.D02Aux
