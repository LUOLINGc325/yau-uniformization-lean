import Yau.Proofs.D02RemovableRay
import Yau.Proofs.D02RemovableAmbient
import Yau.Proofs.D02RemovableExtension

open scoped Manifold Topology ContDiff ENNReal
open MeasureTheory Set Filter

noncomputable section
namespace Yau.NodeProofs.D02RemovableAux
open Yau Yau.Blueprint Yau.LeafProofs Yau.NodeProofs.D02Aux
set_option backward.isDefEq.respectTransparency false

/-- Genuine weighted physical energy, completeness of the original metric,
and bounded injective holomorphic ambient coordinates produce one and the
same radial limit, full punctured limit, and holomorphic extension. -/
theorem physical_weighted_removable {n N : ℕ} {M : ComplexManifold n}
    (g : SmoothMetric M) {f : ℂ → M.Carrier}
    (hf : MDifferentiableOn 𝓘(ℂ, ℂ) (ComplexModel n) f puncturedUnitDisc)
    {ρ σ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1) (hσ : 0 < σ)
    (henergy : physicalWeightedEnergy g.form f ρ σ < ⊤)
    {F : M.Carrier → ComplexVector N} (hF : IsHolomorphicVecMap F)
    (hinj : Function.Injective F)
    (hbounded : ∃ B : ℝ, ∀ z ∈ puncturedUnitDisc, ‖F (f z)‖ ≤ B) :
    ∃ (θ : ℝ) (p : M.Carrier) (r : ℝ) (fext : ℂ → M.Carrier),
      0 < r ∧ r < 1 ∧ fext 0 = p ∧
      Tendsto (fun s : ℝ ↦ f ((s : ℂ) * Complex.exp (θ * Complex.I))) (𝓝[>] 0) (𝓝 p) ∧
      Tendsto f (𝓝[≠] 0) (𝓝 p) ∧
      ContMDiffOn 𝓘(ℂ, ℂ) (ComplexModel n) ∞ fext (Metric.ball 0 r) ∧
      EqOn fext f {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ < r} := by
  classical
  obtain ⟨θ, p, hradial⟩ := exists_physical_radial_limit g hf hρ hρ1 hσ henergy
  have hd : DifferentiableOn ℂ (F ∘ f) puncturedUnitDisc := by
    intro z hz
    have hm := (hF (f z)).comp z
      (hf.mdifferentiableAt (Yau.Proofs.B01Aux.puncturedUnitDisc_isOpen.mem_nhds hz))
    exact hm.differentiableAt.differentiableWithinAt
  letI := L12Aux.inducedMetricSpace g
  letI := L12Aux.inducedMetricSpace_proper g
  obtain ⟨B, hB⟩ := hbounded
  have hlim : Tendsto f (𝓝[≠] (0 : ℂ)) (𝓝 p) :=
    tendsto_of_bounded_holomorphic_ambient_and_radial (by norm_num : (0 : ℝ) < 1)
      hf.continuousOn hF.continuous hinj hd hB θ hradial
  refine ⟨θ, p, 1 / 2, Function.update f 0 p, by norm_num, by norm_num,
    by simp, hradial, hlim, ?_, ?_⟩
  · exact (contMDiff_update_of_punctured_tendsto hf hlim).mono (Metric.ball_subset_ball (by norm_num))
  · intro z hz
    exact Function.update_of_ne (norm_pos_iff.mp hz.1) _ _

/-- The literal product-of-densities input is the same original weighted
physical integral; no finite-speed or radial-limit assumption is added. -/
theorem physical_weighted_removable_lintegral {n N : ℕ} {M : ComplexManifold n}
    (g : SmoothMetric M) {f : ℂ → M.Carrier}
    (hf : MDifferentiableOn 𝓘(ℂ, ℂ) (ComplexModel n) f puncturedUnitDisc)
    {ρ σ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1) (hσ : 0 < σ)
    (henergy : (∫⁻ z in {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ < ρ},
      ENNReal.ofReal (hermitianNormSq (g.form (f z)) (physicalCurveDerivative f z)) *
        ENNReal.ofReal (‖z‖ ^ (-σ))) < ⊤)
    {F : M.Carrier → ComplexVector N} (hF : IsHolomorphicVecMap F)
    (hinj : Function.Injective F)
    (hbounded : ∃ B : ℝ, ∀ z ∈ puncturedUnitDisc, ‖F (f z)‖ ≤ B) :
    ∃ (θ : ℝ) (p : M.Carrier) (r : ℝ) (fext : ℂ → M.Carrier),
      0 < r ∧ r < 1 ∧ fext 0 = p ∧
      Tendsto (fun s : ℝ ↦ f ((s : ℂ) * Complex.exp (θ * Complex.I))) (𝓝[>] 0) (𝓝 p) ∧
      Tendsto f (𝓝[≠] 0) (𝓝 p) ∧
      ContMDiffOn 𝓘(ℂ, ℂ) (ComplexModel n) ∞ fext (Metric.ball 0 r) ∧
      EqOn fext f {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ < r} := by
  have heq : physicalWeightedEnergy g.form f ρ σ =
      ∫⁻ z in {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ < ρ},
        ENNReal.ofReal (hermitianNormSq (g.form (f z)) (physicalCurveDerivative f z)) *
          ENNReal.ofReal (‖z‖ ^ (-σ)) := by
    unfold physicalWeightedEnergy
    apply lintegral_congr
    intro z
    exact ENNReal.ofReal_mul (hermitianNormSq_nonneg _ _)
  exact physical_weighted_removable g hf hρ hρ1 hσ (heq.trans_lt henergy) hF hinj hbounded

end Yau.NodeProofs.D02RemovableAux
