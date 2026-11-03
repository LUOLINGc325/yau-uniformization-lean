import Yau.Proofs.P04CutoffCorrection
import Yau.Proofs.P04CanonicalAE
import Yau.Proofs.P04SingularChartNorm

noncomputable section
open Set Filter MeasureTheory Bundle
open scoped Topology Manifold ContDiff ENNReal

namespace Yau.Proofs.P04Aux
open Yau Yau.LeafProofs BundleDbar
variable {n : ℕ} {M : ComplexManifold n}

/-- A single genuine correction with uniform regularized bounds produces a
nonzero canonical section. The exact pole exponent is 2(n+1). -/
theorem canonical_nonzero_of_uniform_correction (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (p : M.Carrier)
    {χ : ComplexVector n → ℝ} (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hs : tsupport χ ⊆ chartTarget p) {ρ : ℝ} (hρ : 0 < ρ)
    (hball : Metric.ball (chartPt p p) ρ ⊆ chartTarget p)
    (hone : ∀ z ∈ Metric.closedBall (chartPt p p) ρ, χ z=1)
    (k : ℝ) {ψ : M.Carrier → ℝ} (hψ : SmoothFn ψ)
    (u : NQForm (CanonicalCoefficients M) 0)
    (hu : WeightedL2 (r := 1) (CanonicalCoefficients M) g.form flatMetric μ (fun x => k*ψ x) u)
    (hd : WeakDbar (r := 1) (CanonicalCoefficients M) u (cutoffDbar p χ))
    (B : ℝ≥0∞) (hB : B < ⊤)
    (hbound : ∀ j : ℕ, weightedNormSq (r := 1) (CanonicalCoefficients M) g.form flatMetric μ
      (regularizedPoleWeight p χ ((n : ℝ)+1) k ψ (poleEpsilon ρ j)) u ≤ B) :
    ∃ S : CanonicalSection M, IsHolomorphicCanonical S ∧ S p ≠ 0 ∧
      (∫⁻ x, ENNReal.ofReal (canonicalNormSq g.form S x*Real.exp (-(k*ψ x))) ∂μ) < ⊤ := by
  have hΦ : SmoothFn (fun x => k*ψ x) := fun a => contDiffOn_const.mul (hψ a)
  obtain ⟨S,hS,hae,hfinite⟩ := canonical_cutoff_correction_holomorphic g μ hμ
    (fun x => k*ψ x) hΦ p hχ hcχ hs u hu hd
  refine ⟨S,hS,?_,hfinite⟩
  let b : ComplexVector n → ℂ := fun z => (χ z : ℂ)-canonicalCoeff S p z
  have hcae := canonical_coefficients_ae g μ hμ u (cutoffTop p χ-canonicalToTop S) hae p
  have hbAE : (fun z => coefficients (r := 1) (CanonicalCoefficients M) u p z Fin.elim0 0)
      =ᵐ[(lebesgueC n).restrict (chartTarget p)] b := by
    filter_upwards [hcae,ae_restrict_mem (isOpen_extChartAt_target p).measurableSet] with z hz hzs
    exact hz.trans (by rw [canonical_coefficients_sub,cutoffTop_coefficient p hzs,
      coefficient_canonicalToTop])
  have hbBall := ae_restrict_of_ae_restrict_of_subset hball hbAE
  have hsing := singular_chart_norm_of_regularized_bounds g μ hμ p hχ hcχ hs hρ hball hone
    (by positivity : 0 < (n : ℝ)+1) k hψ u hu.1 B hbound
  have hbsing : (∫⁻ z in Metric.ball (chartPt p p) ρ, ENNReal.ofReal
      (‖b z‖^2*Real.exp (-(k*inChart p ψ z))*‖z-chartPt p p‖^(-2*((n : ℝ)+1))) ∂lebesgueC n) < ⊤ := by
    have heq : (∫⁻ z in Metric.ball (chartPt p p) ρ, ENNReal.ofReal
        (‖b z‖^2*Real.exp (-(k*inChart p ψ z))*‖z-chartPt p p‖^(-2*((n : ℝ)+1))) ∂lebesgueC n) =
        (∫⁻ z in Metric.ball (chartPt p p) ρ, ENNReal.ofReal
        (‖coefficients (r := 1) (CanonicalCoefficients M) u p z Fin.elim0 0‖^2*
          Real.exp (-(k*inChart p ψ z))*‖z-chartPt p p‖^(-2*((n : ℝ)+1))) ∂lebesgueC n) := by
      apply lintegral_congr_ae
      exact hbBall.mono (fun z hz => by dsimp only at hz ⊢; rw [hz])
    rw [heq]
    exact hsing.trans_lt hB
  have hp : chartPt p p ∈ chartTarget p := mem_extChartAt_target p
  have hbcont : ContinuousAt b (chartPt p p) :=
    (Complex.continuous_ofReal.continuousAt.comp hχ.continuous.continuousAt).sub
      ((hS p).continuousOn.continuousAt ((isOpen_extChartAt_target p).mem_nhds hp))
  have hΦcont : ContinuousAt (fun z => k*inChart p ψ z) (chartPt p p) :=
    continuousAt_const.mul ((hψ p).continuousOn.continuousAt
      ((isOpen_extChartAt_target p).mem_nhds hp))
  have hbzero := pole_weight_forces_value_zero (L12Aux.manifold_dimension_pos M) (chartPt p p)
    hρ b (fun z => k*inChart p ψ z) hbcont hΦcont hbsing
  apply canonical_ne_zero_of_coefficient_one S p
  change (χ (chartPt p p) : ℂ)-canonicalCoeff S p (chartPt p p)=0 at hbzero
  rw [hone _ (Metric.mem_closedBall_self hρ.le),Complex.ofReal_one] at hbzero
  exact (sub_eq_zero.mp hbzero).symm

end Yau.Proofs.P04Aux
