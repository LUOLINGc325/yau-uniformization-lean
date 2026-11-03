import Yau.Proofs.F01ACompactInitialCoefficients
import Yau.Proofs.F01ALocalInitialPotential
import Yau.Proofs.F01InitialCylinderRescale
import Yau.LeafProofs.L05

/-! The original initial-surface producer applied in one fixed original
holomorphic chart. Its constants are chosen before the approximation
index, using the local clock cap and local transformed matrix range. -/
noncomputable section
open Set Metric
open scoped ContDiff Manifold Matrix ComplexOrder Matrix.Norms.Frobenius
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic Yau.ParabolicCandidates Yau.LeafProofs.L17Aux
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {M : ComplexManifold n}

theorem fixed_original_chart_initial_schauder
    (hn : 0 < n) (g : HermitianField M) (hg : MetricSmooth g)
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (he : MDifferentiableOn (ComplexModel n) (ComplexModel n) e e.source)
    (hei : MDifferentiableOn (ComplexModel n) (ComplexModel n) e.symm e.target)
    {r α β ell upper Mclock : ℝ} (hball : closedBall 0 r ⊆ e.source)
    (hα : 0 < α) (hα1 : α < 1) (hβ : 0 < β) (hβ1 : β < 1)
    (hell : 0 < ell) (hUpper : ell ≤ upper) (hM : 0 ≤ Mclock) :
    ∃ Ci : ℝ, 0 < Ci ∧ ∀ (F : Point n → ℝ) (T ρ : ℝ),
      0 < ρ → 2 * ρ ≤ r → 2 * ρ ≤ 1 → (2 * ρ) ^ 2 ≤ T →
      ContDiffOn ℝ ∞ F (ball 0 r ×ˢ Icc 0 T) →
      (∀ x ∈ ball 0 r, F (x,0) = 0) →
      (∀ x ∈ ball 0 r, ∀ t ∈ Icc 0 T, HasDerivWithinAt (fun s => F (x,s))
        (localNativePotentialClock (pullbackMatrix g e) F (x,t)) (Icc 0 T) t) →
      (∀ p ∈ ball 0 r ×ˢ Icc 0 T, |localNativePotentialClock (pullbackMatrix g e) F p| ≤ Mclock) →
      (∀ p ∈ ball 0 r ×ˢ Icc 0 T,
        (localNativePotentialMatrix (pullbackMatrix g e) F p - (ell : ℂ) • 1).PosSemidef ∧
        ((upper : ℂ) • 1 - localNativePotentialMatrix (pullbackMatrix g e) F p).PosSemidef) →
      SchauderBound (min α β) (cylinder (ball 0 1) (-1) 1)
        (forwardZeroSpaceTime (parabolicRescalePotential ρ F)) Ci := by
  obtain ⟨K, hK, hCoefficients⟩ := fixed_original_chart_initial_holder_budgets
    g hg e he hei hball hα1.le hβ1.le
  obtain ⟨Ci, hCi, hEstimate⟩ := (Yau.LeafProofs.L05).2.2 n hn α β ell upper K Mclock
    hα hα1 hβ hβ1 hell hUpper hK hM
  obtain ⟨hG, _, hq⟩ := original_chart_background_smooth g hg e he hei
  refine ⟨4 * Ci, by positivity, ?_⟩
  intro F T ρ hρ hρr hρ1 hρT hF hF0 hPDE hClock hRange
  let G : Space n → Matrix (Fin n) (Fin n) ℂ := pullbackMatrix g e
  have hScale : 0 < 2 * ρ := by positivity
  have hqBall : ContDiffOn ℝ ∞ (fun z => Real.log (G z).det.re) (ball 0 r) :=
    hq.mono (ball_subset_closedBall.trans hball)
  obtain ⟨hC2, hSup, hZero, hTransformed, hEquation⟩ :=
    normalized_local_initial_inputs G F hScale hρr hρT hM hell hF hF0 hqBall hPDE hClock hRange
  have hMap {z : Space n} (hz : z ∈ ball 0 1) : (2 * ρ) • z ∈ e.source :=
    hball (ball_subset_closedBall (spatialDilation_mem_ball hScale hρr hz))
  have hGs : ContDiffOn ℝ ∞ (fun z => G ((2 * ρ) • z)) (ball 0 1) :=
    hG.comp (by fun_prop) (fun z hz => hMap hz)
  have hGpos (z : Space n) (hz : z ∈ ball 0 1) : (G ((2 * ρ) • z)).PosDef :=
    pullbackMatrix_posDef g e he hei (hMap hz)
  have hHolder := hCoefficients (2 * ρ) hScale hρr hρ1
  have hBound := hEstimate (fun z => G ((2 * ρ) • z))
    (forwardZeroSpaceTime (parabolicRescalePotential (2 * ρ) F))
    hGs hGpos hHolder.1 hHolder.2 hC2 hSup hZero hTransformed hEquation
  exact normalized_initial_half_scale_schauder hρ.ne' F (le_min hα.le hβ.le) hBound

end Yau.NodeProofs.F01Aux
