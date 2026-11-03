import Yau.Proofs.D02DiscMorrey
import Yau.Proofs.D02PotentialExponential
import Yau.Proofs.D02DiscDerivativeBounds

/-! Uniform local Hölder bounds outside the actual large atoms are
derived from the original disc family and its constructed Riesz limit. -/

open scoped Topology ContDiff ENNReal CompactlySupported
open MeasureTheory Filter Set Metric

noncomputable section
namespace Yau.NodeProofs.D02Aux
open Yau Yau.Blueprint

theorem local_uniform_disc_morrey {n N : ℕ} (X : KahlerManifold n)
    {F : Pt X → ComplexVector N} (hF : IsHolomorphicVecMap F) (hImm : IsImmersionMap F)
    {K : Set (Pt X)} (hK : IsCompact K) (fs : ℕ → ℂ → Pt X)
    (hfs : ∀ j, IsHolomorphicDisc (fs j) ∧ (∀ z : ℂ, ‖z‖ = 1 → fs j z ∈ K))
    (u : ℂ → ℝ) (μ : Measure ℂ)
    (hlocal : ∀ S : Set ℂ, IsCompact S → S ⊆ ball (0 : ℂ) 1 →
      IntegrableOn u S volume ∧ Tendsto
        (fun j => ∫ z in S, |immersionPotential X.metric.form F (fs j z) - u z|) atTop (𝓝 0))
    (hμ : ∀ S : Set ℂ, IsCompact S → S ⊆ ball (0 : ℂ) 1 → μ S < ⊤)
    (hvague : ∀ χ : C_c(ℂ, ℝ), tsupport χ ⊆ ball (0 : ℂ) 1 →
      Tendsto (fun j => ∫ z, χ z ∂D02RieszAux.smoothRieszOn (ball (0 : ℂ) 1)
        (fun w => immersionPotential X.metric.form F (fs j w))) atTop (𝓝 (∫ z, χ z ∂μ)))
    {z₀ : ℂ} (hz : z₀ ∈ ball (0 : ℂ) 1) (hatom : μ {z₀} < 1) :
    ∃ r H : ℝ, 0 < r ∧ closedBall z₀ (2 * r) ⊆ ball (0 : ℂ) 1 ∧ 0 ≤ H ∧
      ∀ j z, z ∈ ball z₀ r → ∀ w, w ∈ ball z₀ r →
        lengthDist X.metric.form (fs j z) (fs j w) ≤ H * ‖z - w‖ ^ (1 / 3 : ℝ) := by
  obtain ⟨R, C, hR, hRU, hC, hExp⟩ := local_uniform_exp_of_riesz_limit isOpen_ball
    (fun j z => immersionPotential X.metric.form F (fs j z)) u μ
    (fun j => immersionPotential_disc_contDiffOn X hF hImm (hfs j).1)
    (fun j z hz => immersionPotential_disc_laplacian_nonneg X hF hImm (hfs j).1 hz)
    hlocal hμ hvague hz hatom
  obtain ⟨_, B, _, _, _, _, hconst⟩ := uniformImmersionConstants X hF hImm hK
  obtain ⟨D₀, hD₀, hderiv⟩ := uniform_immersionDisc_derivative X hF hK
  have hn : ‖z₀‖ < 1 := by simpa only [mem_ball, dist_zero_right] using hz
  let r : ℝ := min (R / 4) ((1 - ‖z₀‖) / 8)
  let ρ : ℝ := (1 + ‖z₀‖) / 2
  have hr : 0 < r := lt_min (by positivity) (by positivity)
  have hrR : 2 * r ≤ R := by linarith [min_le_left (R / 4) ((1 - ‖z₀‖) / 8)]
  have hsmall : closedBall z₀ (2 * r) ⊆ ball (0 : ℂ) 1 :=
    (closedBall_subset_closedBall hrR).trans hRU
  have hρ : ρ < 1 := by dsimp [ρ]; linarith
  have hnorm : ∀ z ∈ ball z₀ (2 * r), ‖z‖ ≤ ρ := by
    intro z hz
    have hdist : ‖z - z₀‖ < 2 * r := by simpa only [mem_ball, dist_eq_norm] using hz
    have htri : ‖z‖ ≤ ‖z - z₀‖ + ‖z₀‖ := by
      simpa only [sub_add_cancel] using norm_add_le (z - z₀) z₀
    have hmin := min_le_right (R / 4) ((1 - ‖z₀‖) / 8)
    change r ≤ (1 - ‖z₀‖) / 8 at hmin
    dsimp [ρ]
    linarith
  have hExpsmall : ∀ j, IntegrableOn
      (fun z => Real.exp (-((3 : ℝ) / 2) * immersionPotential X.metric.form F (fs j z)))
      (ball z₀ (2 * r)) volume ∧
      (∫ z in ball z₀ (2 * r), Real.exp (-((3 : ℝ) / 2) * immersionPotential X.metric.form F (fs j z))) ≤ C := by
    intro j
    have hsub : ball z₀ (2 * r) ⊆ ball z₀ R := ball_subset_ball hrR
    exact ⟨(hExp j).1.mono_set hsub,
      (setIntegral_mono_set (hExp j).1 (Eventually.of_forall fun z => (Real.exp_pos _).le)
        hsub.eventuallyLE).trans (hExp j).2⟩
  obtain ⟨H, hH, hHolder⟩ := uniform_disc_morrey_of_exp_bound X.metric hF hImm fs
    (fun j => (hfs j).1) z₀ r hr hsmall B (D₀ / (1 - ρ)) C
    (div_nonneg hD₀.le (by linarith)) hC
    (fun j z hz => (hconst (fs j) (hfs j).1 (hfs j).2 z ((hnorm z hz).trans hρ.le)).2.1)
    (fun j z hz => hderiv ρ hρ (fs j) (hfs j).1 (hfs j).2 z (hnorm z hz)) hExpsmall
  exact ⟨r, H, hr, hsmall, hH, hHolder⟩

end Yau.NodeProofs.D02Aux
