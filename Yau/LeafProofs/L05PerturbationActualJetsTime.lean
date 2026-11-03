import Yau.LeafProofs.L05PerturbationActualJetsRemainder
import Yau.LeafProofs.L05PerturbationPolynomials
import Mathlib.Analysis.Calculus.Deriv.Slope

open Filter Asymptotics Set Metric
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency.types false

namespace Yau.LeafProofs.L05Aux
open Yau.Parabolic

/-- The genuinely causal difference quotient identifies the original terminal within derivative. -/
theorem perturb_actual_time_identification {n : ℕ} {u : Point n → ℝ}
    (hu : C2 (backward 1) u) {eta E r0 c q : ℝ}
    (heta : 0 < eta) (hr0 : 0 < r0) (b : Space n →L[ℝ] ℝ) (A : Sym n)
    (hc : c = u (0, 0))
    (herr : ∀ r : ℝ, 0 < r → r ≤ r0 →
      ∀ p ∈ perturbClosed (0 : Space n) r 0,
        |u p - perturbPolynomial c b A q p| ≤ E * r ^ (2 + eta)) :
    q = timeD (backward 1) u (0, 0) := by
  have h0 : ((0, 0) : Point n) ∈ backward 1 := by norm_num [backward]
  have hD := (hu.2.2.2.2.2 (0, 0) h0).hasDerivWithinAt
  have hfiber : {t : ℝ | ((0 : Space n), t) ∈ backward 1} = Ioc (-1) 0 := by
    ext t
    simp [backward]
  change HasDerivWithinAt (fun t => u (0, t)) (timeD (backward 1) u (0, 0))
    {t : ℝ | ((0 : Space n), t) ∈ backward 1} 0 at hD
  rw [hfiber] at hD
  have hrsmall : ∀ᶠ r : ℝ in 𝓝[>] 0, 0 < r ∧ r < 1 ∧ r ≤ r0 := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds,
      (eventually_lt_nhds hr0).filter_mono nhdsWithin_le_nhds] with r hr h1 hR
    exact ⟨hr, h1, hR.le⟩
  have ht : Tendsto (fun r : ℝ => -(r ^ 2)) (𝓝[>] 0) (𝓝[Ioc (-1) 0 \ {0}] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, ?_⟩
    · have hc : Continuous (fun r : ℝ => -(r ^ 2)) := by fun_prop
      simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
    · filter_upwards [hrsmall] with r hr
      refine ⟨⟨by nlinarith [hr.1], by nlinarith [sq_nonneg r]⟩, ?_⟩
      simp only [mem_singleton_iff]
      nlinarith [sq_pos_of_pos hr.1]
  let F : ℝ → ℝ := fun r => (u (0, -(r ^ 2)) - c) / (-(r ^ 2))
  have hactual : Tendsto F (𝓝[>] 0) (𝓝 (timeD (backward 1) u (0, 0))) := by
    have hs := (hasDerivWithinAt_iff_tendsto_slope.mp hD).comp ht
    simpa only [Function.comp_def, slope_def_field, sub_zero, ← hc] using hs
  have herror : ∀ᶠ r : ℝ in 𝓝[>] 0, ‖F r - q‖ ≤ E * r ^ eta := by
    filter_upwards [hrsmall] with r hr
    have hr2 : r ^ 2 ≠ 0 := pow_ne_zero 2 hr.1.ne'
    have hp : ((0 : Space n), -(r ^ 2)) ∈ perturbClosed (0 : Space n) r 0 := by
      refine ⟨mem_closedBall_self hr.1.le, by dsimp; linarith, by nlinarith [sq_nonneg r]⟩
    have hbnd := herr r hr.1 hr.2.2 (0, -(r ^ 2)) hp
    have hpoly : perturbPolynomial c b A q ((0 : Space n), -(r ^ 2)) = c - q * r ^ 2 := by
      simp [perturbPolynomial, perturbQuad_eq_bilinear, sub_eq_add_neg]
    rw [hpoly] at hbnd
    have heq : F r - q = (u (0, -(r ^ 2)) - (c - q * r ^ 2)) / (-(r ^ 2)) := by
      dsimp [F]
      field_simp [hr.1.ne']
      ring
    rw [heq, Real.norm_eq_abs, abs_div, abs_neg, abs_of_nonneg (sq_nonneg r)]
    apply (div_le_iff₀ (sq_pos_of_pos hr.1)).mpr
    calc
      _ ≤ E * r ^ (2 + eta) := hbnd
      _ = _ := by rw [Real.rpow_add hr.1, Real.rpow_two]; ring
  have hlim : Tendsto (fun r : ℝ => E * r ^ eta) (𝓝[>] 0) (𝓝 0) := by
    have hp := ((tendsto_id : Tendsto (fun r : ℝ => r) (𝓝 (0 : ℝ)) (𝓝 0)).rpow_const
      (Or.inr heta.le)).const_mul E
    simpa [Real.zero_rpow heta.ne'] using hp.mono_left nhdsWithin_le_nhds
  have happrox : Tendsto F (𝓝[>] 0) (𝓝 q) := by
    have h := (squeeze_zero_norm' herror hlim).add_const q
    simpa only [sub_add_cancel, zero_add] using h
  exact tendsto_nhds_unique happrox hactual

end Yau.LeafProofs.L05Aux
