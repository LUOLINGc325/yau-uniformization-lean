import Yau.Proofs.D02PunctureD03
import Yau.Proofs.D02Removable

/-! Original D03 and the actual removable construction produce a temporary
holomorphic extension at each original concentration point. Its value is
the same radial limit supplied by the physical energy argument. -/

open scoped Topology Manifold ContDiff ENNReal
open MeasureTheory Filter Metric Set

noncomputable section
namespace Yau.NodeProofs.D02Aux
open Yau Yau.Blueprint

theorem regular_limit_local_extension {n N : ℕ} (X : KahlerManifold n)
    {F : Pt X → ComplexVector N} (hF : IsHolomorphicVecMap F) (hImm : IsImmersionMap F)
    (hinj : Function.Injective F) (f : ℂ → Pt X) (μ : Measure ℂ)
    (hμ : ∀ K : Set ℂ, IsCompact K → K ⊆ ball (0 : ℂ) 1 → μ K < ⊤)
    (hf : ContMDiffOn 𝓘(ℂ, ℂ) (ComplexModel n) ∞ f (regularPotentialDomain (ball (0 : ℂ) 1) μ))
    (B_F B_u : ℝ) (hBu : 0 ≤ B_u)
    (hbound : ∀ z ∈ regularPotentialDomain (ball (0 : ℂ) 1) μ,
      ‖F (f z)‖ ≤ B_F ∧ immersionDifferentialNormSq X.metric.form F (f z) ≤ B_u)
    (henergy : (∫⁻ z in regularPotentialDomain (ball (0 : ℂ) 1) μ,
      ENNReal.ofReal (hermitianNormSq (X.metric.form (f z)) (physicalCurveDerivative f z))) < ⊤)
    {z₀ : ℂ} (hz : z₀ ∈ ball (0 : ℂ) 1) :
    ∃ (s : ℝ) (p : Pt X) (fext : ℂ → Pt X), 0 < s ∧ ball z₀ s ⊆ ball (0 : ℂ) 1 ∧ fext z₀ = p ∧
      ContMDiffOn 𝓘(ℂ, ℂ) (ComplexModel n) ∞ fext (ball z₀ s) ∧
      EqOn fext f {z : ℂ | 0 < ‖z - z₀‖ ∧ ‖z - z₀‖ < s} := by
  obtain ⟨R, ρ, σ, hR, hRD, _, hcurve, hFbound, hρ, hρ1, hσ, hExtra⟩ :=
    regular_limit_puncture_extraIntegrability X hF hImm f μ hμ hf B_F B_u hBu hbound henergy hz
  obtain ⟨θ, p, r, h, hr, hr1, hp, _, _, hh, heq⟩ := D02RemovableAux.physical_weighted_removable
    X.metric (hcurve.mdifferentiableOn (by simp)) hρ hρ1 hσ hExtra hF hinj ⟨B_F, hFbound⟩
  let α : ℂ → ℂ := fun w => (w - z₀) / (R : ℂ)
  let fext : ℂ → Pt X := h ∘ α
  have hR0 : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  have hα : ContDiff ℂ ∞ α := by dsimp [α]; fun_prop
  have hnorm (w : ℂ) : ‖α w‖ = ‖w - z₀‖ / R := by
    dsimp [α]
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
  have hmap : MapsTo α (ball z₀ (R * r)) (ball (0 : ℂ) r) := by
    intro w hw
    rw [mem_ball, dist_zero_right, hnorm, div_lt_iff₀ hR]
    have hw' : ‖w - z₀‖ < R * r := by simpa only [mem_ball, dist_eq_norm] using hw
    simpa only [mul_comm] using hw'
  have hsmall : ball z₀ (R * r) ⊆ ball (0 : ℂ) 1 :=
    (ball_subset_closedBall.trans (closedBall_subset_closedBall (by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hr1.le hR.le))).trans hRD
  refine ⟨R * r, p, fext, mul_pos hR hr, hsmall, ?_, hh.comp hα.contMDiff.contMDiffOn hmap, ?_⟩
  · simpa only [fext, Function.comp_apply, α, sub_self, zero_div] using hp
  · intro w hw
    have hwα : 0 < ‖α w‖ ∧ ‖α w‖ < r := by
      rw [hnorm]
      exact ⟨div_pos hw.1 hR, (div_lt_iff₀ hR).mpr (by simpa only [mul_comm] using hw.2)⟩
    have hi : z₀ + (R : ℂ) * α w = w := by dsimp [α]; field_simp [hR0] <;> ring
    have hhEq := heq hwα
    simpa only [fext, Function.comp_apply, rescaledCurve, hi] using hhEq

end Yau.NodeProofs.D02Aux
