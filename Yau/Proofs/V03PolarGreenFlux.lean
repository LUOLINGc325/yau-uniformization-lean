import Yau.Proofs.V03PolarGradient
import Yau.Proofs.V03CirclePeriod
import Mathlib.MeasureTheory.Integral.DivergenceTheorem

/-! Native divergence integration for the genuine closed-disc polar
fluxes, including the radial origin and the angular seam. -/

open scoped Topology ContDiff Interval
open MeasureTheory

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

def closedPolarDivergence (u : ℂ → ℝ) (p : ℝ × ℝ) : ℝ :=
  fderivWithin ℝ (polarRadialFlux u) (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ) p (1, 0) +
    fderivWithin ℝ (polarAngularFlux u) (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ) p (0, 1)

theorem closedPolarDivergence_contDiffOn {u : ℂ → ℝ}
    (hu : ContDiffOn ℝ ∞ u (Metric.closedBall (0 : ℂ) 1)) :
    ContDiffOn ℝ ∞ (closedPolarDivergence u) (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ) := by
  have hS : UniqueDiffOn ℝ (Set.Icc (0 : ℝ) 1 ×ˢ (Set.univ : Set ℝ)) :=
    (uniqueDiffOn_Icc (by norm_num : (0 : ℝ) < 1)).prod uniqueDiffOn_univ
  exact (((polarRadialFlux_contDiffOn hu).fderivWithin hS (m := ∞) (by simp)).clm_apply
    contDiffOn_const).add
    (((polarAngularFlux_contDiffOn hu).fderivWithin hS (m := ∞) (by simp)).clm_apply contDiffOn_const)

theorem polarAngularFlux_seam (u : ℂ → ℝ) (r : ℝ) :
    polarAngularFlux u (r, Real.pi) = polarAngularFlux u (r, -Real.pi) := by
  have hp : circlePoint Real.pi = circlePoint (-Real.pi) := by
    have hh := circlePoint_periodic (-Real.pi)
    have he : -Real.pi + 2 * Real.pi = Real.pi := by ring
    simpa only [he] using hh
  simp only [polarAngularFlux, polarDiscPoint, hp]

theorem polarGreen_flux {u : ℂ → ℝ}
    (hu : ContDiffOn ℝ ∞ u (Metric.closedBall (0 : ℂ) 1)) :
    (∫ r in (0 : ℝ)..1, ∫ θ in (-Real.pi)..Real.pi, closedPolarDivergence u (r, θ)) =
      ∫ θ in (-Real.pi)..Real.pi, closedRealGradient u (circlePoint θ) (circlePoint θ) := by
  let S := Set.Icc (0 : ℝ) 1 ×ˢ (Set.univ : Set ℝ)
  have hA := polarRadialFlux_contDiffOn hu
  have hB := polarAngularFlux_contDiffOn hu
  have hsub : Set.uIcc (0 : ℝ) 1 ×ˢ Set.uIcc (-Real.pi) Real.pi ⊆ S := by
    intro p hp
    exact ⟨by simpa only [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hp.1, Set.mem_univ _⟩
  have hnhds (p : ℝ × ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1 ×ˢ Set.Ioo (-Real.pi) Real.pi) :
      S ∈ 𝓝 p :=
    prod_mem_nhds (Icc_mem_nhds hp.1.1 hp.1.2) Filter.univ_mem
  have hdf : ∀ p ∈ Set.Ioo (0 : ℝ) 1 ×ˢ Set.Ioo (-Real.pi) Real.pi,
      HasFDerivAt (polarRadialFlux u) (fderivWithin ℝ (polarRadialFlux u) S p) p := by
    intro p hp
    exact (((hA.differentiableOn (by simp)) p
      ⟨⟨hp.1.1.le, hp.1.2.le⟩, Set.mem_univ _⟩).hasFDerivWithinAt).hasFDerivAt (hnhds p hp)
  have hdg : ∀ p ∈ Set.Ioo (0 : ℝ) 1 ×ˢ Set.Ioo (-Real.pi) Real.pi,
      HasFDerivAt (polarAngularFlux u) (fderivWithin ℝ (polarAngularFlux u) S p) p := by
    intro p hp
    exact (((hB.differentiableOn (by simp)) p
      ⟨⟨hp.1.1.le, hp.1.2.le⟩, Set.mem_univ _⟩).hasFDerivWithinAt).hasFDerivAt (hnhds p hp)
  have hi : IntegrableOn (closedPolarDivergence u)
      (Set.uIcc (0 : ℝ) 1 ×ˢ Set.uIcc (-Real.pi) Real.pi) :=
    ((closedPolarDivergence_contDiffOn hu).continuousOn.mono hsub).integrableOn_compact
      (isCompact_uIcc.prod isCompact_uIcc)
  have hh := integral2_divergence_prod_of_hasFDerivAt (polarRadialFlux u) (polarAngularFlux u)
    (fderivWithin ℝ (polarRadialFlux u) S) (fderivWithin ℝ (polarAngularFlux u) S)
    0 (-Real.pi) 1 Real.pi (hA.continuousOn.mono hsub) (hB.continuousOn.mono hsub)
    (by simpa only [min_eq_left (by norm_num : (0 : ℝ) ≤ 1),
      max_eq_right (by norm_num : (0 : ℝ) ≤ 1), min_eq_left (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi),
      max_eq_right (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi)] using hdf)
    (by simpa only [min_eq_left (by norm_num : (0 : ℝ) ≤ 1),
      max_eq_right (by norm_num : (0 : ℝ) ≤ 1), min_eq_left (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi),
      max_eq_right (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi)] using hdg) hi
  change (∫ r in (0 : ℝ)..1, ∫ θ in (-Real.pi)..Real.pi, closedPolarDivergence u (r, θ)) = _ at hh
  simp_rw [polarAngularFlux_seam] at hh
  simpa only [sub_self, zero_add, polarRadialFlux, polarDiscPoint, Prod.fst, Prod.snd,
    Complex.ofReal_one, Complex.ofReal_zero, one_mul, zero_mul, intervalIntegral.integral_zero, sub_zero] using hh

end Yau.Blueprint.V03Proof
