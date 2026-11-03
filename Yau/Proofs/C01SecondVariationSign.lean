import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Tactic

/-! A genuine C2 energy minimum has nonnegative second variation.
The proof uses the actual derivative limit and the mean value theorem. -/

noncomputable section
open Filter Set
open scoped Topology

namespace Yau.NodeProofs.C01Aux

theorem second_derivative_nonneg_of_localMin
    (f : ℝ → ℝ) (hf : ContDiffAt ℝ 2 f 0) (hmin : IsLocalMin f 0) :
    0 ≤ deriv (deriv f) 0 := by
  by_contra hfail
  have hneg : deriv (deriv f) 0 < 0 := lt_of_not_ge hfail
  have hd : HasDerivAt (deriv f) (deriv (deriv f) 0) 0 :=
    ((hf.derivWithin (m := 1) (by norm_num)).differentiableAt_one).hasDerivAt
  have hzero : deriv f 0 = 0 := hmin.deriv_eq_zero
  have hlim : Tendsto (fun u : ℝ => deriv f u / u) (𝓝[>] 0) (𝓝 (deriv (deriv f) 0)) := by
    simpa only [zero_add, hzero, sub_zero, smul_eq_mul, div_eq_inv_mul] using hd.tendsto_slope_zero_right
  have hslope : ∀ᶠ u in 𝓝[>] (0 : ℝ), deriv f u / u < 0 :=
    hlim.eventually (Iio_mem_nhds hneg)
  obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhdsWithin_iff.mp hslope
  have hreg : ∀ᶠ u in 𝓝 (0 : ℝ), ContinuousAt f u :=
    (hf.eventually (by norm_num)).mono (fun u hu => hu.continuousAt)
  have hboth : ∀ᶠ u in 𝓝 (0 : ℝ), ContinuousAt f u ∧ f 0 ≤ f u := hreg.and hmin
  obtain ⟨ρ, hρ, hρsub⟩ := Metric.mem_nhds_iff.mp hboth
  let δ := min r ρ / 2
  have hδ : 0 < δ := half_pos (lt_min hr hρ)
  have hδr : δ < r := by dsimp only [δ]; linarith [min_le_left r ρ]
  have hδρ : δ < ρ := by dsimp only [δ]; linarith [min_le_right r ρ]
  have hballρ (u : ℝ) (hu : u ∈ Icc (0 : ℝ) δ) : u ∈ Metric.ball 0 ρ := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg hu.1]
    exact hu.2.trans_lt hδρ
  have hcont : ContinuousOn f (Icc (0 : ℝ) δ) :=
    fun u hu => (hρsub (hballρ u hu)).1.continuousWithinAt
  have hderiv (u : ℝ) (hu : u ∈ interior (Icc (0 : ℝ) δ)) : deriv f u < 0 := by
    rw [interior_Icc] at hu
    have huball : u ∈ Metric.ball 0 r := by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hu.1]
      exact hu.2.trans hδr
    have H := hrsub ⟨huball, hu.1⟩
    have H' := mul_lt_mul_of_pos_right H hu.1
    rwa [div_mul_cancel₀ _ hu.1.ne', zero_mul] at H'
  have hanti := strictAntiOn_of_deriv_neg (convex_Icc (0 : ℝ) δ) hcont hderiv
  have hstrict : f δ < f 0 := hanti ⟨le_rfl, hδ.le⟩ ⟨hδ.le, le_rfl⟩ hδ
  exact (not_lt_of_ge (hρsub (hballρ δ ⟨hδ.le, le_rfl⟩)).2) hstrict

end Yau.NodeProofs.C01Aux
