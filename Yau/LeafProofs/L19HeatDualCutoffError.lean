import Yau.LeafProofs.L19HeatDualErrorAlgebra

/-! The actual cutoff duality error tends to zero, with derived growth only. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold Matrix ComplexOrder
namespace Yau.LeafProofs.L19Aux
open L12Aux L18Aux
variable {n : ℕ} {M : ComplexManifold n} {I : Set ℝ}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2200000

theorem scalarHeat_annular_scalar_time_bound (hI : IsOpen I)
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    {u : M.Carrier → ℝ → ℝ} (hu : SmoothSpaceTime u I)
    (o : M.Carrier) {R s T B : ℝ} (hR : 0 ≤ R) (hslab : Icc s T ⊆ I) (hsT : s ≤ T)
    (hL2 : ∀ t ∈ Icc s T, (∫ x in
      {x | R / 2 ≤ inducedDistance g.form o x ∧ inducedDistance g.form o x ≤ 4 * R}, u x t ^ 2 ∂μ) ≤ B) :
    (∫ t in s..T, ∫ x in {x | R ≤ inducedDistance g.form o x ∧ inducedDistance g.form o x ≤ 2 * R},
      u x t ^ 2 ∂μ) ≤ (T - s) * B := by
  have hreg := LocalTime.scalarHeat_annular_integrable hI g μ hμ hu o R (2 * R) hslab hsT
  have hh := intervalIntegral.integral_mono_on hsT hreg.2.1
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => B) volume s T) (fun t ht =>
      (integral_sq_annulus_le_expanded g μ hμ o hR (smoothSpaceTime_slice hu (hslab ht))).trans (hL2 t ht))
  simpa only [intervalIntegral.integral_const, smul_eq_mul] using hh

/-- For every original positive heat solution, a genuine backward heat
test with a Gaussian tail has a vanishing annular duality error.  The
original solution's growth bounds are proved internally from Li--Yau. -/
theorem positiveHeatSolution_gaussian_test_cutoff_error
    (g : SmoothMetric M) (hcomplete : IsComplete g) (hK : IsKahler g)
    (hRic : ∀ x, (ricci g.form x).PosSemidef) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) {u v : M.Carrier → ℝ → ℝ}
    (hu : LeafCandidates.PositiveHeatSolution g.form u) (hI : IsOpen I) (hIpos : I ⊆ Ioi 0)
    (hv : SmoothSpaceTime v I)
    (hbackward : ∀ x t, t ∈ I → HasDerivAt (v x) (-laplacian g.form (fun y => v y t) x) t)
    (o : M.Carrier) {s T C β : ℝ} (hs : 0 < s) (hslab : Icc s T ⊆ I) (hsT : s ≤ T)
    (hC : 0 < C) (hβ : 0 < β)
    (hdecay : ∀ x t, t ∈ Icc s T → |v x t| ≤ C * Real.exp (-β * inducedDistance g.form o x ^ 2))
    (A : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ R : ℝ, 1 ≤ R → ∀ η : M.Carrier → ℝ,
      SmoothFn η → HasCompactSupport η →
      (∀ x, inducedDistance g.form o x ≤ R → η x = 1) →
      tsupport η ⊆ distBall g.form o (2 * R) →
      (∀ x, scalarGradientPair g.form η η x ≤ A ^ 2) →
      |(∫ x, η x * u x T * v x T ∂μ) - (∫ x, η x * u x s * v x s ∂μ)| ≤
        K * Real.exp (-(β / 16) * R ^ 2) := by
  have huI : SmoothSpaceTime u I := fun a => (hu.1 a).mono (fun p hp => ⟨hp.1, hIpos hp.2⟩)
  have hforward : ∀ x t, t ∈ I → HasDerivAt (u x) (laplacian g.form (fun y => u y t) x) t :=
    fun x t ht => positiveHeatSolution_hasDerivAt g.form hu x (hIpos ht)
  obtain ⟨D, E, hD, hE, hUgrowth⟩ := positiveHeatSolution_annular_gaussian_energy_growth
    g hcomplete hK hRic μ hμ hu o hs hsT (show 0 < β / 16 by positivity)
  obtain ⟨F, G, hF, hG, hVdecay⟩ := scalarHeat_annular_gaussian_energy_decay
    g hK hRic μ hμ hI hv (Or.inr hbackward) o hslab hsT hC hβ hdecay
  have hTs : 0 ≤ T - s := sub_nonneg.mpr hsT
  let K := (1 / 2 : ℝ) * ((T - s) * D + A ^ 2 / 4 * E + ((T - s) * F + A ^ 2 / 4 * G))
  refine ⟨K, by dsimp only [K]; positivity, ?_⟩
  intro R hR η hη hcη hone hsupp hηE
  have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one hR
  obtain ⟨hU, hGU⟩ := hUgrowth R hR
  obtain ⟨hV, hGV⟩ := hVdecay R hR
  have hUt := scalarHeat_annular_scalar_time_bound hI g μ hμ huI o hR0.le hslab hsT hU
  have hVt := scalarHeat_annular_scalar_time_bound hI g μ hμ hv o hR0.le hslab hsT hV
  have hUt' : (∫ t in s..T, ∫ x in
      {x | R ≤ inducedDistance g.form o x ∧ inducedDistance g.form o x ≤ 2 * R}, u x t ^ 2 ∂μ) ≤
      ((T - s) * D) * Real.exp ((β / 16) * R ^ 2) := by simpa only [mul_assoc] using hUt
  have hVt' : (∫ t in s..T, ∫ x in
      {x | R ≤ inducedDistance g.form o x ∧ inducedDistance g.form o x ≤ 2 * R}, v x t ^ 2 ∂μ) ≤
      ((T - s) * F) * Real.exp (-(β / 4) * R ^ 2) := by simpa only [mul_assoc] using hVt
  have hbalance := balanced_gaussian_four_energy_bound hβ (sq_nonneg A)
    (mul_nonneg hTs hD) (mul_nonneg hTs hF) hE hG hUt' hVt' hGU hGV
  have herror := scalarHeat_localized_pairing_interval_bound hI g hK μ hμ huI hv
    hforward hbackward hη hcη (scalarHeat_annulus_isCompact g o R (2 * R))
    (fun t _ x hx => ⟨
      scalarGradientPair_radial_cutoff_zero_off_annulus g o (by positivity) hone hsupp _ hx,
      scalarGradientPair_radial_cutoff_zero_off_annulus g o (by positivity) hone hsupp _ hx⟩)
    (sq_nonneg A) (Real.exp_pos (-(β / 8) * R ^ 2)) hηE hslab hsT
  exact herror.trans hbalance

end Yau.LeafProofs.L19Aux
