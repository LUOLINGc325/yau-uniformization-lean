import Yau.LeafProofs.L10DiscEnergyPolar

/-! The disc divergence formula uses a continuous derivative field on the
closed disc and actual derivatives only in its interior. -/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff

namespace Yau.LeafProofs

def discEnergyDivergence (J : ℂ → ℂ →L[ℝ] ℂ) (z : ℂ) : ℝ :=
  (J z 1).re + (J z Complex.I).im

def discEnergyRadialFlux (F : ℂ → ℂ) (r : ℝ) : ℝ :=
  ∫ θ in (-Real.pi)..Real.pi, r * inner ℝ (L08_unitCircle θ) (F (r • L08_unitCircle θ))

theorem discEnergy_polar_mem_closed {r : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) (θ : ℝ) :
    r • L08_unitCircle θ ∈ Metric.closedBall (0 : ℂ) 1 := by
  simpa only [Metric.mem_closedBall, dist_zero_right, norm_smul,
    Real.norm_eq_abs, abs_of_nonneg hr.1, L08_norm_unitCircle, mul_one] using hr.2

theorem discEnergy_polar_mem_ball {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) (θ : ℝ) :
    r • L08_unitCircle θ ∈ Metric.ball (0 : ℂ) 1 := by
  simpa only [Metric.mem_ball, dist_zero_right, norm_smul,
    Real.norm_eq_abs, abs_of_pos hr.1, L08_norm_unitCircle, mul_one] using hr.2

theorem discEnergy_trace_rotation (J : ℂ →L[ℝ] ℂ) (θ : ℝ) :
    inner ℝ (L08_unitCircle θ) (J (L08_unitCircle θ)) +
      inner ℝ (L08_unitCircle θ * Complex.I) (J (L08_unitCircle θ * Complex.I)) =
      (J 1).re + (J Complex.I).im := by
  rw [L08_unitCircle_mul_I_eq, L08_unitCircle_eq]
  simp only [map_add, map_smul, inner_add_left, inner_add_right, real_inner_smul_left,
    real_inner_smul_right]
  have h1 (z : ℂ) : inner ℝ (1 : ℂ) z = z.re := by simp [Complex.inner]
  have hI (z : ℂ) : inner ℝ Complex.I z = z.im := by simp [Complex.inner]
  rw [h1, h1, hI, hI]
  calc
    _ = (Real.cos θ ^ 2 + Real.sin θ ^ 2) * ((J 1).re + (J Complex.I).im) := by ring
    _ = _ := by rw [Real.cos_sq_add_sin_sq]; ring

theorem discEnergyRadialFlux_continuousOn {F : ℂ → ℂ}
    (hF : ContinuousOn F (Metric.closedBall (0 : ℂ) 1)) :
    ContinuousOn (discEnergyRadialFlux F) (Icc (0 : ℝ) 1) := by
  unfold discEnergyRadialFlux
  apply discEnergy_continuousOn_angularIntegral (H := fun p : ℝ × ℝ =>
    p.1 * inner ℝ (L08_unitCircle p.2) (F (p.1 • L08_unitCircle p.2)))
    (neg_le_self Real.pi_pos.le)
  have hp : Continuous (fun p : ℝ × ℝ => p.1 • L08_unitCircle p.2) :=
    continuous_fst.smul (L08_continuous_unitCircle.comp continuous_snd)
  exact continuousOn_fst.mul ((L08_continuous_unitCircle.comp continuous_snd).continuousOn.inner
    (hF.comp hp.continuousOn (fun p hp => discEnergy_polar_mem_closed hp.1 p.2)))

/-- Angular integration turns the tangential derivative into the radial
flux, since the endpoint positions and tangents agree. -/
theorem discEnergy_angular_trace {F : ℂ → ℂ} {J : ℂ → ℂ →L[ℝ] ℂ}
    (hF : ContinuousOn F (Metric.closedBall (0 : ℂ) 1))
    (hJ : ContinuousOn J (Metric.closedBall (0 : ℂ) 1))
    (hD : ∀ z ∈ Metric.ball (0 : ℂ) 1, HasFDerivAt F (J z) z)
    {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) :
    (∫ θ in (-Real.pi)..Real.pi, inner ℝ (L08_unitCircle θ) (F (r • L08_unitCircle θ))) =
      ∫ θ in (-Real.pi)..Real.pi,
        r * inner ℝ (L08_unitCircle θ * Complex.I)
          (J (r • L08_unitCircle θ) (L08_unitCircle θ * Complex.I)) := by
  have hpath : Continuous (fun θ => r • L08_unitCircle θ) :=
    L08_continuous_unitCircle.const_smul r
  have hFc : Continuous (fun θ => F (r • L08_unitCircle θ)) :=
    hF.comp_continuous hpath (fun θ => discEnergy_polar_mem_closed (Ioo_subset_Icc_self hr) θ)
  have hJc : Continuous (fun θ => J (r • L08_unitCircle θ)) :=
    hJ.comp_continuous hpath (fun θ => discEnergy_polar_mem_closed (Ioo_subset_Icc_self hr) θ)
  have hτ : Continuous (fun θ => L08_unitCircle θ * Complex.I) :=
    L08_continuous_unitCircle.mul_const _
  have hderiv (θ : ℝ) : HasDerivAt
      (fun t => inner ℝ (L08_unitCircle t * Complex.I) (F (r • L08_unitCircle t)))
      (r * inner ℝ (L08_unitCircle θ * Complex.I)
        (J (r • L08_unitCircle θ) (L08_unitCircle θ * Complex.I)) -
        inner ℝ (L08_unitCircle θ) (F (r • L08_unitCircle θ))) θ := by
    have h := (L08_hasDerivAt_unitCircle_tangent θ).inner ℝ
      ((hD _ (discEnergy_polar_mem_ball hr θ)).comp_hasDerivAt θ
        ((L08_hasDerivAt_unitCircle θ).const_smul r))
    simpa only [Function.comp_def, Pi.smul_apply, map_smul, real_inner_smul_right, inner_neg_left,
      ← sub_eq_add_neg] using h
  have hN : Continuous (fun θ => inner ℝ (L08_unitCircle θ) (F (r • L08_unitCircle θ))) :=
    L08_continuous_unitCircle.inner hFc
  have hT : Continuous (fun θ => r * inner ℝ (L08_unitCircle θ * Complex.I)
      (J (r • L08_unitCircle θ) (L08_unitCircle θ * Complex.I))) :=
    (hτ.inner (hJc.clm_apply hτ)).const_mul r
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := -Real.pi) (b := Real.pi) (fun θ _ => hderiv θ)
    ((hT.sub hN).intervalIntegrable _ _)
  have he : L08_unitCircle Real.pi = L08_unitCircle (-Real.pi) := by
    simp [L08_unitCircle, Complex.exp_ofReal_mul_I]
  rw [intervalIntegral.integral_sub (hT.intervalIntegrable _ _) (hN.intervalIntegrable _ _),
    he, sub_self] at hFTC
  linarith only [hFTC]

theorem discEnergyRadialFlux_hasDerivAt {F : ℂ → ℂ} {J : ℂ → ℂ →L[ℝ] ℂ}
    (hF : ContinuousOn F (Metric.closedBall (0 : ℂ) 1))
    (hJ : ContinuousOn J (Metric.closedBall (0 : ℂ) 1))
    (hD : ∀ z ∈ Metric.ball (0 : ℂ) 1, HasFDerivAt F (J z) z)
    {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (discEnergyRadialFlux F)
      (∫ θ in (-Real.pi)..Real.pi, r * discEnergyDivergence J (r • L08_unitCircle θ)) r := by
  let H : ℝ × ℝ → ℝ := fun p => p.1 *
    inner ℝ (L08_unitCircle p.2) (F (p.1 • L08_unitCircle p.2))
  let H' : ℝ × ℝ → ℝ := fun p =>
    inner ℝ (L08_unitCircle p.2) (F (p.1 • L08_unitCircle p.2)) +
      p.1 * inner ℝ (L08_unitCircle p.2)
        (J (p.1 • L08_unitCircle p.2) (L08_unitCircle p.2))
  have hp : Continuous (fun p : ℝ × ℝ => p.1 • L08_unitCircle p.2) :=
    continuous_fst.smul (L08_continuous_unitCircle.comp continuous_snd)
  have hFp := hF.comp hp.continuousOn (fun p (hp : p ∈ Icc (0 : ℝ) 1 ×ˢ Icc (-Real.pi) Real.pi) =>
    discEnergy_polar_mem_closed hp.1 p.2)
  have hJp := hJ.comp hp.continuousOn (fun p (hp : p ∈ Icc (0 : ℝ) 1 ×ˢ Icc (-Real.pi) Real.pi) =>
    discEnergy_polar_mem_closed hp.1 p.2)
  have hν : ContinuousOn (fun p : ℝ × ℝ => L08_unitCircle p.2)
      (Icc (0 : ℝ) 1 ×ˢ Icc (-Real.pi) Real.pi) :=
    (L08_continuous_unitCircle.comp continuous_snd).continuousOn
  have hHH : ContinuousOn H (Icc (0 : ℝ) 1 ×ˢ Icc (-Real.pi) Real.pi) :=
    continuousOn_fst.mul (hν.inner hFp)
  have hHH' : ContinuousOn H' (Icc (0 : ℝ) 1 ×ˢ Icc (-Real.pi) Real.pi) :=
    (hν.inner hFp).add (continuousOn_fst.mul (hν.inner (hJp.clm_apply hν)))
  have hderiv : ∀ s ∈ Ioo (0 : ℝ) 1, ∀ θ ∈ Icc (-Real.pi) Real.pi,
      HasDerivAt (fun t => H (t, θ)) (H' (s, θ)) s := by
    intro s hs θ _
    have h := (hasDerivAt_id s).mul ((hasDerivAt_const s (L08_unitCircle θ)).inner ℝ
      ((hD _ (discEnergy_polar_mem_ball hs θ)).comp_hasDerivAt s
        ((hasDerivAt_id s).smul_const (L08_unitCircle θ))))
    convert h using 1 <;> simp only [H, H', Function.comp_def, one_smul, inner_zero_left,
      add_zero, one_mul, id_eq]
    rfl
  have h := discEnergy_hasDerivAt_angularIntegral hHH hHH' hderiv hr
  change HasDerivAt (discEnergyRadialFlux F) _ r at h
  apply h.congr_deriv
  have hpath : Continuous (fun θ => r • L08_unitCircle θ) :=
    L08_continuous_unitCircle.const_smul r
  have hFc : Continuous (fun θ => F (r • L08_unitCircle θ)) :=
    hF.comp_continuous hpath (fun θ => discEnergy_polar_mem_closed (Ioo_subset_Icc_self hr) θ)
  have hJc : Continuous (fun θ => J (r • L08_unitCircle θ)) :=
    hJ.comp_continuous hpath (fun θ => discEnergy_polar_mem_closed (Ioo_subset_Icc_self hr) θ)
  have hτ : Continuous (fun θ => L08_unitCircle θ * Complex.I) :=
    L08_continuous_unitCircle.mul_const _
  have hN : Continuous (fun θ => inner ℝ (L08_unitCircle θ) (F (r • L08_unitCircle θ))) :=
    L08_continuous_unitCircle.inner hFc
  have hR : Continuous (fun θ => r * inner ℝ (L08_unitCircle θ)
      (J (r • L08_unitCircle θ) (L08_unitCircle θ))) :=
    (L08_continuous_unitCircle.inner (hJc.clm_apply L08_continuous_unitCircle)).const_mul r
  have hT : Continuous (fun θ => r * inner ℝ (L08_unitCircle θ * Complex.I)
      (J (r • L08_unitCircle θ) (L08_unitCircle θ * Complex.I))) :=
    (hτ.inner (hJc.clm_apply hτ)).const_mul r
  change (∫ θ in (-Real.pi)..Real.pi,
      inner ℝ (L08_unitCircle θ) (F (r • L08_unitCircle θ)) +
        r * inner ℝ (L08_unitCircle θ) (J (r • L08_unitCircle θ) (L08_unitCircle θ))) = _
  rw [intervalIntegral.integral_add (hN.intervalIntegrable _ _) (hR.intervalIntegrable _ _),
    discEnergy_angular_trace hF hJ hD hr,
    ← intervalIntegral.integral_add (hT.intervalIntegrable _ _) (hR.intervalIntegrable _ _)]
  apply intervalIntegral.integral_congr
  intro θ _
  dsimp only
  rw [← mul_add, add_comm, discEnergy_trace_rotation]
  rfl

/-- A continuous derivative field on the closed disc gives the actual
boundary flux formula without assuming an ambient derivative at the circle. -/
theorem discEnergy_integral_divergence {F : ℂ → ℂ} {J : ℂ → ℂ →L[ℝ] ℂ}
    (hF : ContinuousOn F (Metric.closedBall (0 : ℂ) 1))
    (hJ : ContinuousOn J (Metric.closedBall (0 : ℂ) 1))
    (hD : ∀ z ∈ Metric.ball (0 : ℂ) 1, HasFDerivAt F (J z) z) :
    (∫ z in Metric.ball (0 : ℂ) 1, discEnergyDivergence J z) =
      ∫ θ in (-Real.pi)..Real.pi, inner ℝ (L08_unitCircle θ) (F (L08_unitCircle θ)) := by
  have hdiv : ContinuousOn (discEnergyDivergence J) (Metric.closedBall (0 : ℂ) 1) :=
    (Complex.continuous_re.comp_continuousOn (hJ.clm_apply continuousOn_const)).add
      (Complex.continuous_im.comp_continuousOn (hJ.clm_apply continuousOn_const))
  have hp : Continuous (fun p : ℝ × ℝ => p.1 • L08_unitCircle p.2) :=
    continuous_fst.smul (L08_continuous_unitCircle.comp continuous_snd)
  have hrad : ContinuousOn (fun r => ∫ θ in (-Real.pi)..Real.pi,
      r * discEnergyDivergence J (r • L08_unitCircle θ)) (Icc (0 : ℝ) 1) :=
    discEnergy_continuousOn_angularIntegral (neg_le_self Real.pi_pos.le)
      (continuousOn_fst.mul (hdiv.comp hp.continuousOn
        (fun p hp => discEnergy_polar_mem_closed hp.1 p.2)))
  rw [discEnergy_integral_polar hdiv]
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (show (0 : ℝ) ≤ 1 by norm_num) (discEnergyRadialFlux_continuousOn hF)
    (fun r hr => discEnergyRadialFlux_hasDerivAt hF hJ hD hr)
    (ContinuousOn.intervalIntegrable_of_Icc (by norm_num) hrad)
  simpa only [discEnergyRadialFlux, one_smul, one_mul, zero_mul,
    intervalIntegral.integral_zero, sub_zero] using hFTC

end Yau.LeafProofs
