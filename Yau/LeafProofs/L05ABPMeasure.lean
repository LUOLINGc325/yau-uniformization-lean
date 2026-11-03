import Yau.LeafProofs.L05ABPJacobian

noncomputable section

open Filter MeasureTheory
open scoped Topology ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius

namespace Yau.LeafProofs.L05Aux

open Yau.Parabolic

theorem contactCone_volume {n : ℕ} {m : ℝ} (hm : 0 < m) :
    (volume (contactCone n m)).toReal = abpKappa n*m^(2*n+1) := by
  have hball := Measure.addHaar_ball_of_pos (volume : Measure (Space n)) (0 : Space n)
    (by positivity : 0 < m/4)
  rw [complexVector_finrank_real] at hball
  have hlen : 3*m/4-m/4 = m/2 := by ring
  rw [contactCone,Measure.volume_eq_prod,Measure.prod_prod,Real.volume_Ioo,hlen,hball,
    ENNReal.toReal_mul,ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ (m/4)^(2*n)),
    ENNReal.toReal_ofReal (by positivity : 0 ≤ m/2)]
  unfold abpKappa
  rw [div_pow,pow_succ]
  field_simp

theorem smoothContact_subset_closed {n : ℕ} {R a b : ℝ} {u : Point n → ℝ} :
    smoothContact R a b u ⊆ abpClosed n R a b := by
  intro z hz
  exact ⟨Metric.ball_subset_closedBall hz.1.1,hz.1.2.1.le,hz.1.2.2.le⟩

theorem smoothContact_jacobian_integrable {n : ℕ} {R a b : ℝ} {u : Point n → ℝ}
    (hu : ContDiff ℝ ∞ u) :
    IntegrableOn (fun z => |(fderiv ℝ (contactMap u) z).det|) (smoothContact R a b u) := by
  have hc : Continuous (fun z => |(fderiv ℝ (contactMap u) z).det|) :=
    (ContinuousLinearMap.continuous_det.comp
      ((contactMap_smooth hu).continuous_fderiv (by simp))).abs
  have hD : IsCompact (abpClosed n R a b) :=
    (ProperSpace.isCompact_closedBall (0 : Space n) R).prod isCompact_Icc
  exact (hc.locallyIntegrable.integrableOn_isCompact hD).mono_set smoothContact_subset_closed

/-- The geometric ABP estimate uses the all-points smooth Jacobian theorem.
No nonsmooth contact image or exceptional Peano set is mapped here. -/
theorem smooth_contact_geometric {n : ℕ} {R a b : ℝ} {u : Point n → ℝ}
    (hR : 0 < R) (hR1 : R ≤ 1) (hab : a < b) (hu : ContDiff ℝ ∞ u)
    (hboundary : ∀ z ∈ abpBoundary n R a b, u z ≤ 0)
    {z0 : Point n} (hz0 : z0 ∈ abpClosed n R a b) :
    abpKappa n*(max (u z0) 0)^(2*n+1) ≤
      ∫ z in smoothContact R a b u,
        timeD Set.univ u z*Matrix.det (-(hessian u z : Mat n)) := by
  let L05ABPMeasure_pointVolumeHaar : (volume : Measure (Point n)).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure _ _
  let J : Point n → ℝ := fun z => |(fderiv ℝ (contactMap u) z).det|
  have hJ : IntegrableOn J (smoothContact R a b u) := smoothContact_jacobian_integrable hu
  have hnon : 0 ≤ᵐ[volume.restrict (smoothContact R a b u)] J :=
    Filter.Eventually.of_forall fun z => abs_nonneg _
  have hfinite : (∫⁻ z in smoothContact R a b u, ENNReal.ofReal (J z)) ≠ (⊤ : ENNReal) := by
    rw [← ofReal_integral_eq_lintegral_ofReal hJ hnon]
    exact ENNReal.ofReal_ne_top
  have hint : (∫⁻ z in smoothContact R a b u, ENNReal.ofReal (J z)).toReal =
      ∫ z in smoothContact R a b u, J z := by
    rw [← ofReal_integral_eq_lintegral_ofReal hJ hnon,
      ENNReal.toReal_ofReal (integral_nonneg_of_ae hnon)]
  have heq : (∫ z in smoothContact R a b u, J z) =
      ∫ z in smoothContact R a b u,
        timeD Set.univ u z*Matrix.det (-(hessian u z : Mat n)) := by
    apply setIntegral_congr_fun (smoothContact_measurable hu)
    intro z hz
    exact contactMap_abs_det hu hz
  rw [← heq]
  by_cases hm : 0 < u z0
  · rw [max_eq_left hm.le]
    have hcone := contactCone_subset_image hR hR1 hab hu hboundary hz0 hm
    have harea : volume (contactMap u '' smoothContact R a b u) ≤
        ∫⁻ z in smoothContact R a b u, ENNReal.ofReal |(fderiv ℝ (contactMap u) z).det| :=
      addHaar_image_le_lintegral_abs_det_fderiv (volume : Measure (Point n))
        (smoothContact_measurable hu)
        (fun z _ => ((contactMap_smooth hu).differentiable (by simp) z).hasFDerivAt.hasFDerivWithinAt)
    have hle : volume (contactCone n (u z0)) ≤
        ∫⁻ z in smoothContact R a b u, ENNReal.ofReal (J z) :=
      (measure_mono hcone).trans harea
    have hh := ENNReal.toReal_mono hfinite hle
    rw [contactCone_volume hm,hint] at hh
    exact hh
  · rw [max_eq_right (le_of_not_gt hm),zero_pow (by omega),mul_zero]
    exact integral_nonneg_of_ae hnon

/-- The smooth Pucci subcase, with the source integral justified before it
is used. The viscosity endpoint still requires the regularization argument. -/
theorem smooth_contact_abp_power {n : ℕ} {R a b ell L : ℝ} {u g : Point n → ℝ}
    (hR : 0 < R) (hR1 : R ≤ 1) (hab : a < b) (hell : 0 < ell) (hL : ell ≤ L)
    (hu : ContDiff ℝ ∞ u) (hg : ContinuousOn g (abpClosed n R a b))
    (hboundary : ∀ z ∈ abpBoundary n R a b, u z ≤ 0)
    (hsub : ∀ z ∈ abpOpen n R a b,
      timeD Set.univ u z-pucciPlus ell L (hessian u z) ≤ g z)
    {z0 : Point n} (hz0 : z0 ∈ abpClosed n R a b) :
    abpKappa n*(max (u z0) 0)^(2*n+1) ≤
      (ell⁻¹)^(2*n)*∫ z in abpOpen n R a b, (max (g z) 0)^(2*n+1) := by
  let F : Point n → ℝ := fun z => timeD Set.univ u z*Matrix.det (-(hessian u z : Mat n))
  let G : Point n → ℝ := fun z => (max (g z) 0)^(2*n+1)
  have hD : IsCompact (abpClosed n R a b) :=
    (ProperSpace.isCompact_closedBall (0 : Space n) R).prod isCompact_Icc
  have hQsub : abpOpen n R a b ⊆ abpClosed n R a b :=
    fun z hz => ⟨Metric.ball_subset_closedBall hz.1,hz.2.1.le,hz.2.2.le⟩
  have hSsub : smoothContact R a b u ⊆ abpOpen n R a b := fun _ hz => hz.1
  have hGc : ContinuousOn G (abpClosed n R a b) := by
    intro z hz
    exact ((hg z hz).sup continuousWithinAt_const).pow (2*n+1)
  have hG : IntegrableOn G (abpOpen n R a b) :=
    (hGc.integrableOn_compact hD).mono_set hQsub
  have hGS : IntegrableOn G (smoothContact R a b u) := hG.mono_set hSsub
  have hF : IntegrableOn F (smoothContact R a b u) :=
    (smoothContact_jacobian_integrable hu).congr_fun
      (fun z hz => contactMap_abs_det hu hz) (smoothContact_measurable hu)
  have hpoint (z : Point n) (hz : z ∈ smoothContact R a b u) :
      F z ≤ (ell⁻¹)^(2*n)*G z := by
    have ht := smoothContact_time_nonneg hu hz
    have hH := smoothContact_hessian_nonpos hu hz
    have hineq := hsub z hz.1
    rw [pucciPlus_of_nonpos hell.le hL _ hH] at hineq
    have hc : timeD Set.univ u z+ell*Matrix.trace (-(hessian u z : Mat n)) ≤ g z := by
      rw [Matrix.trace_neg]
      linarith
    have hd := contact_determinant_bound hH ht hell hc
    simpa only [F,G,Fintype.card_prod,Fintype.card_fin,Nat.mul_comm] using hd
  calc
    _ ≤ ∫ z in smoothContact R a b u, F z := smooth_contact_geometric hR hR1 hab hu hboundary hz0
    _ ≤ ∫ z in smoothContact R a b u, (ell⁻¹)^(2*n)*G z :=
      setIntegral_mono_on hF (hGS.const_mul _) (smoothContact_measurable hu) hpoint
    _ = (ell⁻¹)^(2*n)*∫ z in smoothContact R a b u, G z := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (setIntegral_mono_set hG (Filter.Eventually.of_forall fun z => by
        exact pow_nonneg (le_max_right _ _) _) (Filter.Eventually.of_forall hSsub))
      (pow_nonneg (inv_nonneg.mpr hell.le) _)

theorem smooth_contact_abp {n : ℕ} {R a b ell L : ℝ} {u g : Point n → ℝ}
    (hR : 0 < R) (hR1 : R ≤ 1) (hab : a < b) (hell : 0 < ell) (hL : ell ≤ L)
    (hu : ContDiff ℝ ∞ u) (hg : ContinuousOn g (abpClosed n R a b))
    (hboundary : ∀ z ∈ abpBoundary n R a b, u z ≤ 0)
    (hsub : ∀ z ∈ abpOpen n R a b,
      timeD Set.univ u z-pucciPlus ell L (hessian u z) ≤ g z)
    {z0 : Point n} (hz0 : z0 ∈ abpClosed n R a b) :
    u z0 ≤ abpC n ell*
      (∫ z in abpOpen n R a b, (max (g z) 0)^(2*n+1))^(1/((2*n+1 : ℕ) : ℝ)) := by
  let J := ∫ z in abpOpen n R a b, (max (g z) 0)^(2*n+1)
  have hJ : 0 ≤ J := integral_nonneg fun z => pow_nonneg (le_max_right _ _) _
  have hk := abpKappa_pos n
  have hA : 0 ≤ (abpKappa n)⁻¹*(ell⁻¹)^(2*n) := by positivity
  have hp := smooth_contact_abp_power hR hR1 hab hell hL hu hg hboundary hsub hz0
  have hp' : (max (u z0) 0)^(2*n+1) ≤ ((abpKappa n)⁻¹*(ell⁻¹)^(2*n))*J := by
    have hh : (max (u z0) 0)^(2*n+1) ≤ ((ell⁻¹)^(2*n)*J)/abpKappa n :=
      (le_div_iff₀ hk).2 (by simpa only [J,mul_comm] using hp)
    simpa only [J,div_eq_mul_inv,mul_assoc,mul_comm,mul_left_comm] using hh
  have hroot := abp_root_of_power (by omega : 0 < 2*n+1) (le_max_right (u z0) 0) hA hJ hp'
  have hbudget : 1+(abpKappa n)⁻¹*(ell⁻¹)^(2*n) ≤ abpC n ell := by
    unfold abpC
    apply add_le_add le_rfl
    apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hk.le)
    apply pow_le_pow_left₀ (inv_nonneg.mpr hell.le)
    rw [div_eq_mul_inv]
    nlinarith [inv_nonneg.mpr hell.le]
  exact (le_max_left (u z0) 0).trans (hroot.trans
    (mul_le_mul_of_nonneg_right hbudget (Real.rpow_nonneg hJ _)))

end Yau.LeafProofs.L05Aux
