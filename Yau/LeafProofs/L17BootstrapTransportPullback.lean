import Yau.LeafProofs.L17BootstrapPatch
import Yau.LeafProofs.L17BootstrapHolderInterpolationSpace

open Set Metric
open scoped Topology ContDiff
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17BootstrapTransportAux
open L17Aux L17HolderAux L17SchauderAux L17BootstrapPatchAux L17SmallTranslationAux
open L17BootstrapHolderInterpolationAux
variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}
variable {P : UniformChartPartition g} {x : M.Carrier}

 theorem local_difference_bound {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {T gamma : ℝ} (u : LocalHolderSpace F P T gamma) (p : P.centers)
    (q r : ChartCylinder P T) :
    ‖localFun F u ⟨p,r⟩-localFun F u ⟨p,q⟩‖ ≤
      ‖u‖*(parabolicDistance q r/P.radius)^gamma := by
  by_cases hqr : q=r
  · subst r
    simp only [sub_self,norm_zero]
    exact mul_nonneg (norm_nonneg u) (Real.rpow_nonneg (div_nonneg
      (by simp [parabolicDistance]) P.radius_pos.le) gamma)
  · let i : ChartPairs P T := ⟨p,⟨(q,r),hqr⟩⟩
    have h := localWeighted_difference_norm_le F u i
    rw [weighted_norm_eq_scaled_quotient] at h
    exact (div_le_iff₀ (Real.rpow_pos_of_pos (div_pos (parabolicDistance_pos_of_ne hqr) P.radius_pos) gamma)).mp h

variable (D : BootstrapPatch P x) {theta : ComplexVector n} (htheta : ‖theta‖ < D.smallRadius)

def translatedChartPoint {T : ℝ} (q : ChartCylinder P T) : ChartCylinder P T :=
  (⟨cutoffTranslation D.bump theta q.1,D.coordinate_mapsTo_ball htheta q.1.property⟩,q.2)

def translatedLocalPoint {T : ℝ} (q : LocalCylinder P T) : LocalCylinder P T :=
  ⟨q.1,translatedChartPoint D htheta q.2⟩

theorem translatedLocalPoint_continuous (T : ℝ) :
    Continuous (translatedLocalPoint D (T := T) htheta) := by
  apply continuous_sigma_iff.mpr
  intro p
  apply continuous_sigmaMk.comp
  exact (((cutoffTranslation_contDiff D.bump_smooth theta).continuous.comp
    (continuous_subtype_val.comp continuous_fst)).subtype_mk _).prodMk continuous_snd

theorem translated_parabolicDistance_le {T : ℝ} (q r : ChartCylinder P T) :
    parabolicDistance (translatedChartPoint D htheta q) (translatedChartPoint D htheta r) ≤
      2*parabolicDistance q r := by
  have h := D.coordinate_sub_norm_le htheta (q.1 : ComplexVector n) r.1
  change ‖cutoffTranslation D.bump theta q.1-cutoffTranslation D.bump theta r.1‖+
    Real.sqrt |(q.2 : ℝ)-(r.2 : ℝ)| ≤ 2*(‖(q.1 : ComplexVector n)-r.1‖+Real.sqrt |(q.2 : ℝ)-(r.2 : ℝ)|)
  linarith [Real.sqrt_nonneg |(q.2 : ℝ)-(r.2 : ℝ)|]

variable (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {T gamma : ℝ} (hgamma : 0 ≤ gamma) (hgamma1 : gamma ≤ 1)

include hgamma hgamma1 in
theorem translatedLocalFun_weighted_bound (u : LocalHolderSpace F P T gamma) (i : ChartPairs P T) :
    ‖pairWeight P T gamma i •
      (localFun F u (translatedLocalPoint D htheta (localRight P T i))-
        localFun F u (translatedLocalPoint D htheta (localLeft P T i)))‖ ≤ 2*‖u‖ := by
  let q := i.2.val.1
  let r := i.2.val.2
  have hd : 0 < parabolicDistance q r/P.radius := div_pos (parabolicDistance_pos_of_ne i.2.property) P.radius_pos
  have hD0 : 0 ≤ parabolicDistance (translatedChartPoint D htheta q) (translatedChartPoint D htheta r)/P.radius := by
    exact div_nonneg (add_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)) P.radius_pos.le
  have hD : parabolicDistance (translatedChartPoint D htheta q) (translatedChartPoint D htheta r)/P.radius ≤
      2*(parabolicDistance q r/P.radius) := by
    apply (div_le_iff₀ P.radius_pos).mpr
    have h := translated_parabolicDistance_le D htheta q r
    convert h using 1; field_simp [P.radius_pos.ne']
  have hTwo : (2 : ℝ)^gamma ≤ 2 := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) hgamma1
  have hPair := local_difference_bound u i.1 (translatedChartPoint D htheta q) (translatedChartPoint D htheta r)
  rw [weighted_norm_eq_scaled_quotient]
  apply (div_le_iff₀ (Real.rpow_pos_of_pos hd gamma)).mpr
  apply hPair.trans
  have hPow := Real.rpow_le_rpow hD0 hD hgamma
  rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hd.le] at hPow
  have h := mul_le_mul_of_nonneg_left (hPow.trans (mul_le_mul_of_nonneg_right hTwo (Real.rpow_nonneg hd.le _))) (norm_nonneg u)
  exact h.trans_eq (by ring)

def localPullbackElement (u : LocalHolderSpace F P T gamma) : LocalHolderSpace F P T gamma :=
  localOfBounds F P T gamma (fun q => localFun F u (translatedLocalPoint D htheta q))
    (u.val.1.continuous.comp (translatedLocalPoint_continuous D htheta T)) ‖u‖ (2*‖u‖)
    (fun _q => localValue_norm_le F u _) (translatedLocalFun_weighted_bound D htheta F hgamma hgamma1 u)

theorem localPullbackElement_value (u : LocalHolderSpace F P T gamma) (q : LocalCylinder P T) :
    localFun F (localPullbackElement D htheta F hgamma hgamma1 u) q=
      localFun F u (translatedLocalPoint D htheta q) := rfl

theorem localPullbackElement_norm_le (u : LocalHolderSpace F P T gamma) :
    ‖localPullbackElement D htheta F hgamma hgamma1 u‖ ≤ 2*‖u‖ := by
  apply (localOfBounds_norm_le F P T gamma _ _ _ _ (norm_nonneg u) (by positivity) _ _).trans
  exact max_le (by linarith [norm_nonneg u]) le_rfl

def localPullbackLinearMap : LocalHolderSpace F P T gamma →ₗ[ℝ] LocalHolderSpace F P T gamma where
  toFun := localPullbackElement D htheta F hgamma hgamma1
  map_add' u v := by
    apply localFun_injective F P T gamma
    funext q
    rfl
  map_smul' c u := by
    apply localFun_injective F P T gamma
    funext q
    rfl

def localPullbackCLM : LocalHolderSpace F P T gamma →L[ℝ] LocalHolderSpace F P T gamma :=
  (localPullbackLinearMap D htheta F hgamma hgamma1).mkContinuous 2
    (localPullbackElement_norm_le D htheta F hgamma hgamma1)

theorem localPullbackCLM_value (u : LocalHolderSpace F P T gamma) (q : LocalCylinder P T) :
    localFun F (localPullbackCLM D htheta F hgamma hgamma1 u) q=
      localFun F u (translatedLocalPoint D htheta q) := rfl

end Yau.LeafProofs.L17BootstrapTransportAux
