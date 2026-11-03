import Yau.LeafProofs.L16TraceLayerTangential

open MeasureTheory Filter Set
open scoped Topology ContDiff
noncomputable section
set_option maxHeartbeats 1600000
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic Yau.ParabolicCandidates
local instance traceTangentialHolder_dualGroup {n : ℕ} : NormedAddCommGroup (Space n →L[ℝ] ℝ) := inferInstance
local instance traceTangentialHolder_dualSpace {n : ℕ} : NormedSpace ℝ (Space n →L[ℝ] ℝ) := inferInstance
local instance traceTangentialHolder_bilinearGroup {n : ℕ} : NormedAddCommGroup (Space n →L[ℝ] Space n →L[ℝ] ℝ) := inferInstance
local instance traceTangentialHolder_bilinearSpace {n : ℕ} : NormedSpace ℝ (Space n →L[ℝ] Space n →L[ℝ] ℝ) := inferInstance

/-- Absolute integrability of the actual profile-weighted cancelled Hessian. -/
theorem normalTraceTangentialSecond_integrable {n : ℕ} {α F H t a : ℝ}
    (hα : 0 < α) {B : Point n → ℝ} (hB : Continuous B) (hF : ∀ p, |B p| ≤ F)
    (hH0 : 0 ≤ H) (hH : ∀ s x y, |B (x,s)-B (y,s)| ≤ H*‖x-y‖^α)
    (ht : 0 ≤ t) (ha : 0 ≤ a) (ξ : Space n) :
    IntervalIntegrable (fun r : ℝ => normalHeatProfile r a •
      fderiv ℝ (fderiv ℝ (heatAverage r (fun y => B (y,t-r)))) ξ) volume 0 t := by
  rcases ht.eq_or_lt with rfl | ht
  · exact IntervalIntegrable.refl
  apply (intervalIntegrable_iff_integrableOn_Ioo_of_le ht.le).mpr
  have hμ : volume.restrict (Ioo (0 : ℝ) t) ≤ volume.restrict (Ioi (0 : ℝ)) :=
    Measure.restrict_mono_set volume (fun _ hr => hr.1)
  exact ((intervalIntegrable_iff_integrableOn_Ioo_of_le ht.le).mp
    (retardedHeatAverage_secondFDeriv_time_integrable hα hB hF hH0 hH ht ξ)).bdd_smul 1
      ((normalHeatProfile_time_aestronglyMeasurable a).mono_measure hμ) (by
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
        rw [Real.norm_eq_abs,abs_of_nonneg (normalHeatProfile_bounds hr.1 ha).1]
        exact (normalHeatProfile_bounds hr.1 ha).2)

/-- The actual Gaussian primitive is uniformly Lipschitz in its height. -/
theorem normalHeatProfile_normal_increment_bound {r : ℝ} (hr : 0 < r) (a b : ℝ) :
    |normalHeatProfile r a-normalHeatProfile r b| ≤
      (2*(Real.sqrt (4*Real.pi))⁻¹)*|a-b| *r^(-(1/2 : ℝ)) := by
  have hh := Convex.norm_image_sub_le_of_norm_deriv_le (s := (univ : Set ℝ))
    (f := normalHeatProfile r) (C := (2*(Real.sqrt (4*Real.pi))⁻¹)*r^(-(1/2 : ℝ)))
    (fun x _ => (normalHeatProfile_hasDerivAt r x).differentiableAt)
    (by
      intro x _
      rw [(normalHeatProfile_hasDerivAt r x).deriv,Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (by norm_num) (normalGaussianKernel_pos hr x).le)]
      have h := mul_le_mul_of_nonneg_left (normalGaussianKernel_le_rpow hr x) (by norm_num : (0:ℝ) ≤ 2)
      simpa only [mul_assoc] using h)
    convex_univ (mem_univ b) (mem_univ a)
  simp only [Real.norm_eq_abs] at hh
  convert hh using 1; ring

/-- Tangent-location Holder continuity of the genuine TT integral. -/
theorem normalTraceTangentialSecond_spatial_holder_bound {n : ℕ} {α : ℝ}
    (hα : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (B : Point n → ℝ) (F H : ℝ),
      Continuous B → (∀ p, |B p| ≤ F) → 0 ≤ H →
      (∀ s x y, |B (x,s)-B (y,s)| ≤ H*‖x-y‖^α) →
      ∀ t a : ℝ, 0 ≤ t → 0 ≤ a → ∀ ξ η : Space n,
        ‖normalTraceTangentialSecond B t a ξ-normalTraceTangentialSecond B t a η‖ ≤
          C*H*‖ξ-η‖^α := by
  obtain ⟨C2,hC2,hHess⟩ := heatAverage_secondFDeriv_holder_bound (n := n) hα.le
  obtain ⟨C3,hC3,hInc⟩ := heatAverage_secondFDeriv_spatial_increment_bound (n := n) hα.le hα1.le
  let C : ℝ := 4*C2/α+2*C3/(1-α)
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  intro B F H hB hF hH0 hH t a ht ha ξ η
  rcases ht.eq_or_lt with rfl | ht
  · rw [normalTraceTangentialSecond_initial,normalTraceTangentialSecond_initial,sub_self,norm_zero]
    positivity
  by_cases hξη : ξ = η
  · subst η
    simp only [sub_self,norm_zero,Real.zero_rpow hα.ne',mul_zero,le_refl]
  have hd : 0 < ‖ξ-η‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hξη)
  let K : ℝ → Space n →L[ℝ] Space n →L[ℝ] ℝ := fun r =>
    normalHeatProfile r a • (fderiv ℝ (fderiv ℝ (heatAverage r (fun y => B (y,t-r)))) ξ-
      fderiv ℝ (fderiv ℝ (heatAverage r (fun y => B (y,t-r)))) η)
  have hIξ := normalTraceTangentialSecond_integrable hα hB hF hH0 hH ht.le ha ξ
  have hIη := normalTraceTangentialSecond_integrable hα hB hF hH0 hH ht.le ha η
  have hKi : IntervalIntegrable K volume 0 t := by
    simpa only [K,smul_sub] using hIξ.sub hIη
  have heq : normalTraceTangentialSecond B t a ξ-normalTraceTangentialSecond B t a η =
      ∫ r in (0 : ℝ)..t, K r := by
    rw [normalTraceTangentialSecond,normalTraceTangentialSecond,← intervalIntegral.integral_sub hIξ hIη]
    simp only [K,smul_sub]
  have hnear (r : ℝ) (hr : r ∈ Ioc 0 t) : ‖K r‖ ≤ (2*C2*H)*r^(α/2-1) := by
    obtain ⟨hh0,hh1⟩ := normalHeatProfile_bounds hr.1 ha
    dsimp only [K]
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hh0]
    calc
      _ ≤ ‖fderiv ℝ (fderiv ℝ (heatAverage r (fun y => B (y,t-r)))) ξ-
        fderiv ℝ (fderiv ℝ (heatAverage r (fun y => B (y,t-r)))) η‖ :=
          mul_le_of_le_one_left (norm_nonneg _) hh1
      _ ≤ _ := (norm_sub_le _ _).trans (by
        convert add_le_add
          (hHess r hr.1 (fun y => B (y,t-r)) F H (hB.comp (continuous_id.prodMk continuous_const))
            (fun y => hF (y,t-r)) hH0 (hH (t-r)) ξ)
          (hHess r hr.1 (fun y => B (y,t-r)) F H (hB.comp (continuous_id.prodMk continuous_const))
            (fun y => hF (y,t-r)) hH0 (hH (t-r)) η) using 1; ring)
  have hfar (r : ℝ) (hr : r ∈ Ioc (‖ξ-η‖^2) t) :
      ‖K r‖ ≤ (C3*H)*‖ξ-η‖*r^(α/2-3/2) := by
    have hr0 : 0 < r := (sq_pos_of_pos hd).trans hr.1
    obtain ⟨hh0,hh1⟩ := normalHeatProfile_bounds hr0 ha
    dsimp only [K]
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hh0]
    apply (mul_le_of_le_one_left (norm_nonneg _) hh1).trans
    have h := hInc r hr0 (fun y => B (y,t-r)) F H (hB.comp (continuous_id.prodMk continuous_const))
      (fun y => hF (y,t-r)) hH0 (hH (t-r)) η (ξ-η) (Real.le_sqrt_of_sq_le hr.1.le)
    simpa only [add_sub_cancel] using h
  rw [heq]
  have hb := schauder_spatial_near_far_integral_bound hα hα1
    (by positivity : 0 ≤ 2*C2*H) (by positivity : 0 ≤ C3*H) hd ht hKi hnear hfar
  convert hb using 1; dsimp [C]; ring


/-- Height Holder continuity, including height zero, from the true profile derivative. -/
theorem normalTraceTangentialSecond_normal_holder_bound {n : ℕ} {α : ℝ}
    (hα : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (B : Point n → ℝ) (F H : ℝ),
      Continuous B → (∀ p, |B p| ≤ F) → 0 ≤ H →
      (∀ s x y, |B (x,s)-B (y,s)| ≤ H*‖x-y‖^α) →
      ∀ t a b : ℝ, 0 ≤ t → 0 ≤ a → 0 ≤ b → ∀ ξ : Space n,
        ‖normalTraceTangentialSecond B t a ξ-normalTraceTangentialSecond B t b ξ‖ ≤
          C*H*|a-b|^α := by
  obtain ⟨C2,hC2,hHess⟩ := heatAverage_secondFDeriv_holder_bound (n := n) hα.le
  let Cg : ℝ := 2*(Real.sqrt (4*Real.pi))⁻¹
  have hCg : 0 < Cg := by dsimp [Cg]; positivity
  let C : ℝ := 4*C2/α+2*(Cg*C2)/(1-α)
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  intro B F H hB hF hH0 hH t a b ht ha hb ξ
  rcases ht.eq_or_lt with rfl | ht
  · rw [normalTraceTangentialSecond_initial,normalTraceTangentialSecond_initial,sub_self,norm_zero]
    positivity
  by_cases hab : a = b
  · subst b
    simp only [sub_self,norm_zero,abs_zero,Real.zero_rpow hα.ne',mul_zero,le_refl]
  have hd : 0 < |a-b| := abs_pos.mpr (sub_ne_zero.mpr hab)
  let K : ℝ → Space n →L[ℝ] Space n →L[ℝ] ℝ := fun r =>
    (normalHeatProfile r a-normalHeatProfile r b) •
      fderiv ℝ (fderiv ℝ (heatAverage r (fun y => B (y,t-r)))) ξ
  have hIa := normalTraceTangentialSecond_integrable hα hB hF hH0 hH ht.le ha ξ
  have hIb := normalTraceTangentialSecond_integrable hα hB hF hH0 hH ht.le hb ξ
  have hKi : IntervalIntegrable K volume 0 t := by
    simpa only [K,sub_smul] using hIa.sub hIb
  have heq : normalTraceTangentialSecond B t a ξ-normalTraceTangentialSecond B t b ξ =
      ∫ r in (0 : ℝ)..t, K r := by
    rw [normalTraceTangentialSecond,normalTraceTangentialSecond,← intervalIntegral.integral_sub hIa hIb]
    simp only [K,sub_smul]
  have hnear (r : ℝ) (hr : r ∈ Ioc 0 t) : ‖K r‖ ≤ (2*C2*H)*r^(α/2-1) := by
    have ha' := normalHeatProfile_bounds hr.1 ha
    have hb' := normalHeatProfile_bounds hr.1 hb
    have hdiff : |normalHeatProfile r a-normalHeatProfile r b| ≤ 2 := by
      rw [abs_le]; constructor <;> linarith
    dsimp only [K]
    rw [norm_smul,Real.norm_eq_abs]
    calc
      _ ≤ 2*(C2*H*r^(α/2-1)) := mul_le_mul hdiff
        (hHess r hr.1 (fun y => B (y,t-r)) F H (hB.comp (continuous_id.prodMk continuous_const))
          (fun y => hF (y,t-r)) hH0 (hH (t-r)) ξ) (norm_nonneg _) (by norm_num)
      _ = _ := by ring
  have hfar (r : ℝ) (hr : r ∈ Ioc (|a-b|^2) t) :
      ‖K r‖ ≤ ((Cg*C2)*H)*|a-b| *r^(α/2-3/2) := by
    have hr0 : 0 < r := (sq_pos_of_pos hd).trans hr.1
    have hPow : r^(-(1/2 : ℝ))*r^(α/2-1) = r^(α/2-3/2) := by
      rw [← Real.rpow_add hr0]; congr 1; ring
    dsimp only [K]
    rw [norm_smul,Real.norm_eq_abs]
    calc
      _ ≤ (Cg*|a-b| *r^(-(1/2 : ℝ)))*(C2*H*r^(α/2-1)) :=
        mul_le_mul (normalHeatProfile_normal_increment_bound hr0 a b)
          (hHess r hr0 (fun y => B (y,t-r)) F H (hB.comp (continuous_id.prodMk continuous_const))
            (fun y => hF (y,t-r)) hH0 (hH (t-r)) ξ) (norm_nonneg _) (by positivity)
      _ = ((Cg*C2)*H)*|a-b| *(r^(-(1/2 : ℝ))*r^(α/2-1)) := by ring
      _ = _ := by rw [hPow]
  rw [heq]
  have hh := schauder_spatial_near_far_integral_bound hα hα1
    (by positivity : 0 ≤ 2*C2*H) (by positivity : 0 ≤ (Cg*C2)*H) hd ht hKi hnear hfar
  convert hh using 1; dsimp [C]; ring

/-- An honest uniform Poisson bound follows by Gaussian polynomial absorption. -/
theorem normalPoissonKernel_uniform_age_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 0 < r → ∀ a : ℝ, 0 ≤ a →
      normalPoissonKernel a r ≤ C/r := by
  obtain ⟨C,hC,hG⟩ := gaussian_weight_bounded (s := 1) (b := 1/4) (by norm_num) (by norm_num)
  refine ⟨(Real.sqrt (4*Real.pi))⁻¹*C,by positivity,?_⟩
  intro r hr a ha
  let z : ℝ := a/Real.sqrt r
  have hs : Real.sqrt r ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hr)
  have hSc := normalGaussianKernel_sqrt_scaling hr z
  have hz : Real.sqrt r*z = a := by dsimp [z]; field_simp
  rw [hz] at hSc
  have hEq : normalPoissonKernel a r*r = z*normalGaussianKernel 1 z := by
    rw [← hSc]
    dsimp only [normalPoissonKernel,z]
    field_simp
  apply (le_div_iff₀ hr).mpr
  rw [hEq]
  calc
    _ = (Real.sqrt (4*Real.pi))⁻¹*(z*Real.exp (-(1/4 : ℝ)*z^2)) := by
      dsimp only [normalGaussianKernel]
      norm_num
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (by simpa only [Real.rpow_one] using hG z (by dsimp [z]; positivity)) (by positivity)

/-- Age increments use the actual time derivative of the Gaussian primitive. -/
theorem normalHeatProfile_time_increment_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 0 < r → ∀ δ : ℝ, 0 ≤ δ →
      ∀ a : ℝ, 0 ≤ a → |normalHeatProfile (r+δ) a-normalHeatProfile r a| ≤ C*δ/r := by
  obtain ⟨C,hC,hP⟩ := normalPoissonKernel_uniform_age_bound
  refine ⟨C,hC,?_⟩
  intro r hr δ hδ a ha
  have hle : r ≤ r+δ := le_add_of_nonneg_right hδ
  have hMean := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun u (hu : u ∈ Icc r (r+δ)) => (normalHeatProfile_time_hasDerivAt (hr.trans_le hu.1) a).differentiableAt)
    (fun u (hu : u ∈ Icc r (r+δ)) => by
      rw [(normalHeatProfile_time_hasDerivAt (hr.trans_le hu.1) a).deriv,
        Real.norm_eq_abs,abs_neg,abs_of_nonneg (normalPoissonKernel_nonneg ha (hr.trans_le hu.1))]
      exact (hP u (hr.trans_le hu.1) a ha).trans (div_le_div_of_nonneg_left hC.le hr hu.1))
    (convex_Icc r (r+δ)) (left_mem_Icc.mpr hle) (right_mem_Icc.mpr hle)
  simp only [Real.norm_eq_abs,add_sub_cancel_left,abs_of_nonneg hδ] at hMean
  convert hMean using 1; ring


/-- Source-time form of the genuinely integrable TT kernel. -/
theorem normalTraceTangentialSecond_source_integrable {n : ℕ} {α F H t a : ℝ}
    (hα : 0 < α) {B : Point n → ℝ} (hB : Continuous B) (hF : ∀ p, |B p| ≤ F)
    (hH0 : 0 ≤ H) (hH : ∀ s x y, |B (x,s)-B (y,s)| ≤ H*‖x-y‖^α)
    (ht : 0 ≤ t) (ha : 0 ≤ a) (ξ : Space n) :
    IntervalIntegrable (fun σ : ℝ => normalHeatProfile (t-σ) a •
      fderiv ℝ (fderiv ℝ (heatAverage (t-σ) (fun y => B (y,σ)))) ξ) volume 0 t := by
  simpa only [sub_zero,sub_self,sub_sub_cancel] using
    ((normalTraceTangentialSecond_integrable hα hB hF hH0 hH ht ha ξ).comp_sub_left t).symm

/-- Time Holder continuity of the actual TT integral, without time differentiation of B. -/
theorem normalTraceTangentialSecond_temporal_holder_bound {n : ℕ} {α : ℝ}
    (hα : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (B : Point n → ℝ) (F H : ℝ),
      Continuous B → (∀ p, |B p| ≤ F) → 0 ≤ H →
      (∀ σ x y, |B (x,σ)-B (y,σ)| ≤ H*‖x-y‖^α) →
      ∀ t δ a : ℝ, 0 ≤ t → 0 ≤ δ → 0 ≤ a → ∀ ξ : Space n,
        ‖normalTraceTangentialSecond B (t+δ) a ξ-normalTraceTangentialSecond B t a ξ‖ ≤
          C*H*δ^(α/2) := by
  obtain ⟨C0,hC0,hInit⟩ := normalTraceTangentialSecond_bound (n := n) hα
  obtain ⟨C2,hC2,hHess⟩ := heatAverage_secondFDeriv_holder_bound (n := n) hα.le
  obtain ⟨C3,hC3,hInc⟩ := heatAverage_secondFDeriv_time_increment_bound (n := n) hα.le hα1.le
  obtain ⟨Cp,hCp,hProfile⟩ := normalHeatProfile_time_increment_bound
  let C4 : ℝ := C3+Cp*C2
  have hC4 : 0 < C4 := by dsimp [C4]; positivity
  have hTwo : 0 < 2-α := by linarith
  let C : ℝ := C0+6*C2/α+2*C4/(2-α)
  have hC : 0 < C := by dsimp [C]; positivity
  have hC0C : C0 ≤ C := by
    have h1 : 0 ≤ 6*C2/α := by positivity
    have h2 : 0 ≤ 2*C4/(2-α) := by positivity
    dsimp [C]; linarith
  have hRestC : 6*C2/α+2*C4/(2-α) ≤ C := by dsimp [C]; linarith
  refine ⟨C,hC,?_⟩
  intro B F H hB hF hH0 hH t δ a ht hδ ha ξ
  rcases hδ.eq_or_lt with rfl | hδ
  · simp only [add_zero,sub_self,norm_zero,Real.zero_rpow (by positivity : α/2 ≠ 0),mul_zero,le_refl]
  rcases ht.eq_or_lt with rfl | ht
  · rw [zero_add,normalTraceTangentialSecond_initial,sub_zero]
    exact (hInit B F H hB hF hH0 hH δ hδ.le a ha ξ).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC0C hH0)
        (Real.rpow_nonneg hδ.le _))
  have htδ : 0 < t+δ := by positivity
  have hle : t ≤ t+δ := le_add_of_nonneg_right hδ.le
  have hfc (σ : ℝ) : Continuous (fun y : Space n => B (y,σ)) :=
    hB.comp (continuous_id.prodMk continuous_const)
  have hFs (σ : ℝ) (y : Space n) : |B (y,σ)| ≤ F := hF (y,σ)
  let N : ℝ → Space n →L[ℝ] Space n →L[ℝ] ℝ := fun σ =>
    normalHeatProfile (t+δ-σ) a •
      fderiv ℝ (fderiv ℝ (heatAverage (t+δ-σ) (fun y => B (y,σ)))) ξ
  let O : ℝ → Space n →L[ℝ] Space n →L[ℝ] ℝ := fun σ =>
    normalHeatProfile (t-σ) a •
      fderiv ℝ (fderiv ℝ (heatAverage (t-σ) (fun y => B (y,σ)))) ξ
  let A : ℝ → Space n →L[ℝ] Space n →L[ℝ] ℝ := fun σ => N σ-O σ
  let K : ℝ → Space n →L[ℝ] Space n →L[ℝ] ℝ := fun r =>
    normalHeatProfile (r+δ) a •
      fderiv ℝ (fderiv ℝ (heatAverage (r+δ) (fun y => B (y,t-r)))) ξ -
    normalHeatProfile r a •
      fderiv ℝ (fderiv ℝ (heatAverage r (fun y => B (y,t-r)))) ξ
  have hNall : IntervalIntegrable N volume 0 (t+δ) :=
    normalTraceTangentialSecond_source_integrable hα hB hF hH0 hH htδ.le ha ξ
  have hNt : IntervalIntegrable N volume 0 t := hNall.mono_set (by
    rw [uIcc_of_le ht.le,uIcc_of_le htδ.le]
    exact Icc_subset_Icc le_rfl hle)
  have hNtail : IntervalIntegrable N volume t (t+δ) := hNall.mono_set (by
    rw [uIcc_of_le hle,uIcc_of_le htδ.le]
    exact Icc_subset_Icc ht.le le_rfl)
  have hOi : IntervalIntegrable O volume 0 t :=
    normalTraceTangentialSecond_source_integrable hα hB hF hH0 hH ht.le ha ξ
  have hAi : IntervalIntegrable A volume 0 t := hNt.sub hOi
  have harg (r : ℝ) : t+δ-(t-r) = r+δ := by abel
  have hKi : IntervalIntegrable K volume 0 t := by
    simpa only [K,A,N,O,sub_self,sub_zero,sub_sub_cancel,harg] using (hAi.comp_sub_left t).symm
  have hKa : (∫ r in (0 : ℝ)..t, K r) = ∫ σ in (0 : ℝ)..t, A σ := by
    simpa only [K,A,N,O,sub_self,sub_zero,sub_sub_cancel,harg] using
      (intervalIntegral.integral_comp_sub_left (a := (0 : ℝ)) (b := t) A t)
  have hSource (u : ℝ) : normalTraceTangentialSecond B u a ξ =
      ∫ σ in (0 : ℝ)..u, normalHeatProfile (u-σ) a •
        fderiv ℝ (fderiv ℝ (heatAverage (u-σ) (fun y => B (y,σ)))) ξ := by
    simpa only [normalTraceTangentialSecond,sub_self,sub_zero,sub_sub_cancel] using
      (intervalIntegral.integral_comp_sub_left (a := (0 : ℝ)) (b := u)
        (fun r => normalHeatProfile r a • fderiv ℝ (fderiv ℝ (heatAverage r (fun y => B (y,u-r)))) ξ) u).symm
  have heq : normalTraceTangentialSecond B (t+δ) a ξ-normalTraceTangentialSecond B t a ξ =
      (∫ r in (0 : ℝ)..t, K r)+(∫ σ in t..t+δ, N σ) := by
    rw [hSource (t+δ),hSource t]
    change (∫ σ in (0 : ℝ)..t+δ, N σ)-(∫ σ in (0 : ℝ)..t, O σ) = _
    rw [← intervalIntegral.integral_add_adjacent_intervals hNt hNtail,hKa]
    change _ = (∫ σ in (0 : ℝ)..t, N σ-O σ)+_
    rw [intervalIntegral.integral_sub hNt hOi]
    abel
  have hWeighted (r : ℝ) (hr : 0 < r) (σ : ℝ) :
      ‖normalHeatProfile r a • fderiv ℝ (fderiv ℝ (heatAverage r (fun y => B (y,σ)))) ξ‖ ≤
        C2*H*r^(α/2-1) := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (normalHeatProfile_bounds hr ha).1]
    exact (mul_le_of_le_one_left (norm_nonneg _) (normalHeatProfile_bounds hr ha).2).trans
      (hHess r hr (fun y => B (y,σ)) F H (hfc σ) (hFs σ) hH0 (hH σ) ξ)
  have hnear (r : ℝ) (hr : r ∈ Ioc 0 t) : ‖K r‖ ≤ (2*C2*H)*r^(α/2-1) := by
    have hp : (r+δ)^(α/2-1) ≤ r^(α/2-1) :=
      Real.rpow_le_rpow_of_nonpos hr.1 (le_add_of_nonneg_right hδ.le) (by linarith)
    calc
      _ ≤ ‖normalHeatProfile (r+δ) a • fderiv ℝ (fderiv ℝ (heatAverage (r+δ) (fun y => B (y,t-r)))) ξ‖ +
        ‖normalHeatProfile r a • fderiv ℝ (fderiv ℝ (heatAverage r (fun y => B (y,t-r)))) ξ‖ := norm_sub_le _ _
      _ ≤ C2*H*(r+δ)^(α/2-1)+C2*H*r^(α/2-1) :=
        add_le_add (hWeighted (r+δ) (add_pos hr.1 hδ) (t-r)) (hWeighted r hr.1 (t-r))
      _ ≤ C2*H*r^(α/2-1)+C2*H*r^(α/2-1) :=
        add_le_add (mul_le_mul_of_nonneg_left hp (by positivity)) le_rfl
      _ = _ := by ring
  have hfar (r : ℝ) (hr : r ∈ Ioc δ t) : ‖K r‖ ≤ (C4*H)*δ*r^(α/2-2) := by
    have hr0 : 0 < r := hδ.trans hr.1
    let J := fderiv ℝ (fderiv ℝ (heatAverage r (fun y => B (y,t-r)))) ξ
    let J' := fderiv ℝ (fderiv ℝ (heatAverage (r+δ) (fun y => B (y,t-r)))) ξ
    have hK : K r = normalHeatProfile (r+δ) a • (J'-J)+
        (normalHeatProfile (r+δ) a-normalHeatProfile r a) • J := by
      dsimp only [K,J,J']; simp only [smul_sub,sub_smul]; abel
    have hP := normalHeatProfile_bounds (add_pos hr0 hδ) ha
    have hPow : r^(α/2-1)/r = r^(α/2-2) := by
      simpa only [Real.rpow_one,show (α/2-1)-1 = α/2-2 by ring] using
        (Real.rpow_sub hr0 (α/2-1) 1).symm
    rw [hK]
    calc
      _ ≤ ‖normalHeatProfile (r+δ) a • (J'-J)‖+
        ‖(normalHeatProfile (r+δ) a-normalHeatProfile r a) • J‖ := norm_add_le _ _
      _ = normalHeatProfile (r+δ) a*‖J'-J‖+
        |normalHeatProfile (r+δ) a-normalHeatProfile r a| *‖J‖ := by
          rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg hP.1]
      _ ≤ ‖J'-J‖+(Cp*δ/r)*(C2*H*r^(α/2-1)) := add_le_add
        (mul_le_of_le_one_left (norm_nonneg _) hP.2)
        (mul_le_mul (hProfile r hr0 δ hδ.le a ha)
          (hHess r hr0 (fun y => B (y,t-r)) F H (hfc (t-r)) (hFs (t-r)) hH0 (hH (t-r)) ξ)
          (norm_nonneg _) (by positivity))
      _ ≤ C3*H*δ*r^(α/2-2)+(Cp*δ/r)*(C2*H*r^(α/2-1)) := add_le_add
        (hInc r hr0 δ hδ.le (fun y => B (y,t-r)) F H (hfc (t-r)) (hFs (t-r)) hH0 (hH (t-r)) ξ) le_rfl
      _ = C3*H*δ*r^(α/2-2)+(Cp*C2)*H*δ*(r^(α/2-1)/r) := by ring
      _ = _ := by rw [hPow]; dsimp [C4]; ring
  have hOld := schauder_temporal_near_far_integral_bound hα (by linarith : α < 2)
    (by positivity : 0 ≤ 2*C2*H) (by positivity : 0 ≤ C4*H) hδ ht hKi hnear hfar
  have hPow : IntervalIntegrable (fun σ : ℝ => (t+δ-σ)^(α/2-1)) volume t (t+δ) :=
    (schauder_time_weight_integrable hα (t+δ)).mono_set (by
      rw [uIcc_of_le hle,uIcc_of_le htδ.le]
      exact Icc_subset_Icc ht.le le_rfl)
  have hTail := intervalIntegral.norm_integral_le_of_norm_le hle
    (f := N) (g := fun σ : ℝ => C2*H*(t+δ-σ)^(α/2-1))
    (by
      filter_upwards [(volume : Measure ℝ).ae_ne (t+δ)] with σ hσt
      intro hσ
      exact hWeighted (t+δ-σ) (sub_pos.mpr (lt_of_le_of_ne hσ.2 hσt)) σ)
    (hPow.const_mul (C2*H))
  have hTailWeight : (∫ σ in t..t+δ, (t+δ-σ)^(α/2-1)) = (2/α)*δ^(α/2) := by
    rw [intervalIntegral.integral_comp_sub_left (fun r : ℝ => r^(α/2-1)) (t+δ)]
    simp only [sub_self,add_sub_cancel_left]
    rw [integral_rpow (Or.inl (by linarith : -1 < α/2-1)),
      show α/2-1+1 = α/2 by ring,Real.zero_rpow (by positivity : α/2 ≠ 0),sub_zero]
    field_simp [hα.ne']
  rw [intervalIntegral.integral_const_mul,hTailWeight] at hTail
  rw [heq]
  calc
    _ ≤ ‖∫ r in (0 : ℝ)..t, K r‖+‖∫ σ in t..t+δ, N σ‖ := norm_add_le _ _
    _ ≤ (6*C2/α+2*C4/(2-α))*H*δ^(α/2) := by
      convert add_le_add hOld hTail using 1; ring
    _ ≤ C*H*δ^(α/2) := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hRestC hH0) (Real.rpow_nonneg hδ.le _)


/-- Joint three-direction Holder estimate for the actual operator-norm TT integral.
The constant is chosen before the source and its budget. All three closed faces,
including initial time and zero height, are covered by the preceding estimates. -/
theorem normalTraceTangentialSecond_holder_bound {n : ℕ} {α : ℝ}
    (hα : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (B : Point n → ℝ) (F : ℝ),
      HolderBound α Set.univ B F →
      ∀ (ξ η : Space n) (a b t s : ℝ), 0 ≤ a → 0 ≤ b →
        t ∈ Icc 0 1 → s ∈ Icc 0 1 →
        ‖normalTraceTangentialSecond B t a ξ-normalTraceTangentialSecond B s b η‖ ≤
          C*F*(‖ξ-η‖^α+|a-b|^α+|t-s|^(α/2)) := by
  obtain ⟨Cs,hCs,hSpace⟩ := normalTraceTangentialSecond_spatial_holder_bound (n := n) hα hα1
  obtain ⟨Ca,hCa,hNormal⟩ := normalTraceTangentialSecond_normal_holder_bound (n := n) hα hα1
  obtain ⟨Ct,hCt,hTime⟩ := normalTraceTangentialSecond_temporal_holder_bound (n := n) hα hα1
  let C : ℝ := Cs+Ca+Ct
  have hC : 0 < C := by dsimp [C]; positivity
  have hCsC : Cs ≤ C := by dsimp [C]; linarith
  have hCaC : Ca ≤ C := by dsimp [C]; linarith
  have hCtC : Ct ≤ C := by dsimp [C]; linarith
  refine ⟨C,hC,?_⟩
  intro B F hB ξ η a b t s ha hb ht hs
  have hBc : Continuous B := continuousOn_univ.mp (holderBound_continuousOn hα hB)
  have hBF (p : Point n) : |B p| ≤ F := by
    simpa only [Real.norm_eq_abs] using hB.2.1 p (mem_univ _)
  have hBH (σ : ℝ) (x y : Space n) : |B (x,σ)-B (y,σ)| ≤ F*‖x-y‖^α := by
    simpa only [holderWeight,sub_self,abs_zero,
      Real.zero_rpow (by positivity : α/2 ≠ 0),add_zero,Real.norm_eq_abs] using
      hB.2.2 (x,σ) (mem_univ _) (y,σ) (mem_univ _)
  have htime : ‖normalTraceTangentialSecond B t b η-normalTraceTangentialSecond B s b η‖ ≤
      Ct*F*|t-s|^(α/2) := by
    rcases le_total s t with hst | hts
    · have hh := hTime B F F hBc hBF hB.1 hBH s (t-s) b hs.1 (sub_nonneg.mpr hst) hb η
      rw [show s+(t-s) = t by ring] at hh
      simpa only [abs_of_nonneg (sub_nonneg.mpr hst)] using hh
    · have hh := hTime B F F hBc hBF hB.1 hBH t (s-t) b ht.1 (sub_nonneg.mpr hts) hb η
      rw [show t+(s-t) = s by ring] at hh
      rw [norm_sub_rev,abs_sub_comm]
      simpa only [abs_of_nonneg (sub_nonneg.mpr hts)] using hh
  calc
    _ = ‖(normalTraceTangentialSecond B t a ξ-normalTraceTangentialSecond B t a η)+
        (normalTraceTangentialSecond B t a η-normalTraceTangentialSecond B t b η)+
        (normalTraceTangentialSecond B t b η-normalTraceTangentialSecond B s b η)‖ := by
          congr 1; abel
    _ ≤ ‖normalTraceTangentialSecond B t a ξ-normalTraceTangentialSecond B t a η‖+
        ‖normalTraceTangentialSecond B t a η-normalTraceTangentialSecond B t b η‖+
        ‖normalTraceTangentialSecond B t b η-normalTraceTangentialSecond B s b η‖ := norm_add₃_le
    _ ≤ Cs*F*‖ξ-η‖^α+Ca*F*|a-b|^α+Ct*F*|t-s|^(α/2) :=
      add_le_add (add_le_add
        (hSpace B F F hBc hBF hB.1 hBH t a ht.1 ha ξ η)
        (hNormal B F F hBc hBF hB.1 hBH t a b ht.1 ha hb η)) htime
    _ ≤ C*F*‖ξ-η‖^α+C*F*|a-b|^α+C*F*|t-s|^(α/2) :=
      add_le_add (add_le_add
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCsC hB.1)
          (Real.rpow_nonneg (norm_nonneg _) _))
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCaC hB.1)
          (Real.rpow_nonneg (abs_nonneg _) _)))
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCtC hB.1)
          (Real.rpow_nonneg (abs_nonneg _) _))
    _ = _ := by ring

end Yau.LeafProofs.L16Aux
