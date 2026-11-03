import Yau.LeafProofs.L16TracePoissonNormal

open MeasureTheory Filter
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 1200000
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic Yau.ParabolicCandidates

theorem normalGaussianKernel_le_rpow {r : ℝ} (hr : 0 < r) (a : ℝ) :
    normalGaussianKernel r a ≤ (Real.sqrt (4*Real.pi))⁻¹*r^(-(1/2 : ℝ)) := by
  have hExp : Real.exp (-(4*r)⁻¹*a^2) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by positivity)) (sq_nonneg a)
  calc
    normalGaussianKernel r a ≤ (Real.sqrt (4*Real.pi*r))⁻¹ := by
      exact mul_le_of_le_one_right (by positivity) hExp
    _ = _ := by
      rw [Real.sqrt_mul (by positivity : 0 ≤ 4*Real.pi),mul_inv_rev,
        Real.sqrt_eq_rpow,← Real.rpow_neg hr.le]
      ring

theorem normalHeatProfile_time_aestronglyMeasurable (a : ℝ) :
    AEStronglyMeasurable (fun r : ℝ => normalHeatProfile r a)
      (volume.restrict (Set.Ioi 0)) := by
  have hCont : ContinuousOn (fun r : ℝ => normalHeatProfile r a) (Set.Ioi 0) :=
    fun r hr => (normalHeatProfile_time_hasDerivAt hr a).continuousAt.continuousWithinAt
  exact hCont.aestronglyMeasurable measurableSet_Ioi

/-- The actual boundary-trace heat layer at a fixed tangent location. -/
def normalTraceLayer {n : ℕ} (B : Point n → ℝ) (ξ : Space n) (t a : ℝ) : ℝ :=
  ∫ r in (0 : ℝ)..t, normalHeatProfile r a*
    heatAverage r (fun y => B (y,t-r)) ξ

def normalTraceFirst {n : ℕ} (B : Point n → ℝ) (ξ : Space n) (t a : ℝ) : ℝ :=
  ∫ r in (0 : ℝ)..t, (2*normalGaussianKernel r a)*
    heatAverage r (fun y => B (y,t-r)) ξ

theorem normalTraceLayer_initial {n : ℕ} (B : Point n → ℝ) (ξ : Space n) (a : ℝ) :
    normalTraceLayer B ξ 0 a = 0 := by
  simp only [normalTraceLayer,intervalIntegral.integral_same]

theorem normalTraceLayer_boundary {n : ℕ} (B : Point n → ℝ) (ξ : Space n) (t : ℝ) :
    normalTraceLayer B ξ t 0 = 0 := by
  simp only [normalTraceLayer,normalHeatProfile_zero,zero_mul,intervalIntegral.integral_zero]

theorem normalTraceLayer_integrable_and_bound {n : ℕ} {F t a : ℝ}
    {B : Point n → ℝ} (hB : Continuous B) (hF : ∀ p, |B p| ≤ F)
    (ht : 0 ≤ t) (ha : 0 ≤ a) (ξ : Space n) :
    IntervalIntegrable (fun r => normalHeatProfile r a*
      heatAverage r (fun y => B (y,t-r)) ξ) volume 0 t ∧
      |normalTraceLayer B ξ t a| ≤ t*F := by
  let μ : Measure ℝ := volume.restrict (Set.Ioc 0 t)
  let : IsFiniteMeasure μ := ⟨by simp [μ,Real.volume_Ioc]⟩
  have hF0 : 0 ≤ F := (abs_nonneg (B (0,0))).trans (hF (0,0))
  have hMeasure : μ ≤ volume.restrict (Set.Ioi (0 : ℝ)) :=
    Measure.restrict_mono_set volume (fun _ hr => hr.1)
  have hHm := (normalHeatProfile_time_aestronglyMeasurable a).mono_measure hMeasure
  have hAm := (retardedHeatAverage_aestronglyMeasurable hB (ξ,t)).mono_measure hMeasure
  have hm := hHm.mul hAm
  have hb : ∀ᵐ r ∂μ, |normalHeatProfile r a*heatAverage r (fun y => B (y,t-r)) ξ| ≤ F := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    obtain ⟨hPos,hOne⟩ := normalHeatProfile_bounds hr.1 ha
    have hHeat := heatAverage_bound hr.1
      (hB.comp (continuous_id.prodMk continuous_const)) (fun y => hF (y,t-r)) ξ
    rw [abs_mul,abs_of_nonneg hPos]
    exact (mul_le_mul_of_nonneg_left hHeat hPos).trans
      ((mul_le_mul_of_nonneg_right hOne hF0).trans_eq (one_mul F))
  have hi : Integrable (fun r => normalHeatProfile r a*
      heatAverage r (fun y => B (y,t-r)) ξ) μ := by
    apply (integrable_const F).mono' hm
    filter_upwards [hb] with r hr
    simpa only [Real.norm_eq_abs,Pi.mul_apply] using hr
  refine ⟨(intervalIntegrable_iff_integrableOn_Ioc_of_le ht).mpr hi,?_⟩
  have hvol : μ.real Set.univ = t := by
    simp [μ,Measure.real,Real.volume_Ioc,ENNReal.toReal_ofReal ht]
  have hn := norm_integral_le_of_norm_le_const (μ := μ)
    (f := fun r => normalHeatProfile r a*heatAverage r (fun y => B (y,t-r)) ξ)
    (by filter_upwards [hb] with r hr; simpa only [Real.norm_eq_abs,Pi.mul_apply] using hr)
  rw [normalTraceLayer,intervalIntegral.integral_of_le ht]
  change |∫ r, normalHeatProfile r a*heatAverage r (fun y => B (y,t-r)) ξ ∂μ| ≤ t*F
  simpa only [Real.norm_eq_abs,hvol,mul_comm] using hn


theorem normalGaussianKernel_time_measurable (a : ℝ) :
    Measurable (fun r : ℝ => normalGaussianKernel r a) := by
  change Measurable (fun r : ℝ => (Real.sqrt (4*Real.pi*r))⁻¹*Real.exp (-(4*r)⁻¹*a^2))
  fun_prop

/-- The first normal derivative is an actual derivative of the trace layer,
    including the normal boundary. Its integral is genuinely convergent. -/
theorem normalTraceLayer_hasDerivAt {n : ℕ} {F t a : ℝ} {B : Point n → ℝ}
    (hB : Continuous B) (hF : ∀ p, |B p| ≤ F) (ht : 0 ≤ t) (ha : 0 ≤ a)
    (ξ : Space n) :
    IntervalIntegrable (fun r => (2*normalGaussianKernel r a)*
      heatAverage r (fun y => B (y,t-r)) ξ) volume 0 t ∧
      HasDerivAt (normalTraceLayer B ξ t) (normalTraceFirst B ξ t a) a := by
  let μ : Measure ℝ := volume.restrict (Set.Ioc 0 t)
  let A : ℝ → ℝ := fun r => heatAverage r (fun y => B (y,t-r)) ξ
  let C : ℝ := 2*(Real.sqrt (4*Real.pi))⁻¹
  let D : ℝ → ℝ := fun r => (C*F)*r^(-(1/2 : ℝ))
  have hF0 : 0 ≤ F := (abs_nonneg (B (0,0))).trans (hF (0,0))
  have hMeasure : μ ≤ volume.restrict (Set.Ioi (0 : ℝ)) :=
    Measure.restrict_mono_set volume (fun _ hr => hr.1)
  have hAm : AEStronglyMeasurable A μ :=
    (retardedHeatAverage_aestronglyMeasurable hB (ξ,t)).mono_measure hMeasure
  have hMeas : ∀ᶠ x in 𝓝 a, AEStronglyMeasurable
      (fun r => normalHeatProfile r x*A r) μ := by
    exact Filter.Eventually.of_forall fun x =>
      ((normalHeatProfile_time_aestronglyMeasurable x).mono_measure hMeasure).mul hAm
  have hInt : Integrable (fun r => normalHeatProfile r a*A r) μ :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le ht).mp
      (normalTraceLayer_integrable_and_bound hB hF ht ha ξ).1
  have hDMeas : AEStronglyMeasurable
      (fun r => (2*normalGaussianKernel r a)*A r) μ :=
    ((normalGaussianKernel_time_measurable a).const_mul 2).aestronglyMeasurable.mul hAm
  have hBound : ∀ᵐ r ∂μ, ∀ x ∈ (Set.univ : Set ℝ),
      ‖(2*normalGaussianKernel r x)*A r‖ ≤ D r := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    intro x _hx
    have hHeat := heatAverage_bound hr.1
      (hB.comp (continuous_id.prodMk continuous_const)) (fun y => hF (y,t-r)) ξ
    have hGauss := normalGaussianKernel_le_rpow hr.1 x
    have hPos : 0 ≤ 2*normalGaussianKernel r x :=
      mul_nonneg (by norm_num) (normalGaussianKernel_pos hr.1 x).le
    rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg hPos]
    calc
      _ ≤ (2*normalGaussianKernel r x)*F := mul_le_mul_of_nonneg_left hHeat hPos
      _ ≤ D r := by
        have h := mul_le_mul_of_nonneg_right hGauss (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hF0)
        dsimp only [D,C]
        convert h using 1 <;> ring
  have hPower : IntervalIntegrable (fun r : ℝ => r^(-(1/2 : ℝ))) volume 0 t :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  have hDInt : Integrable D μ :=
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le ht).mp hPower).const_mul (C*F)
  have hDeriv : ∀ᵐ r ∂μ, ∀ x ∈ (Set.univ : Set ℝ),
      HasDerivAt (fun y => normalHeatProfile r y*A r) ((2*normalGaussianKernel r x)*A r) x := by
    exact Filter.Eventually.of_forall fun r x _hx => (normalHeatProfile_hasDerivAt r x).mul_const (A r)
  obtain ⟨hi,hd⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ) (s := Set.univ) (x₀ := a) Filter.univ_mem hMeas hInt hDMeas hBound hDInt hDeriv
  refine ⟨(intervalIntegrable_iff_integrableOn_Ioc_of_le ht).mpr hi,?_⟩
  have hFun : normalTraceLayer B ξ t =
      (fun x => ∫ r, normalHeatProfile r x*A r ∂μ) := by
    funext x
    rw [normalTraceLayer,intervalIntegral.integral_of_le ht]
  have hValue : normalTraceFirst B ξ t a =
      ∫ r, (2*normalGaussianKernel r a)*A r ∂μ := by
    rw [normalTraceFirst,intervalIntegral.integral_of_le ht]
  rw [hFun,hValue]
  exact hd

/-- A genuine positive-normal domination by one fixed Poisson density. -/
theorem normalPoissonKernel_le_near {r a x : ℝ}
    (hr : 0 < r) (ha : 0 < a) (hax : a/2 ≤ x) (hxa : x ≤ 3*(a/2)) :
    normalPoissonKernel x r ≤ 3*normalPoissonKernel (a/2) r := by
  have hhalf : 0 ≤ a/2 := by positivity
  have hx : 0 ≤ x := hhalf.trans hax
  have hg := normalGaussianKernel_antitone_nonneg hr hhalf hax
  have hc : x/r ≤ (3*(a/2))/r := div_le_div_of_nonneg_right hxa hr.le
  change (x/r)*normalGaussianKernel r x ≤ 3*((a/2)/r*normalGaussianKernel r (a/2))
  calc
    _ ≤ ((3*(a/2))/r)*normalGaussianKernel r (a/2) :=
      mul_le_mul hc hg (normalGaussianKernel_pos hr x).le (by positivity)
    _ = _ := by ring

/-- The second normal derivative on the strict half space is the actual
    finite-age Poisson integral of the retarded source. -/
theorem normalTraceFirst_hasDerivAt {n : ℕ} {F t a : ℝ} {B : Point n → ℝ}
    (hB : Continuous B) (hF : ∀ p, |B p| ≤ F) (ht : 0 ≤ t) (ha : 0 < a)
    (ξ : Space n) :
    IntervalIntegrable (fun r => normalPoissonKernel a r*
      heatAverage r (fun y => B (y,t-r)) ξ) volume 0 t ∧
      HasDerivAt (normalTraceFirst B ξ t)
        (-(∫ r in (0 : ℝ)..t, normalPoissonKernel a r*
          heatAverage r (fun y => B (y,t-r)) ξ)) a := by
  let μ : Measure ℝ := volume.restrict (Set.Ioc 0 t)
  let A : ℝ → ℝ := fun r => heatAverage r (fun y => B (y,t-r)) ξ
  let D : ℝ → ℝ := fun r => (3*F)*normalPoissonKernel (a/2) r
  have hF0 : 0 ≤ F := (abs_nonneg (B (0,0))).trans (hF (0,0))
  have hMeasure : μ ≤ volume.restrict (Set.Ioi (0 : ℝ)) :=
    Measure.restrict_mono_set volume (fun _ hr => hr.1)
  have hAm : AEStronglyMeasurable A μ :=
    (retardedHeatAverage_aestronglyMeasurable hB (ξ,t)).mono_measure hMeasure
  have hMeas : ∀ᶠ x in 𝓝 a, AEStronglyMeasurable
      (fun r => (2*normalGaussianKernel r x)*A r) μ :=
    Filter.Eventually.of_forall fun x =>
      ((normalGaussianKernel_time_measurable x).const_mul 2).aestronglyMeasurable.mul hAm
  have hInt : Integrable (fun r => (2*normalGaussianKernel r a)*A r) μ :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le ht).mp
      (normalTraceLayer_hasDerivAt hB hF ht ha.le ξ).1
  have hDMeas : AEStronglyMeasurable (fun r => -normalPoissonKernel a r*A r) μ :=
    ((normalPoissonKernel_measurable a).neg.aestronglyMeasurable).mul hAm
  have hBound : ∀ᵐ r ∂μ, ∀ x ∈ Metric.ball a (a/2),
      ‖-normalPoissonKernel x r*A r‖ ≤ D r := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    intro x hx
    have hxabs : |x-a| < a/2 := by simpa only [Metric.mem_ball,Real.dist_eq] using hx
    have hax : a/2 ≤ x := by linarith [(abs_lt.mp hxabs).1]
    have hxa : x ≤ 3*(a/2) := by linarith [(abs_lt.mp hxabs).2]
    have hx0 : 0 ≤ x := (show 0 ≤ a/2 by positivity).trans hax
    have hp := normalPoissonKernel_le_near hr.1 ha hax hxa
    have hHeat := heatAverage_bound hr.1
      (hB.comp (continuous_id.prodMk continuous_const)) (fun y => hF (y,t-r)) ξ
    rw [norm_mul,Real.norm_eq_abs,abs_neg,abs_of_nonneg (normalPoissonKernel_nonneg hx0 hr.1),
      Real.norm_eq_abs]
    calc
      _ ≤ normalPoissonKernel x r*F :=
        mul_le_mul_of_nonneg_left hHeat (normalPoissonKernel_nonneg hx0 hr.1)
      _ ≤ D r := by
        have h := mul_le_mul_of_nonneg_right hp hF0
        dsimp only [D]
        nlinarith
  have hPInt : Integrable (normalPoissonKernel (a/2)) (volume.restrict (Set.Ioi 0)) :=
    (normalPoissonKernel_probability (by positivity : 0 < a/2)).1
  have hDInt : Integrable D μ :=
    (hPInt.mono_measure hMeasure).const_mul (3*F)
  have hDeriv : ∀ᵐ r ∂μ, ∀ x ∈ Metric.ball a (a/2),
      HasDerivAt (fun y => (2*normalGaussianKernel r y)*A r)
        (-normalPoissonKernel x r*A r) x := by
    exact Filter.Eventually.of_forall fun r x _hx => by
      have hd := (normalHeatProfile_second_hasDerivAt r x).mul_const (A r)
      rwa [normalHeatProfile_deriv] at hd
  obtain ⟨hi,hd⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ) (s := Metric.ball a (a/2)) (x₀ := a)
    (Metric.ball_mem_nhds a (by positivity)) hMeas hInt hDMeas hBound hDInt hDeriv
  have hPositive : Integrable (fun r => normalPoissonKernel a r*A r) μ := by
    convert hi.neg using 1
    funext r
    change normalPoissonKernel a r*A r = -(-normalPoissonKernel a r*A r)
    ring
  refine ⟨(intervalIntegrable_iff_integrableOn_Ioc_of_le ht).mpr hPositive,?_⟩
  have hFun : normalTraceFirst B ξ t =
      (fun x => ∫ r, (2*normalGaussianKernel r x)*A r ∂μ) := by
    funext x
    rw [normalTraceFirst,intervalIntegral.integral_of_le ht]
  have hValue : -(∫ r in (0 : ℝ)..t, normalPoissonKernel a r*A r) =
      ∫ r, -normalPoissonKernel a r*A r ∂μ := by
    rw [intervalIntegral.integral_of_le ht,← integral_neg]
    congr 1
    funext r
    ring
  rw [hFun]
  change HasDerivAt _ (-(∫ r in (0 : ℝ)..t, normalPoissonKernel a r*A r)) a
  rw [hValue]
  exact hd

/-- A zero-past source turns the finite-age integral into the true Poisson average. -/
theorem finite_tracePoisson_eq_average {n : ℕ} {a t : ℝ} {B : Point n → ℝ}
    (ha : 0 < a) (ht : 0 ≤ t) (hPast : ∀ y s, s ≤ 0 → B (y,s) = 0)
    (ξ : Space n) :
    (∫ r in (0 : ℝ)..t, normalPoissonKernel a r*
      heatAverage r (fun y => B (y,t-r)) ξ) = tracePoissonAverage a B (ξ,t) := by
  rw [tracePoissonAverage,ite_eq_right ha.ne',intervalIntegral.integral_of_le ht]
  symm
  apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
    (show Set.Ioc (0 : ℝ) t ⊆ Set.Ioi 0 from fun _ hr => hr.1)
  intro r hr
  have htr : t ≤ r := by
    by_contra h
    exact hr.2 ⟨hr.1,(lt_of_not_ge h).le⟩
  have hZero : (fun y => B (y,t-r)) = (0 : Space n → ℝ) := by
    funext y
    exact hPast y (t-r) (sub_nonpos.mpr htr)
  rw [hZero,heatAverage_def]
  simp

/-- For a zero-past source, the actual second normal derivative is minus
    the genuine parabolic Poisson average. -/
theorem normalTraceFirst_hasDerivAt_poisson {n : ℕ} {F t a : ℝ} {B : Point n → ℝ}
    (hB : Continuous B) (hF : ∀ p, |B p| ≤ F) (ht : 0 ≤ t) (ha : 0 < a)
    (hPast : ∀ y s, s ≤ 0 → B (y,s) = 0) (ξ : Space n) :
    HasDerivAt (normalTraceFirst B ξ t) (-tracePoissonAverage a B (ξ,t)) a := by
  have h := (normalTraceFirst_hasDerivAt hB hF ht ha ξ).2
  rwa [finite_tracePoisson_eq_average ha ht hPast ξ] at h

/-- The pre-existing Holder normal-jet field is an actual derivative of the
    first normal trace-layer derivative at every strict-half-space point. -/
theorem normalTraceFirst_hasDerivAt_boundaryJet {n : ℕ} {α T F : ℝ}
    (hα : 0 < α) (hT : 0 ≤ T) {B : Point n → ℝ}
    (hB : HolderBound α (cylinder Set.univ 0 T) B F)
    (hB0 : ∀ x, B (x,0) = 0) (e : Space n) {p : Point n}
    (hp : 0 < inner ℝ e p.1) (ht : 0 ≤ p.2) :
    HasDerivAt (normalTraceFirst (tracePastExtension T B)
      (halfSpaceBoundaryProjection e p.1) p.2)
      (boundaryTraceNormalJet e T B p) (inner ℝ e p.1) := by
  have hGlobal := tracePastExtension_holder hα.le hT hB
  have hCont := continuousOn_univ.mp (holderBound_continuousOn hα hGlobal)
  exact normalTraceFirst_hasDerivAt_poisson hCont
    (fun q => hGlobal.2.1 q (Set.mem_univ _)) ht hp
    (fun y s hs => tracePastExtension_zero_past hB0 hs) _

/-- The first normal derivative remains continuous across the normal face;
    its next derivative is taken one-sided there. -/
theorem normalTraceFirst_continuous {n : ℕ} {F t : ℝ} {B : Point n → ℝ}
    (hB : Continuous B) (hF : ∀ p, |B p| ≤ F) (ht : 0 ≤ t) (ξ : Space n) :
    Continuous (normalTraceFirst B ξ t) := by
  let μ : Measure ℝ := volume.restrict (Set.Ioc 0 t)
  let A : ℝ → ℝ := fun r => heatAverage r (fun y => B (y,t-r)) ξ
  let C : ℝ := 2*(Real.sqrt (4*Real.pi))⁻¹
  let D : ℝ → ℝ := fun r => (C*F)*r^(-(1/2 : ℝ))
  have hF0 : 0 ≤ F := (abs_nonneg (B (0,0))).trans (hF (0,0))
  have hMeasure : μ ≤ volume.restrict (Set.Ioi (0 : ℝ)) :=
    Measure.restrict_mono_set volume (fun _ hr => hr.1)
  have hAm : AEStronglyMeasurable A μ :=
    (retardedHeatAverage_aestronglyMeasurable hB (ξ,t)).mono_measure hMeasure
  have hMeas (x : ℝ) : AEStronglyMeasurable
      (fun r => (2*normalGaussianKernel r x)*A r) μ :=
    ((normalGaussianKernel_time_measurable x).const_mul 2).aestronglyMeasurable.mul hAm
  have hBound (x : ℝ) : ∀ᵐ r ∂μ, ‖(2*normalGaussianKernel r x)*A r‖ ≤ D r := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    have hHeat := heatAverage_bound hr.1
      (hB.comp (continuous_id.prodMk continuous_const)) (fun y => hF (y,t-r)) ξ
    have hGauss := normalGaussianKernel_le_rpow hr.1 x
    have hPos : 0 ≤ 2*normalGaussianKernel r x :=
      mul_nonneg (by norm_num) (normalGaussianKernel_pos hr.1 x).le
    rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg hPos]
    calc
      _ ≤ (2*normalGaussianKernel r x)*F := mul_le_mul_of_nonneg_left hHeat hPos
      _ ≤ D r := by
        have h := mul_le_mul_of_nonneg_right hGauss (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hF0)
        dsimp only [D,C]
        convert h using 1 <;> ring
  have hPower : IntervalIntegrable (fun r : ℝ => r^(-(1/2 : ℝ))) volume 0 t :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  have hDInt : Integrable D μ :=
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le ht).mp hPower).const_mul (C*F)
  have hCont : ∀ᵐ r ∂μ, Continuous (fun x => (2*normalGaussianKernel r x)*A r) := by
    exact Filter.Eventually.of_forall fun r =>
      ((normalGaussianKernel_spatial_smooth r).continuous.const_mul 2).mul_const (A r)
  have h := continuous_of_dominated hMeas hBound hDInt hCont
  have hEq : normalTraceFirst B ξ t =
      (fun x => ∫ r, (2*normalGaussianKernel r x)*A r ∂μ) := by
    funext x
    rw [normalTraceFirst,intervalIntegral.integral_of_le ht]
  rwa [hEq]

/-- The Poisson average has the actual normal boundary limit given by its source. -/
theorem tracePoissonAverage_tendsto_normal_zero {n : ℕ} {α F : ℝ}
    (hα : 0 < α) (hα1 : α < 1) {B : Point n → ℝ}
    (hB : HolderBound α Set.univ B F) (p : Point n) :
    Tendsto (fun a => tracePoissonAverage a B p) (𝓝[>] (0 : ℝ)) (𝓝 (B p)) := by
  obtain ⟨C,hC,h⟩ := tracePoissonAverage_sub_source_bound (n := n) hα hα1
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hPow : Tendsto (fun a : ℝ => C*F*a^α) (𝓝[>] 0) (𝓝 0) := by
    simpa only [Real.zero_rpow hα.ne',mul_zero] using
      (((Real.continuous_rpow_const hα.le).tendsto (0 : ℝ)).mono_left
        nhdsWithin_le_nhds).const_mul (C*F)
  apply squeeze_zero' (Filter.Eventually.of_forall fun _ => norm_nonneg _) ?_ hPow
  filter_upwards [self_mem_nhdsWithin] with a ha
  simpa only [Real.norm_eq_abs] using h B F hB a ha.le p

/-- The normal second derivative at the face is the one-sided value `-B`.
    Only the actual initial trace compatibility is used. -/
theorem normalTraceFirst_hasDerivWithinAt_boundary {n : ℕ} {α T F t : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hT : 0 ≤ T) {B : Point n → ℝ}
    (hB : HolderBound α (cylinder Set.univ 0 T) B F)
    (hB0 : ∀ x, B (x,0) = 0) (ht : t ∈ Set.Icc 0 T) (ξ : Space n) :
    HasDerivWithinAt (normalTraceFirst (tracePastExtension T B) ξ t)
      (-B (ξ,t)) (Set.Ici 0) 0 := by
  let Bhat := tracePastExtension T B
  have hGlobal : HolderBound α Set.univ Bhat F := tracePastExtension_holder hα.le hT hB
  have hCont := continuousOn_univ.mp (holderBound_continuousOn hα hGlobal)
  have hSup (q : Point n) : |Bhat q| ≤ F := hGlobal.2.1 q (Set.mem_univ _)
  have hd (a : ℝ) (ha : 0 < a) := normalTraceFirst_hasDerivAt_poisson hCont hSup ht.1 ha
    (fun y s hs => tracePastExtension_zero_past hB0 hs) ξ
  apply hasDerivWithinAt_Ici_of_tendsto_deriv (s := Set.Ioi 0)
    (fun a ha => (hd a ha).differentiableAt.differentiableWithinAt)
    (normalTraceFirst_continuous hCont hSup ht.1 ξ).continuousAt.continuousWithinAt
    self_mem_nhdsWithin
  have hlim := (tracePoissonAverage_tendsto_normal_zero hα hα1 hGlobal (ξ,t)).neg
  have hEq : Bhat (ξ,t) = B (ξ,t) := tracePastExtension_eqOn T B ⟨Set.mem_univ _,ht⟩
  rw [hEq] at hlim
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with a ha
  exact (hd a ha).deriv.symm

end Yau.LeafProofs.L16Aux
