import spec.CHAIN.LeafObligations

open MeasureTheory Filter
open scoped Topology ENNReal ContDiff Convolution BoundedContinuousFunction

noncomputable section

namespace Yau.LeafProofs

/-- A finite amount of mass contains only finitely many atoms above a fixed
positive threshold. No local-finiteness instance is needed outside `K`. -/
theorem L08_finite_large_atoms {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] (μ : Measure α) (K : Set α)
    (hK : μ K < ⊤) {a : ENNReal} (ha : a ≠ 0) :
    Set.Finite {z | z ∈ K ∧ a ≤ μ {z}} := by
  by_contra h
  have hmass : μ {z | z ∈ K ∧ a ≤ μ {z}} = ⊤ :=
    Set.Infinite.meas_eq_top h ⟨a, ha, fun _ hz ↦ hz.2⟩
  have hle : μ {z | z ∈ K ∧ a ≤ μ {z}} ≤ μ K :=
    measure_mono fun _ hz ↦ hz.1
  rw [hmass] at hle
  exact (not_le_of_gt hK) hle

/-- The fourth component of L08, including its stated open-domain interface. -/
theorem L08_locallyFiniteLargeAtoms : LeafCandidates.LocallyFiniteLargeAtoms := by
  intro O μ _ hμ K hK hKO
  exact L08_finite_large_atoms μ K (hμ K hK hKO) one_ne_zero

/-- A density with respect to planar area has no point masses, even before
any smoothness or finite-mass assumption is imposed. -/
theorem L08_smoothRieszMeasure_singleton (u : ℂ → ℝ) (z₀ : ℂ) (R : ℝ) (z : ℂ) :
    LeafCandidates.smoothRieszMeasure u z₀ R {z} = 0 := by
  unfold LeafCandidates.smoothRieszMeasure
  exact measure_singleton z

/-- The concrete two-coordinate Laplacian preserves smoothness on open sets. -/
theorem L08_contDiffOn_realPlanarLaplacian {u : ℂ → ℝ} {O : Set ℂ}
    (hO : IsOpen O) (hu : ContDiffOn ℝ ∞ u O) :
    ContDiffOn ℝ ∞ (LeafCandidates.realPlanarLaplacian u) O := by
  have huC : ContDiffOn ℝ ∞ (fun z ↦ (u z : ℂ)) O :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn hu
  have hdu : ContDiffOn ℝ ∞ (fderiv ℝ (fun z ↦ (u z : ℂ))) O :=
    huC.fderiv_of_isOpen hO (by simp)
  have hd1 : ContDiffOn ℝ ∞ (fun z ↦ fderiv ℝ (fun z ↦ (u z : ℂ)) z 1) O :=
    hdu.clm_apply contDiffOn_const
  have hdI : ContDiffOn ℝ ∞ (fun z ↦ fderiv ℝ (fun z ↦ (u z : ℂ)) z Complex.I) O :=
    hdu.clm_apply contDiffOn_const
  exact Complex.reCLM.contDiff.comp_contDiffOn
    (((hd1.fderiv_of_isOpen hO (by simp)).clm_apply contDiffOn_const).add
      ((hdI.fderiv_of_isOpen hO (by simp)).clm_apply contDiffOn_const))

/-- Smoothness on a neighborhood of the closed disc makes its Riesz density
integrable, and hence gives the finite-mass part of the decomposition. -/
theorem L08_smoothRieszMeasure_finite {u : ℂ → ℝ} {z₀ : ℂ} {R : ℝ}
    {O : Set ℂ} (hO : IsOpen O) (hball : Metric.closedBall z₀ R ⊆ O)
    (hu : ContDiffOn ℝ ∞ u O) :
    LeafCandidates.smoothRieszMeasure u z₀ R Set.univ < ⊤ := by
  have hcont : ContinuousOn
      (fun z ↦ LeafCandidates.realPlanarLaplacian u z / (2 * Real.pi))
      (Metric.closedBall z₀ R) :=
    ((L08_contDiffOn_realPlanarLaplacian hO hu).continuousOn.div_const _).mono hball
  have hint : IntegrableOn
      (fun z ↦ LeafCandidates.realPlanarLaplacian u z / (2 * Real.pi))
      (Metric.ball z₀ R) volume :=
    (hcont.integrableOn_compact (isCompact_closedBall z₀ R)).mono_set Metric.ball_subset_closedBall
  unfold LeafCandidates.smoothRieszMeasure
  rw [restrict_withDensity measurableSet_ball]
  letI := isFiniteMeasure_withDensity_ofReal hint.hasFiniteIntegral
  exact measure_lt_top _ _

/-- The logarithmic Newton kernel is absolutely integrable on every planar
disc. In polar coordinates its radial integrand is the continuous function
`r * log r`, including at the origin. -/
theorem L08_integrableOn_log_norm_ball (R : ℝ) :
    IntegrableOn (fun w : ℂ ↦ Real.log ‖w‖) (Metric.ball 0 R) volume := by
  rw [integrableOn_fun_norm_addHaar (volume : Measure ℂ)]
  simpa [Complex.finrank_real_complex, smul_eq_mul] using
    (Real.continuous_mul_log.continuousOn.integrableOn_compact
      (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) R))).mono_set Set.Ioo_subset_Icc_self

/-- Translating the logarithmic singularity preserves local absolute
integrability with respect to planar area. -/
theorem L08_integrableOn_log_norm_sub_ball (z : ℂ) (R : ℝ) :
    IntegrableOn (fun w : ℂ ↦ Real.log ‖z - w‖) (Metric.ball z R) volume := by
  have h := ((volume : Measure ℂ).measurePreserving_sub_left z).integrableOn_comp_preimage
    (MeasurableEquiv.subLeft z).measurableEmbedding |>.mpr (L08_integrableOn_log_norm_ball R)
  simpa [Function.comp_def, Metric.ball, dist_eq_norm, norm_sub_rev] using h

/-- The singularity may lie anywhere relative to the integration disc. -/
theorem L08_integrableOn_log_norm_sub_disc (z z₀ : ℂ) (R : ℝ) :
    IntegrableOn (fun w : ℂ ↦ Real.log ‖z - w‖) (Metric.ball z₀ R) volume :=
  (L08_integrableOn_log_norm_sub_ball z (R + dist z₀ z)).mono_set
    (Metric.ball_subset_ball' le_rfl)

/-- Absolute integrability of the logarithmic potential against the actual
smooth Riesz measure. Smoothness bounds the density on the closed disc. -/
theorem L08_smoothRieszMeasure_integrable_log {u : ℂ → ℝ} {z₀ : ℂ} {R : ℝ}
    {O : Set ℂ} (hO : IsOpen O) (hball : Metric.closedBall z₀ R ⊆ O)
    (hu : ContDiffOn ℝ ∞ u O)
    (hΔ : ∀ w ∈ O, 0 ≤ LeafCandidates.realPlanarLaplacian u w) (z : ℂ) :
    Integrable (fun w ↦ Real.log ‖z - w‖) (LeafCandidates.smoothRieszMeasure u z₀ R) := by
  have hcont : ContinuousOn
      (fun w ↦ LeafCandidates.realPlanarLaplacian u w / (2 * Real.pi))
      (Metric.closedBall z₀ R) :=
    ((L08_contDiffOn_realPlanarLaplacian hO hu).continuousOn.div_const _).mono hball
  have hproduct := IntegrableOn.continuousOn_mul_of_subset hcont
    (L08_integrableOn_log_norm_sub_disc z z₀ R) (isCompact_closedBall z₀ R)
    measurableSet_ball Metric.ball_subset_closedBall
  unfold LeafCandidates.smoothRieszMeasure
  rw [restrict_withDensity measurableSet_ball]
  apply (integrable_withDensity_iff_integrable_smul₀'
    ((hcont.mono Metric.ball_subset_closedBall).aemeasurable measurableSet_ball).ennreal_ofReal
    (Filter.Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)).2
  apply hproduct.congr
  filter_upwards [self_mem_ae_restrict measurableSet_ball] with w hw
  have hnonneg : 0 ≤ LeafCandidates.realPlanarLaplacian u w / (2 * Real.pi) :=
    div_nonneg (hΔ w (hball (Metric.ball_subset_closedBall hw)))
      (mul_nonneg (by norm_num) Real.pi_pos.le)
  simp [ENNReal.toReal_ofReal hnonneg, smul_eq_mul]

/-- Local absolute integrability of the planar Newton kernel on the whole
plane, in the form required by the convolution calculus. -/
theorem L08_locallyIntegrable_log_norm :
    LocallyIntegrable (fun w : ℂ ↦ Real.log ‖w‖) volume := by
  rw [locallyIntegrable_iff]
  intro K hK
  obtain ⟨R, hR⟩ := hK.isBounded.subset_ball (0 : ℂ)
  exact (L08_integrableOn_log_norm_ball R).mono_set hR

/-- Moving derivatives to a compactly supported smooth density proves
smoothness of its Newton potential without differentiating the singular
kernel twice under the integral. -/
theorem L08_contDiff_logPotential_compact {f : ℂ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hsupp : HasCompactSupport f) :
    ContDiff ℝ ∞ (fun z : ℂ ↦ ∫ w, Real.log ‖z - w‖ * f w) := by
  have h := hsupp.contDiff_convolution_right (ContinuousLinearMap.mul ℝ ℝ)
    L08_locallyIntegrable_log_norm hf
  convert h using 1
  funext z
  rw [convolution_eq_swap]
  rfl

/-- Removing a neighborhood of its singularity makes the logarithmic kernel
smooth. This is used for the part of a Riesz potential away from an interior
evaluation point. -/
theorem L08_contDiff_cutoff_log_norm {χ : ℂ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hzero : χ =ᶠ[𝓝 0] 0) :
    ContDiff ℝ ∞ (fun w : ℂ ↦ χ w * Real.log ‖w‖) := by
  rw [contDiff_iff_contDiffAt]
  intro w
  by_cases hw : w = 0
  · subst w
    apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [hzero] with w hw
    simp [hw]
  · exact hχ.contDiffAt.mul
      ((contDiffAt_id.norm ℝ hw).log (norm_ne_zero_iff.mpr hw))

/-- A compactly supported smooth replacement for the logarithmic kernel on
any closed annulus separated from the origin. -/
theorem L08_exists_smooth_log_annulus {r T : ℝ} (hr : 0 < r) (hrT : r ≤ T) :
    ∃ k : ℂ → ℝ, ContDiff ℝ ∞ k ∧ HasCompactSupport k ∧
      ∀ w : ℂ, r ≤ ‖w‖ → ‖w‖ ≤ T → k w = Real.log ‖w‖ := by
  let small : ContDiffBump (0 : ℂ) :=
    { rIn := r / 2
      rOut := r
      rIn_pos := half_pos hr
      rIn_lt_rOut := half_lt_self hr }
  let large : ContDiffBump (0 : ℂ) :=
    { rIn := T
      rOut := T + 1
      rIn_pos := hr.trans_le hrT
      rIn_lt_rOut := lt_add_one T }
  let χ : ℂ → ℝ := fun w ↦ large w * (1 - small w)
  have hχ : ContDiff ℝ ∞ χ := large.contDiff.mul (contDiff_const.sub small.contDiff)
  have hzero : χ =ᶠ[𝓝 0] 0 := by
    filter_upwards [small.eventuallyEq_one] with w hw
    simp [χ, hw]
  refine ⟨fun w ↦ χ w * Real.log ‖w‖, L08_contDiff_cutoff_log_norm hχ hzero,
    large.hasCompactSupport.mul_right.mul_right, ?_⟩
  intro w hrw hwT
  have hs : small w = 0 := small.zero_of_le_dist (by simpa [small] using hrw)
  have hl : large w = 1 := large.one_of_mem_closedBall (by simpa [large] using hwT)
  simp [χ, hs, hl]

/-- The potential of an integrable compactly supported density is smooth
away from its support. Locally the kernel can be replaced by the smooth
compactly supported annulus kernel. -/
theorem L08_contDiffAt_logPotential_off_support {f : ℂ → ℝ}
    (hf : Integrable f volume) (hsupp : HasCompactSupport f) {x : ℂ}
    (hx : x ∉ tsupport f) :
    ContDiffAt ℝ ∞ (fun z : ℂ ↦ ∫ w, Real.log ‖z - w‖ * f w) x := by
  obtain ⟨d, hd, hds⟩ := Metric.isOpen_iff.mp (isClosed_tsupport f).isOpen_compl x hx
  obtain ⟨M, hM, hbound⟩ := hsupp.isBounded.exists_pos_norm_lt
  obtain ⟨k, hk, hksupp, hkeq⟩ := L08_exists_smooth_log_annulus (half_pos hd)
    (show d / 2 ≤ ‖x‖ + d + M by linarith [norm_nonneg x])
  have hconv := hksupp.contDiff_convolution_right (ContinuousLinearMap.mul ℝ ℝ)
    hf.locallyIntegrable hk
  apply hconv.contDiffAt.congr_of_eventuallyEq
  filter_upwards [Metric.ball_mem_nhds x (half_pos hd)] with y hy
  rw [convolution_def]
  apply integral_congr_ae
  filter_upwards with w
  by_cases hfw : f w = 0
  · simp [hfw]
  have hw : w ∈ tsupport f := subset_tsupport f hfw
  have hdist : d ≤ dist w x := by
    by_contra! hlt
    exact hds (Metric.mem_ball.mpr hlt) hw
  have hlow : d / 2 ≤ ‖y - w‖ := by
    have htri := dist_triangle w y x
    rw [dist_comm w y, dist_eq_norm y w] at htri
    have hy' := Metric.mem_ball.mp hy
    linarith
  have hupp : ‖y - w‖ ≤ ‖x‖ + d + M := by
    have htri := norm_sub_le y w
    have hy' : ‖y - x‖ < d / 2 := by simpa [dist_eq_norm] using hy
    have hyN := norm_add_le (y - x) x
    rw [sub_add_cancel] at hyN
    have hwM := hbound w hw
    linarith
  simp [hkeq (y - w) hlow hupp, mul_comm]

/-- Multiplication by a smooth cutoff supported inside a smoothness domain
gives a globally smooth function, regardless of the values outside that
domain. -/
theorem L08_contDiff_cutoff_mul {f χ : ℂ → ℝ} {O : Set ℂ}
    (hO : IsOpen O) (hf : ContDiffOn ℝ ∞ f O) (hχ : ContDiff ℝ ∞ χ)
    (hsupp : tsupport χ ⊆ O) :
    ContDiff ℝ ∞ (fun z ↦ χ z * f z) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z ∈ tsupport χ
  · exact hχ.contDiffAt.mul (hf.contDiffAt (hO.mem_nhds (hsupp hz)))
  · apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [(isClosed_tsupport χ).isOpen_compl.mem_nhds hz] with w hw
    simp [image_eq_zero_of_notMem_tsupport hw]

/-- A compactly supported smooth density gives an absolutely convergent
Newton integral at every point. -/
theorem L08_integrable_logPotential_compact {f : ℂ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hsupp : HasCompactSupport f) (z : ℂ) :
    Integrable (fun w ↦ Real.log ‖z - w‖ * f w) volume := by
  have h := hsupp.convolutionExists_left (ContinuousLinearMap.mul ℝ ℝ)
    hf.continuous L08_locallyIntegrable_log_norm z
  simpa [ConvolutionExistsAt, mul_comm] using h

/-- Localizing a density separates a smooth compactly supported near part
from a far part. The original density itself may have a jump at the boundary
of its compact support, as the Riesz density restricted to a disc does. -/
theorem L08_contDiffOn_logPotential {f : ℂ → ℝ} {O : Set ℂ}
    (hO : IsOpen O) (hf : ContDiffOn ℝ ∞ f O) (hfi : Integrable f volume)
    (hsupp : HasCompactSupport f)
    (hkernel : ∀ z ∈ O, Integrable (fun w ↦ Real.log ‖z - w‖ * f w) volume) :
    ContDiffOn ℝ ∞ (fun z : ℂ ↦ ∫ w, Real.log ‖z - w‖ * f w) O := by
  intro x hx
  obtain ⟨d, hd, hdO⟩ := Metric.isOpen_iff.mp hO x hx
  let φ : ContDiffBump x :=
    { rIn := d / 4
      rOut := d / 2
      rIn_pos := by positivity
      rIn_lt_rOut := by linarith }
  have hφO : tsupport φ ⊆ O := by
    rw [φ.tsupport_eq]
    exact (Metric.closedBall_subset_ball (show d / 2 < d by linarith)).trans hdO
  let g : ℂ → ℝ := fun w ↦ φ w * f w
  have hg : ContDiff ℝ ∞ g := L08_contDiff_cutoff_mul hO hf φ.contDiff hφO
  have hgs : HasCompactSupport g := φ.hasCompactSupport.mul_right
  have hgi : Integrable g volume := hg.continuous.integrable_of_hasCompactSupport hgs
  let q : ℂ → ℝ := f - g
  have hqi : Integrable q volume := hfi.sub hgi
  have hqs : HasCompactSupport q := hsupp.sub hgs
  have hxq : x ∉ tsupport q := by
    rw [notMem_tsupport_iff_eventuallyEq]
    filter_upwards [φ.eventuallyEq_one] with w hw
    simp [q, g, hw]
  have hnear := (L08_contDiff_logPotential_compact hg hgs).contDiffAt (x := x)
  have hfar := L08_contDiffAt_logPotential_off_support hqi hqs hxq
  apply ContDiffAt.contDiffWithinAt
  apply (hnear.add hfar).congr_of_eventuallyEq
  filter_upwards [hO.mem_nhds hx] with z hz
  have hIntg := L08_integrable_logPotential_compact hg hgs z
  have hIntq : Integrable (fun w ↦ Real.log ‖z - w‖ * q w) volume := by
    have hsub := (hkernel z hz).sub hIntg
    change Integrable
      (fun w ↦ Real.log ‖z - w‖ * f w - Real.log ‖z - w‖ * g w) volume at hsub
    simpa only [q, Pi.sub_apply, mul_sub] using hsub
  rw [← integral_add hIntg hIntq]
  apply integral_congr_ae
  filter_upwards with w
  simp [q, mul_sub]

/-- The measure-theoretic potential equals the ordinary weighted area
integral with the normalization fixed in L08. -/
theorem L08_smoothRieszMeasure_integral_log_eq {u : ℂ → ℝ} {z₀ : ℂ} {R : ℝ}
    {O : Set ℂ} (hO : IsOpen O) (hball : Metric.closedBall z₀ R ⊆ O)
    (hu : ContDiffOn ℝ ∞ u O)
    (hΔ : ∀ w ∈ O, 0 ≤ LeafCandidates.realPlanarLaplacian u w) (z : ℂ) :
    (∫ w, Real.log ‖z - w‖ ∂(LeafCandidates.smoothRieszMeasure u z₀ R)) =
      ∫ w in Metric.ball z₀ R,
        Real.log ‖z - w‖ * (LeafCandidates.realPlanarLaplacian u w / (2 * Real.pi)) := by
  have hcont := ((L08_contDiffOn_realPlanarLaplacian hO hu).continuousOn.div_const
    (2 * Real.pi)).mono (Metric.ball_subset_closedBall.trans hball)
  unfold LeafCandidates.smoothRieszMeasure
  rw [restrict_withDensity measurableSet_ball,
    integral_withDensity_eq_integral_toReal_smul₀
      (hcont.aemeasurable measurableSet_ball).ennreal_ofReal
      (Filter.Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards [self_mem_ae_restrict measurableSet_ball] with w hw
  have hnonneg : 0 ≤ LeafCandidates.realPlanarLaplacian u w / (2 * Real.pi) :=
    div_nonneg (hΔ w (hball (Metric.ball_subset_closedBall hw)))
      (mul_nonneg (by norm_num) Real.pi_pos.le)
  simp only [ENNReal.toReal_ofReal hnonneg, smul_eq_mul]
  exact mul_comm _ _

/-- Interior smoothness of the actual Riesz potential, including the jump
introduced by restricting its density to the open disc. -/
theorem L08_smoothRieszMeasure_contDiff_logPotential {u : ℂ → ℝ} {z₀ : ℂ} {R : ℝ}
    {O : Set ℂ} (hO : IsOpen O) (hball : Metric.closedBall z₀ R ⊆ O)
    (hu : ContDiffOn ℝ ∞ u O)
    (hΔ : ∀ w ∈ O, 0 ≤ LeafCandidates.realPlanarLaplacian u w) :
    ContDiffOn ℝ ∞
      (fun z : ℂ ↦ ∫ w, Real.log ‖z - w‖ ∂(LeafCandidates.smoothRieszMeasure u z₀ R))
      (Metric.ball z₀ R) := by
  let ρ : ℂ → ℝ := fun w ↦ LeafCandidates.realPlanarLaplacian u w / (2 * Real.pi)
  let f : ℂ → ℝ := (Metric.ball z₀ R).indicator ρ
  have hρ : ContDiffOn ℝ ∞ ρ O := (L08_contDiffOn_realPlanarLaplacian hO hu).div_const _
  have hρc : ContinuousOn ρ (Metric.closedBall z₀ R) := hρ.continuousOn.mono hball
  have hf : ContDiffOn ℝ ∞ f (Metric.ball z₀ R) := by
    apply (hρ.mono (Metric.ball_subset_closedBall.trans hball)).congr
    intro w hw
    exact Set.indicator_of_mem hw ρ
  have hfi : Integrable f volume :=
    (integrable_indicator_iff measurableSet_ball).2
      ((hρc.integrableOn_compact (isCompact_closedBall z₀ R)).mono_set
        Metric.ball_subset_closedBall)
  have hfs : HasCompactSupport f := by
    apply (isCompact_closedBall z₀ R).of_isClosed_subset (isClosed_tsupport f)
    apply Metric.isClosed_closedBall.closure_subset_iff.mpr
    intro w hw
    by_contra hwb
    have hnotball : w ∉ Metric.ball z₀ R := fun h ↦ hwb (Metric.ball_subset_closedBall h)
    exact hw (Set.indicator_of_notMem hnotball ρ)
  have hkernel (z : ℂ) : Integrable (fun w ↦ Real.log ‖z - w‖ * f w) volume := by
    have hprod := (L08_integrableOn_log_norm_sub_disc z z₀ R).mul_continuousOn_of_subset
      hρc measurableSet_ball (isCompact_closedBall z₀ R) Metric.ball_subset_closedBall
    have hInd := (integrable_indicator_iff measurableSet_ball).2 hprod
    convert hInd using 1
    funext w
    exact (Set.indicator_mul_right (Metric.ball z₀ R) (fun w ↦ Real.log ‖z - w‖) ρ).symm
  have heq (z : ℂ) :
      (∫ w, Real.log ‖z - w‖ ∂(LeafCandidates.smoothRieszMeasure u z₀ R)) =
        ∫ w, Real.log ‖z - w‖ * f w := by
    rw [L08_smoothRieszMeasure_integral_log_eq hO hball hu hΔ z,
      ← integral_indicator measurableSet_ball]
    apply integral_congr_ae
    filter_upwards with w
    exact Set.indicator_mul_right (Metric.ball z₀ R) (fun w ↦ Real.log ‖z - w‖) ρ
  exact (L08_contDiffOn_logPotential Metric.isOpen_ball hf hfi hfs
    (fun z _ ↦ hkernel z)).congr (fun z _ ↦ heq z)

/-- Compatibility of the frozen coordinate formula with Mathlib's
Euclidean Laplacian. -/
theorem L08_planarLaplacian_eq_laplacian {f : ℂ → ℂ} {z : ℂ}
    (hf : ContDiffAt ℝ 2 f z) :
    LeafCandidates.planarLaplacian f z = Laplacian.laplacian f z := by
  have hdf : DifferentiableAt ℝ (fderiv ℝ f) z :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  unfold LeafCandidates.planarLaplacian
  rw [fderiv_clm_apply hdf (differentiableAt_const (1 : ℂ)),
    fderiv_clm_apply hdf (differentiableAt_const Complex.I)]
  simp [InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane,
    iteratedFDeriv_two_apply, ContinuousLinearMap.flip_apply]

/-- The real-valued Laplacian used by L08 has exactly the standard Euclidean
normalization. -/
theorem L08_realPlanarLaplacian_eq_laplacian {f : ℂ → ℝ} {z : ℂ}
    (hf : ContDiffAt ℝ 2 f z) :
    LeafCandidates.realPlanarLaplacian f z = Laplacian.laplacian f z := by
  have hC : ContDiffAt ℝ 2 (fun w ↦ (f w : ℂ)) z :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp z hf
  unfold LeafCandidates.realPlanarLaplacian
  rw [L08_planarLaplacian_eq_laplacian hC]
  have h := congrArg Complex.re (hf.laplacian_CLM_comp_left (l := Complex.ofRealCLM))
  simpa [Function.comp_def] using h

/-- The logarithmic kernel is harmonic off its singularity; the missing
normalization at the singularity is handled separately by the fundamental
solution argument. -/
theorem L08_realPlanarLaplacian_log_norm_sub {z w : ℂ} (hzw : z ≠ w) :
    LeafCandidates.realPlanarLaplacian (fun y ↦ Real.log ‖y - w‖) z = 0 := by
  have h := (show AnalyticAt ℂ (fun y : ℂ ↦ y - w) z by fun_prop).harmonicAt_log_norm
    (sub_ne_zero.mpr hzw)
  rw [L08_realPlanarLaplacian_eq_laplacian h.1]
  exact h.2.eq_of_nhds

/-- Upper semicontinuity and exclusion of positive infinity give genuine
real upper bounds on every compact subset of the subharmonicity domain. -/
theorem L08_subharmonic_bddAbove {O K : Set ℂ} {u : ℂ → EReal}
    (hu : LeafCandidates.DiscSubharmonic O u) (hK : IsCompact K) (hKO : K ⊆ O) :
    ∃ C : ℝ, ∀ z ∈ K, u z ≤ (C : EReal) := by
  rcases K.eq_empty_or_nonempty with h | hne
  · exact ⟨0, fun _ hz ↦ (h ▸ hz).elim⟩
  obtain ⟨x, hx, hmax⟩ := (hu.2.1.mono hKO).exists_isMaxOn hne hK
  obtain ⟨C, hC, _⟩ := EReal.exists_between_coe_real (hu.1 x (hKO hx))
  exact ⟨C, fun z hz ↦ (hmax hz).trans hC.le⟩

/-- Multiplying the Newton kernel by any continuous compactly supported
function gives an absolutely integrable function. -/
theorem L08_integrable_log_mul_compact {g : ℂ → ℝ} (hg : Continuous g)
    (hsupp : HasCompactSupport g) :
    Integrable (fun w : ℂ ↦ Real.log ‖w‖ * g w) volume := by
  simpa only [smul_eq_mul] using
    L08_locallyIntegrable_log_norm.integrable_smul_right_of_hasCompactSupport hg hsupp

/-- The Newton potential is the convolution with the logarithmic kernel,
written in the order that places derivatives on the density. -/
theorem L08_logPotential_eq_convolution (f : ℂ → ℝ) :
    (fun z : ℂ ↦ ∫ w, Real.log ‖z - w‖ * f w) =
      (fun w : ℂ ↦ Real.log ‖w‖) ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] f := by
  funext z
  rw [convolution_eq_swap]
  rfl

/-- The directional derivative of a smooth compactly supported Newton
potential is the potential of the corresponding density derivative. -/
theorem L08_fderiv_logPotential_compact {f : ℂ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hsupp : HasCompactSupport f) (v z : ℂ) :
    fderiv ℝ (fun z : ℂ ↦ ∫ w, Real.log ‖z - w‖ * f w) z v =
      ∫ w, Real.log ‖z - w‖ * fderiv ℝ f w v := by
  rw [L08_logPotential_eq_convolution,
    (hsupp.hasFDerivAt_convolution_right (ContinuousLinearMap.mul ℝ ℝ)
      L08_locallyIntegrable_log_norm (hf.of_le (by simp)) z).fderiv]
  rw [convolution_precompR_apply (ContinuousLinearMap.mul ℝ ℝ)
    L08_locallyIntegrable_log_norm (hsupp.fderiv ℝ) (hf.continuous_fderiv (by simp))]
  rw [← L08_logPotential_eq_convolution]

/-- The frozen real operator is the sum of the two actual real directional
second derivatives. -/
theorem L08_realPlanarLaplacian_eq_directions {f : ℂ → ℝ} {z : ℂ}
    (hf : ContDiffAt ℝ 2 f z) :
    LeafCandidates.realPlanarLaplacian f z =
      fderiv ℝ (fun w ↦ fderiv ℝ f w 1) z 1 +
        fderiv ℝ (fun w ↦ fderiv ℝ f w Complex.I) z Complex.I := by
  rw [L08_realPlanarLaplacian_eq_laplacian hf]
  have hdf : DifferentiableAt ℝ (fderiv ℝ f) z :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  rw [fderiv_clm_apply hdf (differentiableAt_const (1 : ℂ)),
    fderiv_clm_apply hdf (differentiableAt_const Complex.I)]
  simp [InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane,
    iteratedFDeriv_two_apply, ContinuousLinearMap.flip_apply]

/-- Both derivatives of the Newton potential can be transferred to its
smooth compactly supported density. The logarithmic kernel is never
differentiated in this identity. -/
theorem L08_realPlanarLaplacian_logPotential_compact {f : ℂ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hsupp : HasCompactSupport f) (z : ℂ) :
    LeafCandidates.realPlanarLaplacian (fun z : ℂ ↦ ∫ w, Real.log ‖z - w‖ * f w) z =
      ∫ w, Real.log ‖z - w‖ * LeafCandidates.realPlanarLaplacian f w := by
  let p : ℂ → ℝ := fun z ↦ ∫ w, Real.log ‖z - w‖ * f w
  let d1 : ℂ → ℝ := fun w ↦ fderiv ℝ f w 1
  let dI : ℂ → ℝ := fun w ↦ fderiv ℝ f w Complex.I
  have hd1 : ContDiff ℝ ∞ d1 := (hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hdI : ContDiff ℝ ∞ dI := (hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hs1 : HasCompactSupport d1 := hsupp.fderiv_apply ℝ 1
  have hsI : HasCompactSupport dI := hsupp.fderiv_apply ℝ Complex.I
  have heq1 : (fun y ↦ fderiv ℝ p y 1) =
      (fun y ↦ ∫ w, Real.log ‖y - w‖ * d1 w) :=
    funext fun y ↦ L08_fderiv_logPotential_compact hf hsupp 1 y
  have heqI : (fun y ↦ fderiv ℝ p y Complex.I) =
      (fun y ↦ ∫ w, Real.log ‖y - w‖ * dI w) :=
    funext fun y ↦ L08_fderiv_logPotential_compact hf hsupp Complex.I y
  have hInt1 : Integrable (fun w ↦ Real.log ‖z - w‖ * fderiv ℝ d1 w 1) volume :=
    L08_integrable_logPotential_compact
      ((hd1.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const) (hs1.fderiv_apply ℝ 1) z
  have hIntI : Integrable (fun w ↦ Real.log ‖z - w‖ * fderiv ℝ dI w Complex.I) volume :=
    L08_integrable_logPotential_compact
      ((hdI.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const)
      (hsI.fderiv_apply ℝ Complex.I) z
  change LeafCandidates.realPlanarLaplacian p z = _
  rw [L08_realPlanarLaplacian_eq_directions
    ((L08_contDiff_logPotential_compact hf hsupp).contDiffAt.of_le (by simp))]
  rw [heq1, heqI, L08_fderiv_logPotential_compact hd1 hs1 1 z,
    L08_fderiv_logPotential_compact hdI hsI Complex.I z, ← integral_add hInt1 hIntI]
  apply integral_congr_ae
  filter_upwards with w
  rw [L08_realPlanarLaplacian_eq_directions (hf.contDiffAt.of_le (by simp))]
  dsimp only [d1, dI]
  ring

/-- Polar integration on an annulus, with the angular interval and area
Jacobian explicit. The angle interval has length exactly `2 * π`. -/
theorem L08_integral_annulus_polar {a b : ℝ} (ha : 0 < a) (hab : a < b)
    {h : ℂ → ℝ}
    (hh : ContinuousOn h {w : ℂ | a ≤ ‖w‖ ∧ ‖w‖ ≤ b}) :
    (∫ w in {w : ℂ | a < ‖w‖ ∧ ‖w‖ < b}, h w) =
      ∫ r in Set.Ioo a b, ∫ θ in Set.Ioo (-Real.pi) Real.pi,
        r * h ((r : ℂ) * (Real.cos θ + Real.sin θ * Complex.I)) := by
  let A : Set ℂ := {w | a < ‖w‖ ∧ ‖w‖ < b}
  let D : Set (ℝ × ℝ) := Set.Ioo a b ×ˢ Set.Ioo (-Real.pi) Real.pi
  let G : ℝ × ℝ → ℝ := fun p ↦ p.1 * h (Complex.polarCoord.symm p)
  have hA : MeasurableSet A :=
    ((isOpen_lt continuous_const continuous_norm).inter
      (isOpen_lt continuous_norm continuous_const)).measurableSet
  have hpcont : Continuous (fun p : ℝ × ℝ ↦ Complex.polarCoord.symm p) := by
    simp only [Complex.polarCoord_symm_apply]
    fun_prop
  have hG : ContinuousOn G (Set.Icc a b ×ˢ Set.Icc (-Real.pi) Real.pi) := by
    apply continuousOn_fst.mul (hh.comp hpcont.continuousOn ?_)
    intro p hp
    change a ≤ ‖Complex.polarCoord.symm p‖ ∧ ‖Complex.polarCoord.symm p‖ ≤ b
    rw [Complex.norm_polarCoord_symm, abs_of_pos (ha.trans_le hp.1.1)]
    exact hp.1
  have hInt : IntegrableOn G D volume :=
    (hG.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
      (Set.prod_mono Set.Ioo_subset_Icc_self Set.Ioo_subset_Icc_self)
  have hchange : (∫ w in A, h w) = ∫ p in D, G p := by
    rw [← integral_indicator hA, ← Complex.integral_comp_polarCoord_symm]
    change (∫ p in polarCoord.target,
      p.1 * A.indicator h (Complex.polarCoord.symm p)) = ∫ p in D, G p
    have htarget : MeasurableSet polarCoord.target := measurableSet_Ioi.prod measurableSet_Ioo
    have hD : MeasurableSet D := measurableSet_Ioo.prod measurableSet_Ioo
    rw [← integral_indicator htarget, ← integral_indicator hD]
    apply integral_congr_ae
    filter_upwards with p
    by_cases hpD : p ∈ D
    · have hpT : p ∈ polarCoord.target := ⟨ha.trans hpD.1.1, hpD.2⟩
      have hpA : Complex.polarCoord.symm p ∈ A := by
        change a < ‖Complex.polarCoord.symm p‖ ∧ ‖Complex.polarCoord.symm p‖ < b
        rw [Complex.norm_polarCoord_symm, abs_of_pos (ha.trans hpD.1.1)]
        exact hpD.1
      rw [Set.indicator_of_mem hpT, Set.indicator_of_mem hpD, Set.indicator_of_mem hpA]
    · by_cases hpT : p ∈ polarCoord.target
      · have hpA : Complex.polarCoord.symm p ∉ A := by
          intro hpA
          apply hpD
          refine ⟨?_, hpT.2⟩
          change a < p.1 ∧ p.1 < b
          simpa only [A, Set.mem_ofPred_eq, Complex.norm_polarCoord_symm,
            abs_of_pos (show 0 < p.1 from hpT.1)] using hpA
        rw [Set.indicator_of_mem hpT, Set.indicator_of_notMem hpD,
          Set.indicator_of_notMem hpA, mul_zero]
      · rw [Set.indicator_of_notMem hpT, Set.indicator_of_notMem hpD]
  rw [hchange]
  rw [Measure.volume_eq_prod] at hInt ⊢
  rw [setIntegral_prod _ hInt]
  simp only [G, Complex.polarCoord_symm_apply]

/-- Differentiation of a compact angular integral. Joint continuity of the
integrand and its parameter derivative supplies a common bound on a compact
parameter neighborhood. -/
theorem L08_hasDerivAt_intervalIntegral {F F' : ℝ → ℝ → ℝ}
    (hF : Continuous (fun p : ℝ × ℝ ↦ F p.1 p.2))
    (hF' : Continuous (fun p : ℝ × ℝ ↦ F' p.1 p.2))
    (hderiv : ∀ r θ : ℝ, HasDerivAt (fun s ↦ F s θ) (F' r θ) r)
    (a b r₀ : ℝ) :
    HasDerivAt (fun r ↦ ∫ θ in a..b, F r θ) (∫ θ in a..b, F' r₀ θ) r₀ := by
  have hFc (r : ℝ) : Continuous (F r) := hF.comp (continuous_const.prodMk continuous_id)
  have hF'c (r : ℝ) : Continuous (F' r) := hF'.comp (continuous_const.prodMk continuous_id)
  obtain ⟨C, hC⟩ := ((isCompact_closedBall r₀ 1).prod isCompact_uIcc).exists_bound_of_continuousOn
    hF'.continuousOn
  apply (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s := Metric.ball r₀ 1) (bound := fun _ ↦ C) (Metric.ball_mem_nhds r₀ zero_lt_one)
    (Filter.Eventually.of_forall fun r ↦ (hFc r).aestronglyMeasurable.restrict)
    ((hFc r₀).intervalIntegrable a b) ((hF'c r₀).aestronglyMeasurable.restrict)
    (Filter.Eventually.of_forall fun θ hθ r hr ↦
      hC (r, θ) ⟨Metric.ball_subset_closedBall hr, Set.uIoc_subset_uIcc hθ⟩)
    (intervalIntegrable_const)
    (Filter.Eventually.of_forall fun θ _ r _ ↦ hderiv r θ)).2

/-- The standard positively oriented unit circle. -/
def L08_unitCircle (θ : ℝ) : ℂ := Complex.exp ((θ : ℂ) * Complex.I)

theorem L08_continuous_unitCircle : Continuous L08_unitCircle := by
  unfold L08_unitCircle
  fun_prop

theorem L08_hasDerivAt_unitCircle (θ : ℝ) :
    HasDerivAt L08_unitCircle (L08_unitCircle θ * Complex.I) θ := by
  have heq : L08_unitCircle = circleMap (0 : ℂ) 1 := by
    funext t
    simp [L08_unitCircle, circleMap]
  rw [heq]
  exact hasDerivAt_circleMap 0 1 θ

theorem L08_norm_unitCircle (θ : ℝ) : ‖L08_unitCircle θ‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I θ

def L08_angularIntegral (φ : ℂ → ℝ) (r : ℝ) : ℝ :=
  ∫ θ in (-Real.pi)..Real.pi, φ (r • L08_unitCircle θ)

def L08_angularRadialDerivative (φ : ℂ → ℝ) (r : ℝ) : ℝ :=
  ∫ θ in (-Real.pi)..Real.pi, fderiv ℝ φ (r • L08_unitCircle θ) (L08_unitCircle θ)

def L08_angularRadialSecondDerivative (φ : ℂ → ℝ) (r : ℝ) : ℝ :=
  ∫ θ in (-Real.pi)..Real.pi,
    fderiv ℝ (fderiv ℝ φ) (r • L08_unitCircle θ) (L08_unitCircle θ) (L08_unitCircle θ)

/-- First radial differentiation under the compact angular integral. -/
theorem L08_hasDerivAt_angularIntegral {φ : ℂ → ℝ} (hφ : ContDiff ℝ ∞ φ) (r : ℝ) :
    HasDerivAt (L08_angularIntegral φ) (L08_angularRadialDerivative φ r) r := by
  have hpath : Continuous (fun p : ℝ × ℝ ↦ p.1 • L08_unitCircle p.2) :=
    continuous_fst.smul (L08_continuous_unitCircle.comp continuous_snd)
  have hdφ : Continuous (fderiv ℝ φ) := hφ.continuous_fderiv (by simp)
  apply L08_hasDerivAt_intervalIntegral (hφ.continuous.comp hpath)
    ((hdφ.comp hpath).clm_apply (L08_continuous_unitCircle.comp continuous_snd))
    (fun s θ ↦ ?_) (-Real.pi) Real.pi r
  convert (hφ.differentiable (by simp) (s • L08_unitCircle θ)).hasFDerivAt.comp_hasDerivAt s
    ((hasDerivAt_id s).smul_const (L08_unitCircle θ)) using 1 <;>
    simp only [Function.comp_def, one_smul, id_eq]

/-- Second radial differentiation, again differentiating the smooth
density rather than the logarithmic kernel. -/
theorem L08_hasDerivAt_angularRadialDerivative {φ : ℂ → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (r : ℝ) :
    HasDerivAt (L08_angularRadialDerivative φ)
      (L08_angularRadialSecondDerivative φ r) r := by
  have hpath : Continuous (fun p : ℝ × ℝ ↦ p.1 • L08_unitCircle p.2) :=
    continuous_fst.smul (L08_continuous_unitCircle.comp continuous_snd)
  have hdφ : ContDiff ℝ ∞ (fderiv ℝ φ) := hφ.fderiv_right (by simp)
  have hq : Continuous (fun p : ℝ × ℝ ↦ L08_unitCircle p.2) :=
    L08_continuous_unitCircle.comp continuous_snd
  apply L08_hasDerivAt_intervalIntegral
    ((hdφ.continuous.comp hpath).clm_apply hq)
    (((hdφ.continuous_fderiv (by simp)).comp hpath).clm_apply hq |>.clm_apply hq)
    (fun s θ ↦ ?_) (-Real.pi) Real.pi r
  have hderiv := (hdφ.differentiable (by simp) (s • L08_unitCircle θ)).hasFDerivAt.comp_hasDerivAt s
    ((hasDerivAt_id s).smul_const (L08_unitCircle θ))
  convert hderiv.clm_apply (hasDerivAt_const s (L08_unitCircle θ)) using 1 <;>
    simp only [Function.comp_def, one_smul, id_eq, ContinuousLinearMap.map_zero, add_zero]

/-- The unit-circle parameter in the real basis `(1, I)`. -/
theorem L08_unitCircle_eq (θ : ℝ) :
    L08_unitCircle θ = Real.cos θ • (1 : ℂ) + Real.sin θ • Complex.I := by
  simp [L08_unitCircle, Complex.exp_ofReal_mul_I, Complex.real_smul]

/-- Rotation by a right angle in the same real basis. -/
theorem L08_unitCircle_mul_I_eq (θ : ℝ) :
    L08_unitCircle θ * Complex.I =
      (-Real.sin θ) • (1 : ℂ) + Real.cos θ • Complex.I := by
  rw [L08_unitCircle_eq]
  simp only [Complex.real_smul, mul_one, add_mul, mul_assoc, ← pow_two, Complex.I_sq,
    mul_neg, mul_one, Complex.ofReal_neg]
  ring

/-- The trace of a real bilinear form is unchanged by the circle rotation.
The mixed terms cancel without assuming symmetry of the bilinear form. -/
theorem L08_bilinear_circle_trace (B : ℂ →L[ℝ] ℂ →L[ℝ] ℝ) (θ : ℝ) :
    B (L08_unitCircle θ) (L08_unitCircle θ) +
        B (L08_unitCircle θ * Complex.I) (L08_unitCircle θ * Complex.I) =
      B 1 1 + B Complex.I Complex.I := by
  rw [L08_unitCircle_mul_I_eq, L08_unitCircle_eq]
  simp only [map_add, map_smul, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul]
  calc
    _ = (Real.cos θ ^ 2 + Real.sin θ ^ 2) * (B 1 1 + B Complex.I Complex.I) := by ring
    _ = B 1 1 + B Complex.I Complex.I := by rw [Real.cos_sq_add_sin_sq]; ring

/-- A concrete second angular derivative of the unit circle. -/
theorem L08_hasDerivAt_unitCircle_tangent (θ : ℝ) :
    HasDerivAt (fun t ↦ L08_unitCircle t * Complex.I) (-L08_unitCircle θ) θ := by
  simpa only [mul_assoc, ← pow_two, Complex.I_sq, mul_neg, mul_one] using
    (L08_hasDerivAt_unitCircle θ).mul_const Complex.I

/-- The angular derivative of the first angular derivative of a smooth
function restricted to a circle. -/
theorem L08_hasDerivAt_angularTangent {φ : ℂ → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (r θ : ℝ) :
    HasDerivAt
      (fun t ↦ fderiv ℝ φ (r • L08_unitCircle t) (r • (L08_unitCircle t * Complex.I)))
      (r ^ 2 * fderiv ℝ (fderiv ℝ φ) (r • L08_unitCircle θ)
          (L08_unitCircle θ * Complex.I) (L08_unitCircle θ * Complex.I) -
        r * fderiv ℝ φ (r • L08_unitCircle θ) (L08_unitCircle θ)) θ := by
  have hdφ : ContDiff ℝ ∞ (fderiv ℝ φ) := hφ.fderiv_right (by simp)
  have hcurve := (L08_hasDerivAt_unitCircle θ).const_smul r
  have htangent := (L08_hasDerivAt_unitCircle_tangent θ).const_smul r
  have hD := (hdφ.differentiable (by simp) (r • L08_unitCircle θ)).hasFDerivAt.comp_hasDerivAt θ hcurve
  convert hD.clm_apply htangent using 1 <;>
    simp only [Function.comp_def, Pi.smul_apply, map_smul, smul_apply, smul_eq_mul, map_neg] <;> ring

/-- The angular integral of the Laplacian equals the second radial
derivative plus the first radial derivative divided by the radius. The
angular second derivative integrates to zero by the matching endpoint
tangents of the circle parameter. -/
theorem L08_angular_laplacian {φ : ℂ → ℝ} (hφ : ContDiff ℝ ∞ φ)
    {r : ℝ} (hr : 0 < r) :
    (∫ θ in (-Real.pi)..Real.pi,
      LeafCandidates.realPlanarLaplacian φ (r • L08_unitCircle θ)) =
      L08_angularRadialSecondDerivative φ r + L08_angularRadialDerivative φ r / r := by
  let N : ℝ → ℝ := fun θ ↦ fderiv ℝ φ (r • L08_unitCircle θ) (L08_unitCircle θ)
  let T : ℝ → ℝ := fun θ ↦ fderiv ℝ (fderiv ℝ φ) (r • L08_unitCircle θ)
    (L08_unitCircle θ * Complex.I) (L08_unitCircle θ * Complex.I)
  let R : ℝ → ℝ := fun θ ↦ fderiv ℝ (fderiv ℝ φ) (r • L08_unitCircle θ)
    (L08_unitCircle θ) (L08_unitCircle θ)
  have hdφ : ContDiff ℝ ∞ (fderiv ℝ φ) := hφ.fderiv_right (by simp)
  have hpath : Continuous (fun θ ↦ r • L08_unitCircle θ) :=
    L08_continuous_unitCircle.const_smul r
  have hqI : Continuous (fun θ ↦ L08_unitCircle θ * Complex.I) :=
    L08_continuous_unitCircle.mul_const _
  have hN : Continuous N := (hdφ.continuous.comp hpath).clm_apply L08_continuous_unitCircle
  have hT : Continuous T :=
    ((hdφ.continuous_fderiv (by simp)).comp hpath).clm_apply hqI |>.clm_apply hqI
  have hR : Continuous R :=
    ((hdφ.continuous_fderiv (by simp)).comp hpath).clm_apply L08_continuous_unitCircle |>.clm_apply
      L08_continuous_unitCircle
  have hzero : (∫ θ in (-Real.pi)..Real.pi, r ^ 2 * T θ - r * N θ) = 0 := by
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (a := -Real.pi) (b := Real.pi)
      (fun θ _ ↦ L08_hasDerivAt_angularTangent hφ r θ)
      (((hT.const_mul (r ^ 2)).sub (hN.const_mul r)).intervalIntegrable _ _)
    have hqend : L08_unitCircle Real.pi = L08_unitCircle (-Real.pi) := by
      simp [L08_unitCircle, Complex.exp_ofReal_mul_I]
    simpa only [T, N, hqend, sub_self] using hFTC
  have htrace (θ : ℝ) :
      LeafCandidates.realPlanarLaplacian φ (r • L08_unitCircle θ) = R θ + T θ := by
    rw [L08_realPlanarLaplacian_eq_laplacian (hφ.contDiffAt.of_le (by simp)),
      InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane]
    simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one]
    exact (L08_bilinear_circle_trace (fderiv ℝ (fderiv ℝ φ) (r • L08_unitCircle θ)) θ).symm
  calc
    _ = ∫ θ in (-Real.pi)..Real.pi, R θ + T θ :=
      intervalIntegral.integral_congr fun θ _ ↦ htrace θ
    _ = (∫ θ in (-Real.pi)..Real.pi, R θ) + ∫ θ in (-Real.pi)..Real.pi, T θ :=
      intervalIntegral.integral_add (hR.intervalIntegrable _ _) (hT.intervalIntegrable _ _)
    _ = L08_angularRadialSecondDerivative φ r + L08_angularRadialDerivative φ r / r := by
      change (∫ θ in (-Real.pi)..Real.pi, R θ) + (∫ θ in (-Real.pi)..Real.pi, T θ) =
        (∫ θ in (-Real.pi)..Real.pi, R θ) + (∫ θ in (-Real.pi)..Real.pi, N θ) / r
      congr 1
      apply (eq_div_iff hr.ne').2
      rw [intervalIntegral.integral_sub ((hT.const_mul (r ^ 2)).intervalIntegrable _ _)
        ((hN.const_mul r).intervalIntegrable _ _), intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul] at hzero
      apply mul_left_cancel₀ hr.ne'
      nlinarith only [hzero]

theorem L08_continuous_angularRadialSecondDerivative {φ : ℂ → ℝ}
    (hφ : ContDiff ℝ ∞ φ) : Continuous (L08_angularRadialSecondDerivative φ) := by
  have hdφ : ContDiff ℝ ∞ (fderiv ℝ φ) := hφ.fderiv_right (by simp)
  have hpath : Continuous (fun p : ℝ × ℝ ↦ p.1 • L08_unitCircle p.2) :=
    continuous_fst.smul (L08_continuous_unitCircle.comp continuous_snd)
  have hq : Continuous (fun p : ℝ × ℝ ↦ L08_unitCircle p.2) :=
    L08_continuous_unitCircle.comp continuous_snd
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (((hdφ.continuous_fderiv (by simp)).comp hpath).clm_apply hq |>.clm_apply hq)
    (-Real.pi) Real.pi

/-- The radial primitive used in the annulus calculation. -/
theorem L08_hasDerivAt_logBoundary {φ : ℂ → ℝ} (hφ : ContDiff ℝ ∞ φ)
    {r : ℝ} (hr : 0 < r) :
    HasDerivAt
      (fun s ↦ s * Real.log s * L08_angularRadialDerivative φ s - L08_angularIntegral φ s)
      (Real.log r * (r * L08_angularRadialSecondDerivative φ r +
        L08_angularRadialDerivative φ r)) r := by
  have h := (((hasDerivAt_id r).mul (Real.hasDerivAt_log hr.ne')).mul
    (L08_hasDerivAt_angularRadialDerivative hφ r)).sub (L08_hasDerivAt_angularIntegral hφ r)
  convert h using 1
  · rfl
  · simp only [id_eq, Pi.mul_apply, one_mul, mul_inv_cancel₀ hr.ne']
    ring

/-- The exact annular Green identity needed for the logarithmic fundamental
solution, derived from polar integration and one-dimensional calculus. Both
boundary circles retain their contributions. -/
theorem L08_log_laplacian_annulus {φ : ℂ → ℝ} (hφ : ContDiff ℝ ∞ φ)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    (∫ w in {w : ℂ | a < ‖w‖ ∧ ‖w‖ < b},
      Real.log ‖w‖ * LeafCandidates.realPlanarLaplacian φ w) =
      (b * Real.log b * L08_angularRadialDerivative φ b - L08_angularIntegral φ b) -
        (a * Real.log a * L08_angularRadialDerivative φ a - L08_angularIntegral φ a) := by
  have hLc : Continuous (LeafCandidates.realPlanarLaplacian φ) :=
    continuousOn_univ.mp
      (L08_contDiffOn_realPlanarLaplacian isOpen_univ hφ.contDiffOn).continuousOn
  have hh : ContinuousOn
      (fun w : ℂ ↦ Real.log ‖w‖ * LeafCandidates.realPlanarLaplacian φ w)
      {w : ℂ | a ≤ ‖w‖ ∧ ‖w‖ ≤ b} :=
    (continuous_norm.continuousOn.log (fun w hw ↦ (ha.trans_le hw.1).ne')).mul hLc.continuousOn
  have hangle (g : ℝ → ℝ) :
      (∫ θ in Set.Ioo (-Real.pi) Real.pi, g θ) = ∫ θ in (-Real.pi)..Real.pi, g θ := by
    rw [intervalIntegral.integral_of_le (by linarith [Real.pi_pos]), integral_Ioc_eq_integral_Ioo]
  have hBc : Continuous (L08_angularRadialDerivative φ) :=
    continuous_iff_continuousAt.mpr fun r ↦ (L08_hasDerivAt_angularRadialDerivative hφ r).continuousAt
  have hCc := L08_continuous_angularRadialSecondDerivative hφ
  have hint : IntervalIntegrable
      (fun r ↦ Real.log r * (r * L08_angularRadialSecondDerivative φ r +
        L08_angularRadialDerivative φ r)) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hab.le]
    exact (continuousOn_id.log (fun r hr ↦ (ha.trans_le hr.1).ne')).mul
      ((continuousOn_id.mul hCc.continuousOn).add hBc.continuousOn)
  calc
    _ = ∫ r in Set.Ioo a b,
        Real.log r * (r * L08_angularRadialSecondDerivative φ r +
          L08_angularRadialDerivative φ r) := by
      rw [L08_integral_annulus_polar ha hab hh]
      apply setIntegral_congr_fun measurableSet_Ioo
      intro r hr
      have hr0 : 0 < r := ha.trans hr.1
      calc
        _ = ∫ θ in Set.Ioo (-Real.pi) Real.pi,
            (r * Real.log r) * LeafCandidates.realPlanarLaplacian φ (r • L08_unitCircle θ) := by
          apply setIntegral_congr_fun measurableSet_Ioo
          intro θ _
          have hq : L08_unitCircle θ = Real.cos θ + Real.sin θ * Complex.I :=
            Complex.exp_ofReal_mul_I θ
          dsimp only
          rw [← hq, ← Complex.real_smul, norm_smul, L08_norm_unitCircle,
            Real.norm_eq_abs, abs_of_pos hr0, mul_one]
          ring
        _ = (r * Real.log r) * ∫ θ in Set.Ioo (-Real.pi) Real.pi,
            LeafCandidates.realPlanarLaplacian φ (r • L08_unitCircle θ) := by
          rw [integral_const_mul]
        _ = (r * Real.log r) * (L08_angularRadialSecondDerivative φ r +
            L08_angularRadialDerivative φ r / r) := by
          rw [hangle, L08_angular_laplacian hφ hr0]
        _ = Real.log r * (r * L08_angularRadialSecondDerivative φ r +
            L08_angularRadialDerivative φ r) := by field_simp [hr0.ne']
    _ = ∫ r in a..b, Real.log r * (r * L08_angularRadialSecondDerivative φ r +
        L08_angularRadialDerivative φ r) := by
      rw [intervalIntegral.integral_of_le hab.le, integral_Ioc_eq_integral_Ioo]
    _ = _ := by
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ hint
      intro r hr
      have hra : a ≤ r := (show r ∈ Set.Icc a b by simpa [Set.uIcc_of_le hab.le] using hr).1
      exact L08_hasDerivAt_logBoundary hφ (ha.trans_le hra)

theorem L08_contDiff_realPlanarLaplacian {φ : ℂ → ℝ} (hφ : ContDiff ℝ ∞ φ) :
    ContDiff ℝ ∞ (LeafCandidates.realPlanarLaplacian φ) :=
  contDiffOn_univ.mp (L08_contDiffOn_realPlanarLaplacian isOpen_univ hφ.contDiffOn)

/-- Taking the genuine Laplacian creates no support outside the original
function's support. -/
theorem L08_tsupport_realPlanarLaplacian_subset {φ : ℂ → ℝ} (hφ : ContDiff ℝ ∞ φ) :
    tsupport (LeafCandidates.realPlanarLaplacian φ) ⊆ tsupport φ := by
  change closure (Function.support (LeafCandidates.realPlanarLaplacian φ)) ⊆ tsupport φ
  apply (isClosed_tsupport φ).closure_subset_iff.mpr
  intro z hz
  by_contra hzφ
  apply hz
  rw [L08_realPlanarLaplacian_eq_directions (hφ.contDiffAt.of_le (by simp))]
  have hz1 : z ∉ tsupport (fun w ↦ fderiv ℝ φ w 1) :=
    fun h ↦ hzφ (tsupport_fderiv_apply_subset ℝ (1 : ℂ) h)
  have hzI : z ∉ tsupport (fun w ↦ fderiv ℝ φ w Complex.I) :=
    fun h ↦ hzφ (tsupport_fderiv_apply_subset ℝ Complex.I h)
  rw [fderiv_of_notMem_tsupport ℝ hz1, fderiv_of_notMem_tsupport ℝ hzI]
  simp

theorem L08_hasCompactSupport_realPlanarLaplacian {φ : ℂ → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hsupp : HasCompactSupport φ) :
    HasCompactSupport (LeafCandidates.realPlanarLaplacian φ) :=
  hsupp.of_isClosed_subset (isClosed_tsupport _) (L08_tsupport_realPlanarLaplacian_subset hφ)

theorem L08_integrable_log_laplacian {φ : ℂ → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hsupp : HasCompactSupport φ) :
    Integrable (fun w : ℂ ↦ Real.log ‖w‖ * LeafCandidates.realPlanarLaplacian φ w) volume :=
  L08_integrable_log_mul_compact (L08_contDiff_realPlanarLaplacian hφ).continuous
    (L08_hasCompactSupport_realPlanarLaplacian hφ hsupp)

/-- The inner-circle contribution converges to the correct positive mass.
Continuity of `r * log r` at zero removes the remaining boundary term. -/
theorem L08_tendsto_inner_logBoundary {φ : ℂ → ℝ} (hφ : ContDiff ℝ ∞ φ) :
    Tendsto
      (fun r ↦ L08_angularIntegral φ r - r * Real.log r * L08_angularRadialDerivative φ r)
      (𝓝 0) (𝓝 (2 * Real.pi * φ 0)) := by
  have hAc : Continuous (L08_angularIntegral φ) :=
    continuous_iff_continuousAt.mpr fun r ↦ (L08_hasDerivAt_angularIntegral hφ r).continuousAt
  have hBc : Continuous (L08_angularRadialDerivative φ) :=
    continuous_iff_continuousAt.mpr fun r ↦ (L08_hasDerivAt_angularRadialDerivative hφ r).continuousAt
  have hcont := hAc.sub (Real.continuous_mul_log.mul hBc)
  have hzero : L08_angularIntegral φ 0 - 0 * Real.log 0 * L08_angularRadialDerivative φ 0 =
      2 * Real.pi * φ 0 := by
    simp only [L08_angularIntegral, zero_smul, intervalIntegral.integral_const,
      sub_neg_eq_add, smul_eq_mul, zero_mul, sub_zero]
    ring
  rw [← hzero]
  exact hcont.tendsto 0

/-- Outside the support, both outer-circle terms vanish exactly. -/
theorem L08_angular_outer_eq_zero {φ : ℂ → ℝ} {R : ℝ} (hR : 0 < R)
    (hsupp : tsupport φ ⊆ Metric.ball 0 R) :
    L08_angularIntegral φ R = 0 ∧ L08_angularRadialDerivative φ R = 0 := by
  have hout (θ : ℝ) : R • L08_unitCircle θ ∉ tsupport φ := by
    intro h
    have hb := hsupp h
    have hnorm : ‖R • L08_unitCircle θ‖ = R := by
      rw [norm_smul, L08_norm_unitCircle, Real.norm_eq_abs, abs_of_pos hR, mul_one]
    have hlt : R < R := by simpa only [Metric.mem_ball, dist_zero_right, hnorm] using hb
    exact lt_irrefl R hlt
  have hφzero (θ : ℝ) : φ (R • L08_unitCircle θ) = 0 :=
    image_eq_zero_of_notMem_tsupport (hout θ)
  have hDzero (θ : ℝ) : fderiv ℝ φ (R • L08_unitCircle θ) (L08_unitCircle θ) = 0 := by
    rw [fderiv_of_notMem_tsupport ℝ (hout θ)]
    rfl
  constructor
  · simp only [L08_angularIntegral, hφzero, intervalIntegral.integral_zero]
  · simp only [L08_angularRadialDerivative, hDzero, intervalIntegral.integral_zero]

/-- Removing a shrinking inner disc from an integrable function does not
change its integral in the limit. The outer truncation already lies outside
the function's support. -/
theorem L08_tendsto_annulus_integral {g : ℂ → ℝ} {R : ℝ} (hg : Integrable g volume)
    (hg0 : g 0 = 0) (hout : ∀ w : ℂ, R ≤ ‖w‖ → g w = 0) :
    Tendsto (fun ε : ℝ ↦ ∫ w in {w : ℂ | ε < ‖w‖ ∧ ‖w‖ < R}, g w)
      (𝓝 0) (𝓝 (∫ w, g w)) := by
  let F : ℝ → ℂ → ℝ := fun ε ↦ {w : ℂ | ε < ‖w‖ ∧ ‖w‖ < R}.indicator g
  have hA (ε : ℝ) : MeasurableSet {w : ℂ | ε < ‖w‖ ∧ ‖w‖ < R} :=
    ((isOpen_lt continuous_const continuous_norm).inter
      (isOpen_lt continuous_norm continuous_const)).measurableSet
  have hlim : ∀ w : ℂ, Tendsto (fun ε : ℝ ↦ F ε w) (𝓝 0) (𝓝 (g w)) := by
    intro w
    by_cases hwg : g w = 0
    · refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
      exact Filter.Eventually.of_forall fun ε ↦ by simp [F, hwg, Set.indicator]
    have hw0 : w ≠ 0 := fun h ↦ hwg (h ▸ hg0)
    have hwR : ‖w‖ < R := lt_of_not_ge fun h ↦ hwg (hout w h)
    have hε : ∀ᶠ ε : ℝ in 𝓝 0, ε < ‖w‖ := isOpen_Iio.mem_nhds (norm_pos_iff.mpr hw0)
    refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [hε] with ε hε
    have hwA : w ∈ {w : ℂ | ε < ‖w‖ ∧ ‖w‖ < R} := ⟨hε, hwR⟩
    exact (Set.indicator_of_mem hwA g).symm
  have hDCT := tendsto_integral_filter_of_dominated_convergence (fun w ↦ ‖g w‖)
    (Filter.Eventually.of_forall fun ε ↦ hg.aestronglyMeasurable.indicator (hA ε))
    (Filter.Eventually.of_forall fun ε ↦ ae_of_all volume fun w ↦ norm_indicator_le_norm_self g w)
    hg.norm (ae_of_all volume hlim)
  convert hDCT using 1
  funext ε
  exact (integral_indicator (hA ε)).symm

/-- The planar logarithmic fundamental-solution identity, proved on smooth
compactly supported test functions. The normalization is the one in the
frozen L08 statement. -/
theorem L08_log_fundamental_solution {φ : ℂ → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hsupp : HasCompactSupport φ) :
    (∫ w : ℂ, Real.log ‖w‖ * LeafCandidates.realPlanarLaplacian φ w) =
      2 * Real.pi * φ 0 := by
  obtain ⟨R, hR, hbound⟩ := hsupp.isBounded.exists_pos_norm_lt
  have hsuppR : tsupport φ ⊆ Metric.ball 0 R := by
    intro w hw
    simpa only [Metric.mem_ball, dist_zero_right] using hbound w hw
  let J : ℂ → ℝ := fun w ↦ Real.log ‖w‖ * LeafCandidates.realPlanarLaplacian φ w
  have hJ : Integrable J volume := L08_integrable_log_laplacian hφ hsupp
  have hJ0 : J 0 = 0 := by simp [J]
  have hJout : ∀ w : ℂ, R ≤ ‖w‖ → J w = 0 := by
    intro w hw
    have hwnot : w ∉ tsupport φ := by
      intro h
      exact (not_lt_of_ge hw) (hbound w h)
    have hwnotL : w ∉ tsupport (LeafCandidates.realPlanarLaplacian φ) :=
      fun h ↦ hwnot (L08_tsupport_realPlanarLaplacian_subset hφ h)
    simp only [J, image_eq_zero_of_notMem_tsupport hwnotL, mul_zero]
  have hIntegral := (L08_tendsto_annulus_integral hJ hJ0 hJout).mono_left
    (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
  have hBoundary := (L08_tendsto_inner_logBoundary hφ).mono_left
    (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
  have hOuter := L08_angular_outer_eq_zero hR hsuppR
  have hεpos : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < ε := self_mem_nhdsWithin
  have hεR : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε < R :=
    (show ∀ᶠ ε : ℝ in 𝓝 0, ε < R from isOpen_Iio.mem_nhds hR).filter_mono nhdsWithin_le_nhds
  have heq : (fun ε : ℝ ↦ ∫ w in {w : ℂ | ε < ‖w‖ ∧ ‖w‖ < R}, J w) =ᶠ[𝓝[>] 0]
      (fun ε ↦ L08_angularIntegral φ ε - ε * Real.log ε * L08_angularRadialDerivative φ ε) := by
    filter_upwards [hεpos, hεR] with ε hε hεR
    change (∫ w in {w : ℂ | ε < ‖w‖ ∧ ‖w‖ < R},
      Real.log ‖w‖ * LeafCandidates.realPlanarLaplacian φ w) = _
    rw [L08_log_laplacian_annulus hφ hε hεR, hOuter.1, hOuter.2]
    ring
  exact tendsto_nhds_unique (hIntegral.congr' heq) hBoundary

/-- Translation leaves the concrete real planar Laplacian unchanged. -/
theorem L08_realPlanarLaplacian_comp_add_left {f : ℂ → ℝ}
    (hf : ContDiff ℝ ∞ f) (z w : ℂ) :
    LeafCandidates.realPlanarLaplacian (fun u ↦ f (z + u)) w =
      LeafCandidates.realPlanarLaplacian f (z + w) := by
  have hcomp : ContDiff ℝ ∞ (fun u : ℂ ↦ f (z + u)) :=
    hf.comp (contDiff_const.add contDiff_id)
  rw [L08_realPlanarLaplacian_eq_laplacian (hcomp.contDiffAt.of_le (by simp)),
    L08_realPlanarLaplacian_eq_laplacian (hf.contDiffAt.of_le (by simp))]
  simp only [InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane,
    iteratedFDeriv_comp_add_left]

/-- The full compact-density Newton potential has precisely the required
Laplacian, including its mass on the diagonal. -/
theorem L08_realPlanarLaplacian_logPotential_compact_eq {f : ℂ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hsupp : HasCompactSupport f) (z : ℂ) :
    LeafCandidates.realPlanarLaplacian (fun z : ℂ ↦ ∫ w, Real.log ‖z - w‖ * f w) z =
      2 * Real.pi * f z := by
  have hcomp : ContDiff ℝ ∞ (fun u : ℂ ↦ f (z + u)) :=
    hf.comp (contDiff_const.add contDiff_id)
  have hscomp : HasCompactSupport (fun u : ℂ ↦ f (z + u)) :=
    hsupp.comp_homeomorph (Homeomorph.addLeft z)
  have hfund := L08_log_fundamental_solution hcomp hscomp
  simp only [L08_realPlanarLaplacian_comp_add_left hf z, add_zero] at hfund
  rw [L08_realPlanarLaplacian_logPotential_compact hf hsupp z]
  calc
    _ = ∫ u : ℂ, Real.log ‖u‖ * LeafCandidates.realPlanarLaplacian f (z + u) := by
      simpa only [sub_add_eq_sub_sub, sub_self, zero_sub, norm_neg] using
        (integral_add_left_eq_self
          (fun w : ℂ ↦ Real.log ‖z - w‖ * LeafCandidates.realPlanarLaplacian f w) z).symm
    _ = 2 * Real.pi * f z := hfund

/-- Directional differentiation of an arbitrary locally integrable kernel
convolved with a compactly supported smooth function. -/
theorem L08_fderiv_convolution_right {f g : ℂ → ℝ} (hf : LocallyIntegrable f volume)
    (hg : ContDiff ℝ ∞ g) (hsupp : HasCompactSupport g) (v z : ℂ) :
    fderiv ℝ (f ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] g) z v =
      (f ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] (fun w ↦ fderiv ℝ g w v)) z := by
  rw [(hsupp.hasFDerivAt_convolution_right (ContinuousLinearMap.mul ℝ ℝ)
    hf (hg.of_le (by simp)) z).fderiv]
  exact convolution_precompR_apply (ContinuousLinearMap.mul ℝ ℝ) hf
    (hsupp.fderiv ℝ) (hg.continuous_fderiv (by simp)) z v

/-- The Laplacian may be transferred to the smooth compact factor of a
convolution with a merely locally integrable factor. -/
theorem L08_realPlanarLaplacian_convolution_right {f g : ℂ → ℝ}
    (hf : LocallyIntegrable f volume) (hg : ContDiff ℝ ∞ g) (hsupp : HasCompactSupport g)
    (z : ℂ) :
    LeafCandidates.realPlanarLaplacian (f ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] g) z =
      (f ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] LeafCandidates.realPlanarLaplacian g) z := by
  let d1 : ℂ → ℝ := fun w ↦ fderiv ℝ g w 1
  let dI : ℂ → ℝ := fun w ↦ fderiv ℝ g w Complex.I
  have hd1 : ContDiff ℝ ∞ d1 := (hg.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hdI : ContDiff ℝ ∞ dI := (hg.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hs1 : HasCompactSupport d1 := hsupp.fderiv_apply ℝ 1
  have hsI : HasCompactSupport dI := hsupp.fderiv_apply ℝ Complex.I
  have heq1 : (fun y ↦ fderiv ℝ (f ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] g) y 1) =
      f ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] d1 :=
    funext fun y ↦ L08_fderiv_convolution_right hf hg hsupp 1 y
  have heqI : (fun y ↦ fderiv ℝ (f ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] g) y Complex.I) =
      f ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] dI :=
    funext fun y ↦ L08_fderiv_convolution_right hf hg hsupp Complex.I y
  have hd11 : ContDiff ℝ ∞ (fun w ↦ fderiv ℝ d1 w 1) :=
    (hd1.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hdII : ContDiff ℝ ∞ (fun w ↦ fderiv ℝ dI w Complex.I) :=
    (hdI.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hconv1 := (hs1.fderiv_apply ℝ (1 : ℂ)).convolutionExists_right
    (ContinuousLinearMap.mul ℝ ℝ) hf hd11.continuous z
  have hconvI := (hsI.fderiv_apply ℝ Complex.I).convolutionExists_right
    (ContinuousLinearMap.mul ℝ ℝ) hf hdII.continuous z
  have hsum : (fun w ↦ fderiv ℝ d1 w 1) + (fun w ↦ fderiv ℝ dI w Complex.I) =
      LeafCandidates.realPlanarLaplacian g := by
    funext w
    exact (L08_realPlanarLaplacian_eq_directions (hg.contDiffAt.of_le (by simp))).symm
  rw [L08_realPlanarLaplacian_eq_directions
    ((hsupp.contDiff_convolution_right (ContinuousLinearMap.mul ℝ ℝ) hf hg).contDiffAt.of_le (by simp))]
  rw [heq1, heqI, L08_fderiv_convolution_right hf hd1 hs1 1 z,
    L08_fderiv_convolution_right hf hdI hsI Complex.I z, ← hconv1.distrib_add hconvI, hsum]

/-- The frozen Laplacian depends only on the germ of a function. -/
theorem L08_realPlanarLaplacian_congr_nhds {f g : ℂ → ℝ} {z : ℂ}
    (h : f =ᶠ[𝓝 z] g) :
    LeafCandidates.realPlanarLaplacian f z = LeafCandidates.realPlanarLaplacian g z := by
  have hc : (fun w ↦ (f w : ℂ)) =ᶠ[𝓝 z] (fun w ↦ (g w : ℂ)) :=
    h.fun_comp (fun r : ℝ ↦ (r : ℂ))
  have hd := hc.fderiv (𝕜 := ℝ)
  have h1 := hd.fun_comp (fun L : ℂ →L[ℝ] ℂ ↦ L 1)
  have hI := hd.fun_comp (fun L : ℂ →L[ℝ] ℂ ↦ L Complex.I)
  simp only [Function.comp_def] at h1 hI
  unfold LeafCandidates.realPlanarLaplacian LeafCandidates.planarLaplacian
  rw [(h1.fderiv (𝕜 := ℝ)).eq_of_nhds, (hI.fderiv (𝕜 := ℝ)).eq_of_nhds]

/-- The far part of an integrable compactly supported density has a
harmonic Newton potential. The smooth annulus cutoff permits all derivatives
to be taken on a compact smooth kernel. -/
theorem L08_realPlanarLaplacian_logPotential_off_support {f : ℂ → ℝ}
    (hf : Integrable f volume) (hsupp : HasCompactSupport f) {x : ℂ}
    (hx : x ∉ tsupport f) :
    LeafCandidates.realPlanarLaplacian (fun z : ℂ ↦ ∫ w, Real.log ‖z - w‖ * f w) x = 0 := by
  obtain ⟨d, hd, hds⟩ := Metric.isOpen_iff.mp (isClosed_tsupport f).isOpen_compl x hx
  obtain ⟨M, hM, hbound⟩ := hsupp.isBounded.exists_pos_norm_lt
  obtain ⟨k, hk, hksupp, hkeq⟩ := L08_exists_smooth_log_annulus (half_pos hd)
    (show d / 2 ≤ ‖x‖ + d + M by linarith [norm_nonneg x])
  have hdist {w : ℂ} (hw : w ∈ tsupport f) : d ≤ dist w x := by
    by_contra! hlt
    exact hds (Metric.mem_ball.mpr hlt) hw
  have heq : (fun z : ℂ ↦ ∫ w, Real.log ‖z - w‖ * f w) =ᶠ[𝓝 x]
      f ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] k := by
    filter_upwards [Metric.ball_mem_nhds x (half_pos hd)] with y hy
    rw [convolution_def]
    apply integral_congr_ae
    filter_upwards with w
    by_cases hfw : f w = 0
    · simp [hfw]
    have hw : w ∈ tsupport f := subset_tsupport f hfw
    have hlow : d / 2 ≤ ‖y - w‖ := by
      have htri := dist_triangle w y x
      rw [dist_comm w y, dist_eq_norm y w] at htri
      have hy' := Metric.mem_ball.mp hy
      linarith [hdist hw]
    have hupp : ‖y - w‖ ≤ ‖x‖ + d + M := by
      have htri := norm_sub_le y w
      have hy' : ‖y - x‖ < d / 2 := by simpa [dist_eq_norm] using hy
      have hyN := norm_add_le (y - x) x
      rw [sub_add_cancel] at hyN
      have hwM := hbound w hw
      linarith
    simp [hkeq (y - w) hlow hupp, mul_comm]
  rw [L08_realPlanarLaplacian_congr_nhds heq,
    L08_realPlanarLaplacian_convolution_right hf.locallyIntegrable hk hksupp x, convolution_def]
  apply integral_eq_zero_of_ae
  filter_upwards with w
  by_cases hfw : f w = 0
  · simp [hfw]
  have hw : w ∈ tsupport f := subset_tsupport f hfw
  have hlow : d / 2 < ‖x - w‖ := by
    have hdistw := hdist hw
    rw [dist_comm w x, dist_eq_norm x w] at hdistw
    linarith
  have hupp : ‖x - w‖ < ‖x‖ + d + M := by
    have htri := norm_sub_le x w
    have hwM := hbound w hw
    linarith
  have hS : IsOpen {u : ℂ | d / 2 < ‖u‖ ∧ ‖u‖ < ‖x‖ + d + M} :=
    (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)
  have heqk : k =ᶠ[𝓝 (x - w)] (fun u : ℂ ↦ Real.log ‖u‖) := by
    filter_upwards [hS.mem_nhds ⟨hlow, hupp⟩] with u hu
    exact hkeq u hu.1.le hu.2.le
  have hnonzero : x - w ≠ 0 := norm_pos_iff.mp ((half_pos hd).trans hlow)
  have hlog : LeafCandidates.realPlanarLaplacian (fun u : ℂ ↦ Real.log ‖u‖) (x - w) = 0 := by
    simpa only [sub_zero] using L08_realPlanarLaplacian_log_norm_sub (w := 0) hnonzero
  simp only [ContinuousLinearMap.mul_apply', L08_realPlanarLaplacian_congr_nhds heqk,
    hlog, mul_zero, Pi.zero_apply]

theorem L08_realPlanarLaplacian_add {f g : ℂ → ℝ} {z : ℂ}
    (hf : ContDiffAt ℝ 2 f z) (hg : ContDiffAt ℝ 2 g z) :
    LeafCandidates.realPlanarLaplacian (fun w ↦ f w + g w) z =
      LeafCandidates.realPlanarLaplacian f z + LeafCandidates.realPlanarLaplacian g z := by
  rw [L08_realPlanarLaplacian_eq_laplacian (hf.add hg),
    L08_realPlanarLaplacian_eq_laplacian hf, L08_realPlanarLaplacian_eq_laplacian hg]
  exact hf.laplacian_add hg

theorem L08_realPlanarLaplacian_sub {f g : ℂ → ℝ} {z : ℂ}
    (hf : ContDiffAt ℝ 2 f z) (hg : ContDiffAt ℝ 2 g z) :
    LeafCandidates.realPlanarLaplacian (fun w ↦ f w - g w) z =
      LeafCandidates.realPlanarLaplacian f z - LeafCandidates.realPlanarLaplacian g z := by
  rw [L08_realPlanarLaplacian_eq_laplacian (hf.sub hg),
    L08_realPlanarLaplacian_eq_laplacian hf, L08_realPlanarLaplacian_eq_laplacian hg]
  exact hf.laplacian_sub hg

/-- The fundamental-solution equation remains valid wherever the density
is smooth, even when the density has jumps elsewhere on its compact support. -/
theorem L08_realPlanarLaplacian_logPotential {f : ℂ → ℝ} {O : Set ℂ}
    (hO : IsOpen O) (hf : ContDiffOn ℝ ∞ f O) (hfi : Integrable f volume)
    (hsupp : HasCompactSupport f)
    (hkernel : ∀ z ∈ O, Integrable (fun w ↦ Real.log ‖z - w‖ * f w) volume)
    {x : ℂ} (hx : x ∈ O) :
    LeafCandidates.realPlanarLaplacian (fun z : ℂ ↦ ∫ w, Real.log ‖z - w‖ * f w) x =
      2 * Real.pi * f x := by
  obtain ⟨d, hd, hdO⟩ := Metric.isOpen_iff.mp hO x hx
  let φ : ContDiffBump x :=
    { rIn := d / 4
      rOut := d / 2
      rIn_pos := by positivity
      rIn_lt_rOut := by linarith }
  have hφO : tsupport φ ⊆ O := by
    rw [φ.tsupport_eq]
    exact (Metric.closedBall_subset_ball (show d / 2 < d by linarith)).trans hdO
  let g : ℂ → ℝ := fun w ↦ φ w * f w
  have hg : ContDiff ℝ ∞ g := L08_contDiff_cutoff_mul hO hf φ.contDiff hφO
  have hgs : HasCompactSupport g := φ.hasCompactSupport.mul_right
  have hgi : Integrable g volume := hg.continuous.integrable_of_hasCompactSupport hgs
  let q : ℂ → ℝ := f - g
  have hqi : Integrable q volume := hfi.sub hgi
  have hqs : HasCompactSupport q := hsupp.sub hgs
  have hxq : x ∉ tsupport q := by
    rw [notMem_tsupport_iff_eventuallyEq]
    filter_upwards [φ.eventuallyEq_one] with w hw
    simp [q, g, hw]
  have hnear := (L08_contDiff_logPotential_compact hg hgs).contDiffAt (x := x)
  have hfar := L08_contDiffAt_logPotential_off_support hqi hqs hxq
  have heq : (fun z : ℂ ↦ ∫ w, Real.log ‖z - w‖ * f w) =ᶠ[𝓝 x]
      (fun z ↦ (∫ w, Real.log ‖z - w‖ * g w) + ∫ w, Real.log ‖z - w‖ * q w) := by
    filter_upwards [hO.mem_nhds hx] with z hz
    have hIntg := L08_integrable_logPotential_compact hg hgs z
    have hIntq : Integrable (fun w ↦ Real.log ‖z - w‖ * q w) volume := by
      have hsub := (hkernel z hz).sub hIntg
      change Integrable
        (fun w ↦ Real.log ‖z - w‖ * f w - Real.log ‖z - w‖ * g w) volume at hsub
      simpa only [q, Pi.sub_apply, mul_sub] using hsub
    rw [← integral_add hIntg hIntq]
    apply integral_congr_ae
    filter_upwards with w
    simp [q, mul_sub]
  rw [L08_realPlanarLaplacian_congr_nhds heq,
    L08_realPlanarLaplacian_add (hnear.of_le (by simp)) (hfar.of_le (by simp)),
    L08_realPlanarLaplacian_logPotential_compact_eq hg hgs,
    L08_realPlanarLaplacian_logPotential_off_support hqi hqs hxq]
  have hφx : φ x = 1 := φ.eventuallyEq_one.eq_of_nhds
  simp only [g, hφx, one_mul, add_zero]

/-- The Newton integral of a smooth density restricted to a disc solves
the Poisson equation at every interior point of that disc. -/
theorem L08_realPlanarLaplacian_disc_logPotential {ρ : ℂ → ℝ} {z₀ : ℂ} {R : ℝ}
    {O : Set ℂ} (hO : IsOpen O) (hball : Metric.closedBall z₀ R ⊆ O)
    (hρ : ContDiffOn ℝ ∞ ρ O) {z : ℂ} (hz : z ∈ Metric.ball z₀ R) :
    LeafCandidates.realPlanarLaplacian
      (fun z : ℂ ↦ ∫ w in Metric.ball z₀ R, Real.log ‖z - w‖ * ρ w) z =
      2 * Real.pi * ρ z := by
  let f : ℂ → ℝ := (Metric.ball z₀ R).indicator ρ
  have hρc : ContinuousOn ρ (Metric.closedBall z₀ R) := hρ.continuousOn.mono hball
  have hf : ContDiffOn ℝ ∞ f (Metric.ball z₀ R) := by
    apply (hρ.mono (Metric.ball_subset_closedBall.trans hball)).congr
    intro w hw
    exact Set.indicator_of_mem hw ρ
  have hfi : Integrable f volume :=
    (integrable_indicator_iff measurableSet_ball).2
      ((hρc.integrableOn_compact (isCompact_closedBall z₀ R)).mono_set
        Metric.ball_subset_closedBall)
  have hfs : HasCompactSupport f := by
    apply (isCompact_closedBall z₀ R).of_isClosed_subset (isClosed_tsupport f)
    apply Metric.isClosed_closedBall.closure_subset_iff.mpr
    intro w hw
    by_contra hwb
    have hnotball : w ∉ Metric.ball z₀ R := fun h ↦ hwb (Metric.ball_subset_closedBall h)
    exact hw (Set.indicator_of_notMem hnotball ρ)
  have hkernel (z : ℂ) : Integrable (fun w ↦ Real.log ‖z - w‖ * f w) volume := by
    have hprod := (L08_integrableOn_log_norm_sub_disc z z₀ R).mul_continuousOn_of_subset
      hρc measurableSet_ball (isCompact_closedBall z₀ R) Metric.ball_subset_closedBall
    have hInd := (integrable_indicator_iff measurableSet_ball).2 hprod
    convert hInd using 1
    funext w
    exact (Set.indicator_mul_right (Metric.ball z₀ R) (fun w ↦ Real.log ‖z - w‖) ρ).symm
  have heq (y : ℂ) : (∫ w in Metric.ball z₀ R, Real.log ‖y - w‖ * ρ w) =
      ∫ w, Real.log ‖y - w‖ * f w := by
    rw [← integral_indicator measurableSet_ball]
    apply integral_congr_ae
    filter_upwards with w
    exact Set.indicator_mul_right (Metric.ball z₀ R) (fun w ↦ Real.log ‖y - w‖) ρ
  rw [L08_realPlanarLaplacian_congr_nhds (Filter.Eventually.of_forall heq),
    L08_realPlanarLaplacian_logPotential Metric.isOpen_ball hf hfi hfs (fun y _ ↦ hkernel y) hz]
  simp only [f, Set.indicator_of_mem hz]

/-- The exact measure in the frozen statement reproduces the original
smooth Laplacian, with its `(2π)⁻¹` density. -/
theorem L08_smoothRieszMeasure_realPlanarLaplacian_logPotential {u : ℂ → ℝ} {z₀ : ℂ} {R : ℝ}
    {O : Set ℂ} (hO : IsOpen O) (hball : Metric.closedBall z₀ R ⊆ O)
    (hu : ContDiffOn ℝ ∞ u O)
    (hΔ : ∀ w ∈ O, 0 ≤ LeafCandidates.realPlanarLaplacian u w)
    {z : ℂ} (hz : z ∈ Metric.ball z₀ R) :
    LeafCandidates.realPlanarLaplacian
      (fun z : ℂ ↦ ∫ w, Real.log ‖z - w‖ ∂(LeafCandidates.smoothRieszMeasure u z₀ R)) z =
      LeafCandidates.realPlanarLaplacian u z := by
  rw [L08_realPlanarLaplacian_congr_nhds
    (Filter.Eventually.of_forall (L08_smoothRieszMeasure_integral_log_eq hO hball hu hΔ))]
  rw [L08_realPlanarLaplacian_disc_logPotential hO hball
    ((L08_contDiffOn_realPlanarLaplacian hO hu).div_const (2 * Real.pi)) hz]
  field_simp

/-- The complete smooth Riesz component of L08, including finite mass,
absence of atoms, harmonic smooth remainder and absolute convergence. -/
theorem L08_smoothPlanarRieszDecomposition : LeafCandidates.SmoothPlanarRieszDecomposition := by
  intro u z₀ R hR hdata
  obtain ⟨O, hO, hball, hu, hΔ⟩ := hdata
  let p : ℂ → ℝ := fun z ↦ ∫ w, Real.log ‖z - w‖ ∂(LeafCandidates.smoothRieszMeasure u z₀ R)
  have hp : ContDiffOn ℝ ∞ p (Metric.ball z₀ R) :=
    L08_smoothRieszMeasure_contDiff_logPotential hO hball hu hΔ
  refine ⟨L08_smoothRieszMeasure_finite hO hball hu,
    L08_smoothRieszMeasure_singleton u z₀ R, fun z ↦ u z - p z,
    (hu.mono (Metric.ball_subset_closedBall.trans hball)).sub hp, ?_, ?_⟩
  · intro z hz
    rw [L08_realPlanarLaplacian_sub
      ((hu.contDiffAt (hO.mem_nhds (hball (Metric.ball_subset_closedBall hz)))).of_le (by simp))
      ((hp.contDiffAt (Metric.isOpen_ball.mem_nhds hz)).of_le (by simp)),
      L08_smoothRieszMeasure_realPlanarLaplacian_logPotential hO hball hu hΔ hz, sub_self]
  · intro z hz
    exact ⟨L08_smoothRieszMeasure_integrable_log hO hball hu hΔ z, (sub_add_cancel _ _).symm⟩

/-- Finite lower truncation of an extended-real potential. -/
def L08_lowerTrunc (u : ℂ → EReal) (n : ℕ) (z : ℂ) : ℝ :=
  (max (u z) ((-(n : ℝ) : ℝ) : EReal)).toReal

theorem L08_coe_lowerTrunc {u : ℂ → EReal} (n : ℕ) {z : ℂ} (hu : u z < ⊤) :
    (L08_lowerTrunc u n z : EReal) = max (u z) ((-(n : ℝ) : ℝ) : EReal) := by
  apply EReal.coe_toReal
  · exact (max_lt hu (EReal.coe_lt_top _)).ne
  · exact ne_of_gt ((EReal.bot_lt_coe (-(n : ℝ))).trans_le (le_max_right _ _))

theorem L08_le_coe_lowerTrunc {u : ℂ → EReal} (n : ℕ) {z : ℂ} (hu : u z < ⊤) :
    u z ≤ (L08_lowerTrunc u n z : EReal) := by
  rw [L08_coe_lowerTrunc n hu]
  exact le_max_left _ _

theorem L08_lowerTrunc_le {u : ℂ → EReal} (n : ℕ) {z : ℂ} {C : ℝ}
    (hC : u z ≤ (C : EReal)) (hCn : -(n : ℝ) ≤ C) : L08_lowerTrunc u n z ≤ C := by
  apply EReal.coe_le_coe_iff.mp
  rw [L08_coe_lowerTrunc n (hC.trans_lt (EReal.coe_lt_top C))]
  exact max_le hC (EReal.coe_le_coe_iff.mpr hCn)

theorem L08_lowerTrunc_antitone {u : ℂ → EReal} {z : ℂ} (hu : u z < ⊤) :
    Antitone (fun n : ℕ ↦ L08_lowerTrunc u n z) := by
  intro n m hnm
  apply EReal.coe_le_coe_iff.mp
  rw [L08_coe_lowerTrunc m hu, L08_coe_lowerTrunc n hu]
  exact max_le_max_left _ (EReal.coe_le_coe_iff.mpr (neg_le_neg (Nat.cast_le.mpr hnm)))

/-- Lipschitz upper envelope of a finite lower truncation on a fixed set. -/
def L08_majorantEnvelope (K : Set ℂ) (u : ℂ → EReal) (n : ℕ) (x : ℂ) : ℝ :=
  ⨆ y : K, L08_lowerTrunc u n y - (n : ℝ) * dist x y

theorem L08_majorantEnvelope_bddAbove {K : Set ℂ} {u : ℂ → EReal} {C : ℝ}
    (hC0 : 0 ≤ C) (hC : ∀ z ∈ K, u z ≤ (C : EReal)) (n : ℕ) (x : ℂ) :
    BddAbove (Set.range (fun y : K ↦ L08_lowerTrunc u n y - (n : ℝ) * dist x y)) := by
  refine ⟨C, ?_⟩
  rintro t ⟨y, rfl⟩
  have ht := L08_lowerTrunc_le n (hC y y.2)
    ((neg_nonpos.mpr (Nat.cast_nonneg n)).trans hC0)
  linarith [mul_nonneg (Nat.cast_nonneg n : 0 ≤ (n : ℝ)) (dist_nonneg (x := x) (y := (y : ℂ)))]

theorem L08_majorantEnvelope_lipschitz {K : Set ℂ} {u : ℂ → EReal} {C : ℝ}
    (hK : K.Nonempty) (hC0 : 0 ≤ C) (hC : ∀ z ∈ K, u z ≤ (C : EReal)) (n : ℕ) :
    LipschitzWith (n : NNReal) (L08_majorantEnvelope K u n) := by
  letI : Nonempty K := hK.to_subtype
  have haux (x x' : ℂ) :
      L08_majorantEnvelope K u n x ≤ L08_majorantEnvelope K u n x' + (n : ℝ) * dist x x' := by
    apply ciSup_le
    intro y
    have hs := le_ciSup (L08_majorantEnvelope_bddAbove hC0 hC n x') y
    have ht := mul_le_mul_of_nonneg_left (dist_triangle x' x (y : ℂ))
      (Nat.cast_nonneg n : 0 ≤ (n : ℝ))
    rw [mul_add, dist_comm x' x] at ht
    change L08_lowerTrunc u n y - (n : ℝ) * dist x' y ≤ L08_majorantEnvelope K u n x' at hs
    linarith
  apply LipschitzWith.of_dist_le_mul
  intro x x'
  rw [Real.dist_eq]
  change |L08_majorantEnvelope K u n x - L08_majorantEnvelope K u n x'| ≤ (n : ℝ) * dist x x'
  apply abs_sub_le_iff.mpr
  constructor
  · linarith [haux x x']
  · have h := haux x' x
    rw [dist_comm x' x] at h
    linarith

theorem L08_le_coe_majorantEnvelope {K : Set ℂ} {u : ℂ → EReal} {C : ℝ}
    (hC0 : 0 ≤ C) (hC : ∀ z ∈ K, u z ≤ (C : EReal)) (n : ℕ) {x : ℂ} (hx : x ∈ K) :
    u x ≤ (L08_majorantEnvelope K u n x : EReal) := by
  have hs := le_ciSup (L08_majorantEnvelope_bddAbove hC0 hC n x) (⟨x, hx⟩ : K)
  have htrunc : L08_lowerTrunc u n x ≤ L08_majorantEnvelope K u n x := by
    simpa only [dist_self, mul_zero, sub_zero, L08_majorantEnvelope] using hs
  exact (L08_le_coe_lowerTrunc n ((hC x hx).trans_lt (EReal.coe_lt_top C))).trans
    (EReal.coe_le_coe_iff.mpr htrunc)

theorem L08_majorantEnvelope_antitone {K : Set ℂ} {u : ℂ → EReal} {C : ℝ}
    (hK : K.Nonempty) (hC0 : 0 ≤ C) (hC : ∀ z ∈ K, u z ≤ (C : EReal)) (x : ℂ) :
    Antitone (fun n : ℕ ↦ L08_majorantEnvelope K u n x) := by
  letI : Nonempty K := hK.to_subtype
  intro n m hnm
  apply ciSup_mono (L08_majorantEnvelope_bddAbove hC0 hC n x)
  intro y
  have ht := L08_lowerTrunc_antitone ((hC y y.2).trans_lt (EReal.coe_lt_top C)) hnm
  have hp := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hnm : (n : ℝ) ≤ m)
    (dist_nonneg (x := x) (y := (y : ℂ)))
  linarith

/-- A bounded upper semicontinuous function is recovered by the decreasing
Lipschitz majorants, including at points where its value is `-∞`. -/
theorem L08_tendsto_majorantEnvelope {K : Set ℂ} {u : ℂ → EReal} {C : ℝ}
    (hC0 : 0 ≤ C) (hC : ∀ z ∈ K, u z ≤ (C : EReal))
    (hu : UpperSemicontinuousOn u K) {x : ℂ} (hx : x ∈ K) :
    Tendsto (fun n : ℕ ↦ (L08_majorantEnvelope K u n x : EReal)) atTop (𝓝 (u x)) := by
  letI : Nonempty K := ⟨⟨x, hx⟩⟩
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Filter.Eventually.of_forall fun n ↦ ha.trans_le (L08_le_coe_majorantEnvelope hC0 hC n hx)
  · intro b hb
    obtain ⟨q, hq, hqb⟩ := EReal.exists_between_coe_real hb
    obtain ⟨δ, hδ, hlocal⟩ := Metric.mem_nhdsWithin_iff.mp (hu x hx q hq)
    obtain ⟨N, hN⟩ := exists_nat_gt (max (-q) ((C - q) / δ))
    filter_upwards [eventually_ge_atTop N] with n hn
    have hnq : -(n : ℝ) ≤ q := by
      have := (le_max_left (-q) ((C - q) / δ)).trans_lt hN
      have := (Nat.cast_le.mpr hn : (N : ℝ) ≤ n)
      linarith
    have hnδ : C - q ≤ (n : ℝ) * δ := by
      have h := (le_max_right (-q) ((C - q) / δ)).trans_lt hN
      have h' := (div_lt_iff₀ hδ).mp h
      have := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hn : (N : ℝ) ≤ n) hδ.le
      linarith
    have hbound : L08_majorantEnvelope K u n x ≤ q := by
      apply ciSup_le
      intro y
      by_cases hy : dist x (y : ℂ) < δ
      · have hyq : u y ≤ (q : EReal) :=
          (hlocal ⟨by simpa only [Metric.mem_ball, dist_comm] using hy, y.2⟩).le
        have ht := L08_lowerTrunc_le n hyq hnq
        linarith [mul_nonneg (Nat.cast_nonneg n : 0 ≤ (n : ℝ))
          (dist_nonneg (x := x) (y := (y : ℂ)))]
      · have ht := L08_lowerTrunc_le n (hC y y.2)
          ((neg_nonpos.mpr (Nat.cast_nonneg n)).trans hC0)
        have hp := mul_le_mul_of_nonneg_left (le_of_not_gt hy) (Nat.cast_nonneg n : 0 ≤ (n : ℝ))
        linarith
    exact (EReal.coe_le_coe_iff.mpr hbound).trans_lt hqb

theorem L08_majorantEnvelope_le {K : Set ℂ} {u : ℂ → EReal} {C : ℝ}
    (hK : K.Nonempty) (hC0 : 0 ≤ C) (hC : ∀ z ∈ K, u z ≤ (C : EReal))
    (n : ℕ) (x : ℂ) : L08_majorantEnvelope K u n x ≤ C := by
  letI : Nonempty K := hK.to_subtype
  apply ciSup_le
  intro y
  have ht := L08_lowerTrunc_le n (hC y y.2)
    ((neg_nonpos.mpr (Nat.cast_nonneg n)).trans hC0)
  linarith [mul_nonneg (Nat.cast_nonneg n : 0 ≤ (n : ℝ))
    (dist_nonneg (x := x) (y := (y : ℂ)))]

/-- On a compact set, local L¹ finiteness makes these majorants converge
under the area integral as well as pointwise. -/
theorem L08_tendsto_integral_majorantEnvelope {K : Set ℂ} {u : ℂ → EReal} {C : ℝ}
    (hK : IsCompact K) (hKn : K.Nonempty) (hC0 : 0 ≤ C)
    (hC : ∀ z ∈ K, u z ≤ (C : EReal)) (hu : UpperSemicontinuousOn u K)
    (hfinite : ∀ᵐ z ∂volume.restrict K, u z ≠ ⊥ ∧ u z ≠ ⊤)
    (hi : IntegrableOn (fun z ↦ (u z).toReal) K volume) :
    Tendsto (fun n : ℕ ↦ ∫ z in K, L08_majorantEnvelope K u n z) atTop
      (𝓝 (∫ z in K, (u z).toReal)) := by
  apply tendsto_integral_filter_of_dominated_convergence (fun z ↦ |(u z).toReal| + C)
  · exact Filter.Eventually.of_forall fun n ↦
      (L08_majorantEnvelope_lipschitz hKn hC0 hC n).continuous.aestronglyMeasurable.restrict
  · apply Filter.Eventually.of_forall
    intro n
    filter_upwards [hfinite, ae_restrict_mem hK.measurableSet] with z hz hzK
    have hl := L08_le_coe_majorantEnvelope hC0 hC n hzK
    rw [← EReal.coe_toReal hz.2 hz.1] at hl
    have hlow := EReal.coe_le_coe_iff.mp hl
    have hhigh := L08_majorantEnvelope_le hKn hC0 hC n z
    rw [Real.norm_eq_abs]
    exact abs_le.mpr ⟨by linarith [neg_abs_le (u z).toReal], by linarith [abs_nonneg (u z).toReal]⟩
  · exact hi.norm.add (integrableOn_const hK.measure_lt_top.ne)
  · filter_upwards [hfinite, ae_restrict_mem hK.measurableSet] with z hz hzK
    have ht := (EReal.tendsto_toReal hz.2 hz.1).comp (L08_tendsto_majorantEnvelope hC0 hC hu hzK)
    simpa only [Function.comp_def, EReal.toReal_coe] using ht

/-- The angular interval used by polar coordinates gives the same circle
average as the frozen interval `[0,2π]`. -/
theorem L08_circleAverage_eq_angularIntegral (f : ℂ → ℝ) (z : ℂ) (r : ℝ) :
    Yau.circleAverage (fun θ ↦ f (z + r * Complex.exp (θ * Complex.I))) =
      (2 * Real.pi)⁻¹ * ∫ θ in (-Real.pi)..Real.pi, f (z + r • L08_unitCircle θ) := by
  have hp := ((periodic_circleMap z r).comp f).intervalIntegral_add_eq 0 (-Real.pi)
  have hend : -Real.pi + 2 * Real.pi = Real.pi := by ring
  simp only [zero_add, hend, Function.comp_def, circleMap] at hp
  unfold Yau.circleAverage
  rw [hp]
  rfl

/-- Integrating the continuous-majorant submeans over a positive radial
interval gives the genuine area estimate for that majorant. -/
theorem L08_subharmonic_continuous_annulus_bound {O : Set ℂ} {u : ℂ → EReal}
    (hu : LeafCandidates.DiscSubharmonic O u) {z : ℂ} {a b q : ℝ}
    (ha : 0 < a) (hab : a < b) (hball : Metric.closedBall z b ⊆ O)
    (hq : (q : EReal) ≤ u z) {f : ℂ → ℝ} (hf : Continuous f)
    (hmajor : ∀ w ∈ Metric.closedBall z b, u w ≤ (f w : EReal)) :
    q * (Real.pi * (b ^ 2 - a ^ 2)) ≤
      ∫ w in {w : ℂ | a < ‖w‖ ∧ ‖w‖ < b}, f (z + w) := by
  let J : ℝ → ℝ := fun r ↦ ∫ θ in (-Real.pi)..Real.pi, f (z + r • L08_unitCircle θ)
  have hpath : Continuous (fun p : ℝ × ℝ ↦ z + p.1 • L08_unitCircle p.2) :=
    continuous_const.add (continuous_fst.smul (L08_continuous_unitCircle.comp continuous_snd))
  have hJ : Continuous J := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun r θ ↦ f (z + r • L08_unitCircle θ))
    exact hf.comp hpath
  have hpoint (r : ℝ) (hr : r ∈ Set.Icc a b) : q * (2 * Real.pi) ≤ J r := by
    have hr0 : 0 < r := ha.trans_le hr.1
    have hsub := hu.2.2 z r hr0
      ((Metric.closedBall_subset_closedBall hr.2).trans hball)
      (fun θ ↦ f (z + r * Complex.exp (θ * Complex.I)))
      (hf.comp (continuous_circleMap z r))
      (fun θ ↦ hmajor _ ((Metric.closedBall_subset_closedBall hr.2)
        (circleMap_mem_closedBall z hr0.le θ)))
    have h := EReal.coe_le_coe_iff.mp (hq.trans hsub)
    rw [L08_circleAverage_eq_angularIntegral] at h
    change q ≤ (2 * Real.pi)⁻¹ * J r at h
    have hpos : 0 < 2 * Real.pi := by positivity
    have hm := mul_le_mul_of_nonneg_right h hpos.le
    field_simp at hm
    nlinarith
  have hmono := intervalIntegral.integral_mono_on (μ := volume) hab.le
    ((continuous_id.mul continuous_const).intervalIntegrable a b)
    ((continuous_id.mul hJ).intervalIntegrable a b)
    (fun r hr ↦ mul_le_mul_of_nonneg_left (hpoint r hr) (ha.trans_le hr.1).le)
  change (∫ r in a..b, r * (q * (2 * Real.pi))) ≤ ∫ r in a..b, r * J r at hmono
  have hleft : (∫ r in a..b, r * (q * (2 * Real.pi))) =
      q * (Real.pi * (b ^ 2 - a ^ 2)) := by
    rw [intervalIntegral.integral_mul_const, integral_id]
    ring
  rw [hleft] at hmono
  convert hmono using 1
  rw [L08_integral_annulus_polar (h := fun w ↦ f (z + w)) ha hab
    ((hf.comp (continuous_const.add continuous_id)).continuousOn),
    intervalIntegral.integral_of_le hab.le, integral_Ioc_eq_integral_Ioo]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro r _
  dsimp only
  rw [integral_const_mul]
  congr 1
  unfold J
  rw [intervalIntegral.integral_of_le (by linarith [Real.pi_pos]), integral_Ioc_eq_integral_Ioo]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro θ _
  have hq : L08_unitCircle θ = Real.cos θ + Real.sin θ * Complex.I :=
    Complex.exp_ofReal_mul_I θ
  dsimp only
  rw [← hq, ← Complex.real_smul]

theorem L08_integral_translate_annulus (f : ℂ → ℝ) (z : ℂ) (a b : ℝ) :
    (∫ w in {w : ℂ | a < ‖w‖ ∧ ‖w‖ < b}, f (z + w)) =
      ∫ w in {w : ℂ | a < ‖w - z‖ ∧ ‖w - z‖ < b}, f w := by
  have h := (measurePreserving_add_left (volume : Measure ℂ) z).setIntegral_preimage_emb
    (MeasurableEquiv.addLeft z).measurableEmbedding f
    {w : ℂ | a < ‖w - z‖ ∧ ‖w - z‖ < b}
  simpa only [Set.preimage_setOf_eq, add_sub_cancel_left] using h

theorem L08_tendsto_integral_majorantEnvelope_subset {K S : Set ℂ} {u : ℂ → EReal} {C : ℝ}
    (hK : IsCompact K) (hKn : K.Nonempty) (hS : MeasurableSet S) (hSK : S ⊆ K)
    (hC0 : 0 ≤ C) (hC : ∀ z ∈ K, u z ≤ (C : EReal)) (hu : UpperSemicontinuousOn u K)
    (hfinite : ∀ᵐ z ∂volume.restrict K, u z ≠ ⊥ ∧ u z ≠ ⊤)
    (hi : IntegrableOn (fun z ↦ (u z).toReal) K volume) :
    Tendsto (fun n : ℕ ↦ ∫ z in S, L08_majorantEnvelope K u n z) atTop
      (𝓝 (∫ z in S, (u z).toReal)) := by
  have hfin := ae_restrict_of_ae_restrict_of_subset hSK hfinite
  apply tendsto_integral_filter_of_dominated_convergence (fun z ↦ |(u z).toReal| + C)
  · exact Filter.Eventually.of_forall fun n ↦
      (L08_majorantEnvelope_lipschitz hKn hC0 hC n).continuous.aestronglyMeasurable.restrict
  · apply Filter.Eventually.of_forall
    intro n
    filter_upwards [hfin, ae_restrict_mem hS] with z hz hzS
    have hl := L08_le_coe_majorantEnvelope hC0 hC n (hSK hzS)
    rw [← EReal.coe_toReal hz.2 hz.1] at hl
    have hlow := EReal.coe_le_coe_iff.mp hl
    have hhigh := L08_majorantEnvelope_le hKn hC0 hC n z
    rw [Real.norm_eq_abs]
    exact abs_le.mpr ⟨by linarith [neg_abs_le (u z).toReal], by linarith [abs_nonneg (u z).toReal]⟩
  · exact (hi.mono_set hSK).norm.add
      (integrableOn_const ((measure_mono hSK).trans_lt hK.measure_lt_top).ne)
  · filter_upwards [hfin, ae_restrict_mem hS] with z hz hzS
    have ht := (EReal.tendsto_toReal hz.2 hz.1).comp
      (L08_tendsto_majorantEnvelope hC0 hC hu (hSK hzS))
    simpa only [Function.comp_def, EReal.toReal_coe] using ht

/-- The original extended-real subharmonic function satisfies the area
submean on every positive annulus contained in the domain. -/
theorem L08_subharmonic_annulus_bound {O : Set ℂ} {u : ℂ → EReal}
    (hu : LeafCandidates.DiscSubharmonic O u) (hL1 : LeafCandidates.LocallyL1 O u)
    {z : ℂ} {a b q : ℝ} (ha : 0 < a) (hab : a < b)
    (hball : Metric.closedBall z b ⊆ O) (hq : (q : EReal) ≤ u z) :
    q * (Real.pi * (b ^ 2 - a ^ 2)) ≤
      ∫ w in {w : ℂ | a < ‖w - z‖ ∧ ‖w - z‖ < b}, (u w).toReal := by
  let K := Metric.closedBall z b
  let S := {w : ℂ | a < ‖w - z‖ ∧ ‖w - z‖ < b}
  have hK : IsCompact K := isCompact_closedBall z b
  have hKn : K.Nonempty := ⟨z, Metric.mem_closedBall_self (ha.trans hab).le⟩
  have hS : MeasurableSet S :=
    ((isOpen_lt continuous_const (continuous_id.sub continuous_const).norm).inter
      (isOpen_lt (continuous_id.sub continuous_const).norm continuous_const)).measurableSet
  have hSK : S ⊆ K := by
    intro w hw
    exact Metric.mem_closedBall.mpr (by simpa only [dist_eq_norm] using hw.2.le)
  obtain ⟨B, hB⟩ := L08_subharmonic_bddAbove hu hK hball
  let C := max B 0
  have hC0 : 0 ≤ C := le_max_right _ _
  have hC : ∀ w ∈ K, u w ≤ (C : EReal) :=
    fun w hw ↦ (hB w hw).trans (EReal.coe_le_coe_iff.mpr (le_max_left _ _))
  have hconv := L08_tendsto_integral_majorantEnvelope_subset hK hKn hS hSK hC0 hC
    (hu.2.1.mono hball) (hL1 K hK hball).1 (hL1 K hK hball).2
  apply ge_of_tendsto hconv
  apply Filter.Eventually.of_forall
  intro n
  have h := L08_subharmonic_continuous_annulus_bound hu ha hab hball hq
    (L08_majorantEnvelope_lipschitz hKn hC0 hC n).continuous
    (fun w hw ↦ L08_le_coe_majorantEnvelope hC0 hC n hw)
  rw [L08_integral_translate_annulus] at h
  exact h

theorem L08_integral_annulus_const (z : ℂ) (c : ℝ) {a b : ℝ}
    (ha : 0 < a) (hab : a < b) :
    (∫ w in {w : ℂ | a < ‖w - z‖ ∧ ‖w - z‖ < b}, c) =
      c * (Real.pi * (b ^ 2 - a ^ 2)) := by
  rw [← L08_integral_translate_annulus (fun _ ↦ c) z a b,
    L08_integral_annulus_polar (h := fun _ ↦ c) ha hab continuous_const.continuousOn]
  have hangle (r : ℝ) : (∫ θ in Set.Ioo (-Real.pi) Real.pi, r * c) =
      (2 * Real.pi) * (r * c) := by
    rw [← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos])]
    simp only [intervalIntegral.integral_const, smul_eq_mul]
    ring
  simp_rw [hangle]
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hab.le]
  calc
    _ = (2 * Real.pi * c) * ∫ r in a..b, r := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro r _
      ring
    _ = _ := by rw [integral_id]; ring

/-- A pointwise upper bound is controlled uniformly by the L¹ error on any
fixed compact neighborhood containing the annulus. -/
theorem L08_subharmonic_annulus_error_bound {O K : Set ℂ} {u : ℂ → EReal}
    (hu : LeafCandidates.DiscSubharmonic O u) (hL1 : LeafCandidates.LocallyL1 O u)
    (hK : IsCompact K) (hKO : K ⊆ O) {z : ℂ} {a b q : ℝ}
    (ha : 0 < a) (hab : a < b) (hball : Metric.closedBall z b ⊆ K)
    (hq : (q : EReal) ≤ u z) (c : ℝ) :
    q * (Real.pi * (b ^ 2 - a ^ 2)) ≤ c * (Real.pi * (b ^ 2 - a ^ 2)) +
      ∫ w in K, |(u w).toReal - c| := by
  let S := {w : ℂ | a < ‖w - z‖ ∧ ‖w - z‖ < b}
  have hSK : S ⊆ K := by
    intro w hw
    apply hball
    exact Metric.mem_closedBall.mpr (by simpa only [dist_eq_norm] using hw.2.le)
  have hi := (hL1 K hK hKO).2
  have hc : IntegrableOn (fun _ : ℂ ↦ c) K volume := integrableOn_const hK.measure_lt_top.ne
  have he : IntegrableOn (fun w ↦ |(u w).toReal - c|) K volume := (hi.sub hc).norm
  have hsconst := hc.mono_set hSK
  have hserror := he.mono_set hSK
  have hmean := L08_subharmonic_annulus_bound hu hL1 ha hab (hball.trans hKO) hq
  have hupper : (∫ w in S, (u w).toReal) ≤ ∫ w in S, c + |(u w).toReal - c| := by
    apply integral_mono (hi.mono_set hSK) (hsconst.add hserror)
    intro w
    change (u w).toReal ≤ c + |(u w).toReal - c|
    linarith [le_abs_self ((u w).toReal - c)]
  have herror : (∫ w in S, |(u w).toReal - c|) ≤ ∫ w in K, |(u w).toReal - c| :=
    setIntegral_mono_set he (Filter.Eventually.of_forall fun w ↦ abs_nonneg _)
      (Filter.Eventually.of_forall hSK)
  rw [integral_add hsconst hserror, L08_integral_annulus_const z c ha hab] at hupper
  exact hmean.trans (hupper.trans (add_le_add le_rfl herror))

/-- The complete constant-limit Hartogs component of L08. The radius and
the containing compact neighborhood are chosen uniformly over `K`. -/
theorem L08_subharmonicHartogs : LeafCandidates.SubharmonicHartogs := by
  intro O u c hO hu hconv K hK hKO ε hε
  obtain ⟨δ, hδ, hδO⟩ := hK.exists_cthickening_subset_open hO hKO
  let L := Metric.cthickening δ K
  have hL : IsCompact L := hK.cthickening
  let A := Real.pi * (δ ^ 2 - (δ / 2) ^ 2)
  have hA : 0 < A := by
    apply mul_pos Real.pi_pos
    nlinarith [sq_pos_of_pos hδ]
  have ht : Tendsto (fun j ↦ ∫ w in L, |(u j w).toReal - c|) atTop (𝓝 0) := by
    simpa only [EReal.toReal_coe] using hconv.2 L hL hδO
  have hevent : ∀ᶠ j in atTop, (∫ w in L, |(u j w).toReal - c|) < ε * A :=
    (tendsto_order.mp ht).2 (ε * A) (mul_pos hε hA)
  filter_upwards [hevent] with j hj
  intro z hz
  by_contra h
  obtain ⟨q, hq, hqu⟩ := EReal.exists_between_coe_real (lt_of_not_ge h)
  have hqr : c + ε < q := EReal.coe_lt_coe_iff.mp hq
  have hb := L08_subharmonic_annulus_error_bound (hu j).1 (hu j).2 hL hδO
    (half_pos hδ) (half_lt_self hδ) (Metric.closedBall_subset_cthickening hz δ) hqu.le c
  change q * A ≤ c * A + ∫ w in L, |(u j w).toReal - c| at hb
  have hp := mul_lt_mul_of_pos_right hqr hA
  nlinarith

theorem L08_subharmonic_annulus_error_le {O K : Set ℂ} {u : ℂ → EReal}
    (hu : LeafCandidates.DiscSubharmonic O u) (hL1 : LeafCandidates.LocallyL1 O u)
    (hK : IsCompact K) (hKO : K ⊆ O) {z : ℂ} {a b : ℝ}
    (ha : 0 < a) (hab : a < b) (hball : Metric.closedBall z b ⊆ K) (c : ℝ) :
    u z ≤ ((c + (∫ w in K, |(u w).toReal - c|) /
      (Real.pi * (b ^ 2 - a ^ 2)) : ℝ) : EReal) := by
  let A := Real.pi * (b ^ 2 - a ^ 2)
  have hA : 0 < A := by
    apply mul_pos Real.pi_pos
    nlinarith [mul_pos (sub_pos.mpr hab) (show 0 < b + a by linarith)]
  by_contra h
  obtain ⟨q, hq, hqu⟩ := EReal.exists_between_coe_real (lt_of_not_ge h)
  have hqr := EReal.coe_lt_coe_iff.mp hq
  have hb := L08_subharmonic_annulus_error_bound hu hL1 hK hKO ha hab hball hqu.le c
  change q * A ≤ c * A + ∫ w in K, |(u w).toReal - c| at hb
  change c + (∫ w in K, |(u w).toReal - c|) / A < q at hqr
  have hp := mul_lt_mul_of_pos_right hqr hA
  rw [add_mul, div_mul_cancel₀ _ hA.ne'] at hp
  exact (not_lt_of_ge hb) hp

/-- The local area L¹ bound in the compactness hypothesis already gives a
uniform pointwise upper bound on every smaller compact set. -/
theorem L08_subharmonic_uniform_bddAbove {O : Set ℂ} {u : ℕ → ℂ → EReal}
    (hO : IsOpen O) (hu : ∀ j, LeafCandidates.DiscSubharmonic O (u j) ∧
      LeafCandidates.LocallyL1 O (u j))
    (hbound : ∀ K : Set ℂ, IsCompact K → K ⊆ O → ∃ C : ℝ, ∀ j,
      ∫ z in K, |(u j z).toReal| ≤ C)
    {K : Set ℂ} (hK : IsCompact K) (hKO : K ⊆ O) :
    ∃ C : ℝ, ∀ j z, z ∈ K → u j z ≤ (C : EReal) := by
  obtain ⟨δ, hδ, hδO⟩ := hK.exists_cthickening_subset_open hO hKO
  let L := Metric.cthickening δ K
  have hL : IsCompact L := hK.cthickening
  obtain ⟨C, hC⟩ := hbound L hL hδO
  let A := Real.pi * (δ ^ 2 - (δ / 2) ^ 2)
  have hA : 0 < A := by
    apply mul_pos Real.pi_pos
    nlinarith [sq_pos_of_pos hδ]
  refine ⟨C / A, ?_⟩
  intro j z hz
  have h := L08_subharmonic_annulus_error_le (hu j).1 (hu j).2 hL hδO
    (half_pos hδ) (half_lt_self hδ) (Metric.closedBall_subset_cthickening hz δ) 0
  simp only [sub_zero, zero_add] at h
  exact h.trans (EReal.coe_le_coe_iff.mpr
    (div_le_div_of_nonneg_right (hC j) hA.le))

/-- A continuous majorant on a disc satisfies the numerical circle bound
needed when integrating against a positive radial kernel. -/
theorem L08_subharmonic_continuous_circle_bound {O : Set ℂ} {u : ℂ → EReal}
    (hu : LeafCandidates.DiscSubharmonic O u) {z : ℂ} {r q : ℝ}
    (hr : 0 < r) (hball : Metric.closedBall z r ⊆ O) (hq : (q : EReal) ≤ u z)
    {f : ℂ → ℝ} (hf : Continuous f)
    (hmajor : ∀ w ∈ Metric.closedBall z r, u w ≤ (f w : EReal)) :
    q * (2 * Real.pi) ≤ ∫ θ in (-Real.pi)..Real.pi, f (z + r • L08_unitCircle θ) := by
  have hsub := hu.2.2 z r hr hball
    (fun θ ↦ f (z + r * Complex.exp (θ * Complex.I)))
    (hf.comp (continuous_circleMap z r))
    (fun θ ↦ hmajor _ (circleMap_mem_closedBall z hr.le θ))
  have h := EReal.coe_le_coe_iff.mp (hq.trans hsub)
  rw [L08_circleAverage_eq_angularIntegral] at h
  have hpos : 0 < 2 * Real.pi := by positivity
  have hm := mul_le_mul_of_nonneg_right h hpos.le
  field_simp at hm
  nlinarith

/-- Positive continuous radial weights can be integrated against the exact
continuous-majorant submeans. -/
theorem L08_subharmonic_continuous_weighted_annulus_bound {O : Set ℂ} {u : ℂ → EReal}
    (hu : LeafCandidates.DiscSubharmonic O u) {z : ℂ} {a b q : ℝ}
    (ha : 0 < a) (hab : a < b) (hball : Metric.closedBall z b ⊆ O)
    (hq : (q : EReal) ≤ u z) {f : ℂ → ℝ} (hf : Continuous f)
    (hmajor : ∀ w ∈ Metric.closedBall z b, u w ≤ (f w : EReal))
    {κ : ℝ → ℝ} (hκ : Continuous κ) (hκ0 : ∀ r ∈ Set.Icc a b, 0 ≤ κ r) :
    q * (2 * Real.pi * ∫ r in a..b, r * κ r) ≤
      ∫ w in {w : ℂ | a < ‖w‖ ∧ ‖w‖ < b}, κ ‖w‖ * f (z + w) := by
  let J : ℝ → ℝ := fun r ↦ ∫ θ in (-Real.pi)..Real.pi, f (z + r • L08_unitCircle θ)
  have hpath : Continuous (fun p : ℝ × ℝ ↦ z + p.1 • L08_unitCircle p.2) :=
    continuous_const.add (continuous_fst.smul (L08_continuous_unitCircle.comp continuous_snd))
  have hJ : Continuous J := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun r θ ↦ f (z + r • L08_unitCircle θ))
    exact hf.comp hpath
  have hpoint (r : ℝ) (hr : r ∈ Set.Icc a b) : q * (2 * Real.pi) ≤ J r :=
    L08_subharmonic_continuous_circle_bound hu (ha.trans_le hr.1)
      ((Metric.closedBall_subset_closedBall hr.2).trans hball) hq hf
      (fun w hw ↦ hmajor w (Metric.closedBall_subset_closedBall hr.2 hw))
  have hmono := intervalIntegral.integral_mono_on (μ := volume) hab.le
    (((continuous_id.mul hκ).mul continuous_const).intervalIntegrable a b)
    (((continuous_id.mul hκ).mul hJ).intervalIntegrable a b)
    (fun r hr ↦ mul_le_mul_of_nonneg_left (hpoint r hr)
      (mul_nonneg (ha.trans_le hr.1).le (hκ0 r hr)))
  change (∫ r in a..b, (r * κ r) * (q * (2 * Real.pi))) ≤
    ∫ r in a..b, (r * κ r) * J r at hmono
  rw [intervalIntegral.integral_mul_const] at hmono
  have hleft : (∫ r in a..b, r * κ r) * (q * (2 * Real.pi)) =
      q * (2 * Real.pi * ∫ r in a..b, r * κ r) := by ring
  rw [hleft] at hmono
  convert hmono using 1
  rw [L08_integral_annulus_polar (h := fun w ↦ κ ‖w‖ * f (z + w)) ha hab
    (((hκ.comp continuous_norm).mul (hf.comp (continuous_const.add continuous_id))).continuousOn),
    intervalIntegral.integral_of_le hab.le, integral_Ioc_eq_integral_Ioo]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro r hr
  dsimp only
  calc
    _ = ∫ θ in Set.Ioo (-Real.pi) Real.pi, (r * κ r) * f (z + r • L08_unitCircle θ) := by
      apply setIntegral_congr_fun measurableSet_Ioo
      intro θ _
      have hq : L08_unitCircle θ = Real.cos θ + Real.sin θ * Complex.I :=
        Complex.exp_ofReal_mul_I θ
      dsimp only
      rw [← hq, ← Complex.real_smul, norm_smul, L08_norm_unitCircle,
        Real.norm_eq_abs, abs_of_pos (ha.trans hr.1), mul_one]
      ring
    _ = (r * κ r) * J r := by
      rw [integral_const_mul]
      congr 1
      unfold J
      rw [intervalIntegral.integral_of_le (by linarith [Real.pi_pos]), integral_Ioc_eq_integral_Ioo]

theorem L08_tendsto_integral_weight_majorantEnvelope_subset
    {K S : Set ℂ} {u : ℂ → EReal} {C : ℝ} {k : ℂ → ℝ}
    (hK : IsCompact K) (hKn : K.Nonempty) (hS : MeasurableSet S) (hSK : S ⊆ K)
    (hC0 : 0 ≤ C) (hC : ∀ z ∈ K, u z ≤ (C : EReal)) (hu : UpperSemicontinuousOn u K)
    (hfinite : ∀ᵐ z ∂volume.restrict K, u z ≠ ⊥ ∧ u z ≠ ⊤)
    (hi : IntegrableOn (fun z ↦ (u z).toReal) K volume) (hk : Continuous k) :
    Tendsto (fun n : ℕ ↦ ∫ z in S, k z * L08_majorantEnvelope K u n z) atTop
      (𝓝 (∫ z in S, k z * (u z).toReal)) := by
  have hfin := ae_restrict_of_ae_restrict_of_subset hSK hfinite
  apply tendsto_integral_filter_of_dominated_convergence (fun z ↦ |k z| * (|(u z).toReal| + C))
  · exact Filter.Eventually.of_forall fun n ↦
      (hk.mul (L08_majorantEnvelope_lipschitz hKn hC0 hC n).continuous).aestronglyMeasurable.restrict
  · apply Filter.Eventually.of_forall
    intro n
    filter_upwards [hfin, ae_restrict_mem hS] with z hz hzS
    have hl := L08_le_coe_majorantEnvelope hC0 hC n (hSK hzS)
    rw [← EReal.coe_toReal hz.2 hz.1] at hl
    have hlow := EReal.coe_le_coe_iff.mp hl
    have hhigh := L08_majorantEnvelope_le hKn hC0 hC n z
    have hnorm : |L08_majorantEnvelope K u n z| ≤ |(u z).toReal| + C :=
      abs_le.mpr ⟨by linarith [neg_abs_le (u z).toReal], by linarith [abs_nonneg (u z).toReal]⟩
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left hnorm (abs_nonneg _)
  · have hbase : IntegrableOn (fun z ↦ |(u z).toReal| + C) K volume :=
      hi.norm.add (integrableOn_const hK.measure_lt_top.ne)
    exact IntegrableOn.continuousOn_mul_of_subset hk.norm.continuousOn
      (hbase.mono_set hSK) hK hS hSK
  · filter_upwards [hfin, ae_restrict_mem hS] with z hz hzS
    have ht := (EReal.tendsto_toReal hz.2 hz.1).comp
      (L08_tendsto_majorantEnvelope hC0 hC hu (hSK hzS))
    have ht' : Tendsto (fun n ↦ L08_majorantEnvelope K u n z) atTop (𝓝 (u z).toReal) := by
      simpa only [Function.comp_def, EReal.toReal_coe] using ht
    exact tendsto_const_nhds.mul ht'

/-- A nonnegative radial kernel supported between two positive radii
majorizes the original potential when normalized to have mass one. -/
theorem L08_subharmonic_radial_annulus_le {O : Set ℂ} {u : ℂ → EReal}
    (hu : LeafCandidates.DiscSubharmonic O u) (hL1 : LeafCandidates.LocallyL1 O u)
    {z : ℂ} {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (hball : Metric.closedBall z b ⊆ O) {κ : ℝ → ℝ} (hκ : Continuous κ)
    (hκ0 : ∀ r ∈ Set.Icc a b, 0 ≤ κ r)
    (hκmass : 2 * Real.pi * (∫ r in a..b, r * κ r) = 1) :
    u z ≤ ((∫ w in {w : ℂ | a < ‖w - z‖ ∧ ‖w - z‖ < b},
      κ ‖w - z‖ * (u w).toReal : ℝ) : EReal) := by
  let K := Metric.closedBall z b
  let S := {w : ℂ | a < ‖w - z‖ ∧ ‖w - z‖ < b}
  have hK : IsCompact K := isCompact_closedBall z b
  have hKn : K.Nonempty := ⟨z, Metric.mem_closedBall_self (ha.trans hab).le⟩
  have hS : MeasurableSet S :=
    ((isOpen_lt continuous_const (continuous_id.sub continuous_const).norm).inter
      (isOpen_lt (continuous_id.sub continuous_const).norm continuous_const)).measurableSet
  have hSK : S ⊆ K := by
    intro w hw
    exact Metric.mem_closedBall.mpr (by simpa only [dist_eq_norm] using hw.2.le)
  obtain ⟨B, hB⟩ := L08_subharmonic_bddAbove hu hK hball
  let C := max B 0
  have hC0 : 0 ≤ C := le_max_right _ _
  have hC : ∀ w ∈ K, u w ≤ (C : EReal) :=
    fun w hw ↦ (hB w hw).trans (EReal.coe_le_coe_iff.mpr (le_max_left _ _))
  have hk : Continuous (fun w : ℂ ↦ κ ‖w - z‖) := hκ.comp (continuous_id.sub continuous_const).norm
  have hconv := L08_tendsto_integral_weight_majorantEnvelope_subset hK hKn hS hSK hC0 hC
    (hu.2.1.mono hball) (hL1 K hK hball).1 (hL1 K hK hball).2 hk
  by_contra h
  obtain ⟨q, hq, hqu⟩ := EReal.exists_between_coe_real (lt_of_not_ge h)
  have hqr := EReal.coe_lt_coe_iff.mp hq
  have hbound : q ≤ ∫ w in S, κ ‖w - z‖ * (u w).toReal := by
    apply ge_of_tendsto hconv
    apply Filter.Eventually.of_forall
    intro n
    have hb := L08_subharmonic_continuous_weighted_annulus_bound hu ha hab hball hqu.le
      (L08_majorantEnvelope_lipschitz hKn hC0 hC n).continuous
      (fun w hw ↦ L08_le_coe_majorantEnvelope hC0 hC n hw) hκ hκ0
    rw [hκmass, mul_one] at hb
    have heq := L08_integral_translate_annulus
      (fun w ↦ κ ‖w - z‖ * L08_majorantEnvelope K u n w) z a b
    simp only [add_sub_cancel_left] at heq
    rw [heq] at hb
    exact hb
  exact (not_lt_of_ge hbound) hqr

/-- A one-dimensional bump, used only through a squared radial variable. -/
def L08_radialBump : ContDiffBump (1 : ℝ) :=
  ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩

def L08_radialProfile (t r : ℝ) : ℝ := L08_radialBump (r ^ 2 / t ^ 2)

def L08_radialMass (t : ℝ) : ℝ :=
  2 * Real.pi * ∫ r in (t / 2)..(2 * t), r * L08_radialProfile t r

def L08_radialKernel (t : ℝ) (w : ℂ) : ℝ :=
  L08_radialProfile t ‖w‖ / L08_radialMass t

theorem L08_continuous_radialProfile (t : ℝ) : Continuous (L08_radialProfile t) :=
  L08_radialBump.continuous.comp ((continuous_id.pow 2).div_const _)

theorem L08_radialProfile_nonneg (t r : ℝ) : 0 ≤ L08_radialProfile t r :=
  L08_radialBump.nonneg

theorem L08_radialProfile_self {t : ℝ} (ht : 0 < t) : L08_radialProfile t t = 1 := by
  unfold L08_radialProfile
  rw [div_self (sq_pos_of_pos ht).ne']
  exact L08_radialBump.one_of_mem_closedBall
    (Metric.mem_closedBall_self L08_radialBump.rIn_pos.le)

theorem L08_radialMass_pos {t : ℝ} (ht : 0 < t) : 0 < L08_radialMass t := by
  apply mul_pos (by positivity : 0 < 2 * Real.pi)
  apply intervalIntegral.integral_pos (by linarith)
    ((continuous_id.mul (L08_continuous_radialProfile t)).continuousOn)
    (fun r hr ↦ mul_nonneg (show 0 ≤ id r by change 0 ≤ r; linarith [hr.1])
      (L08_radialProfile_nonneg t r))
  refine ⟨t, ⟨by linarith, by linarith⟩, ?_⟩
  change 0 < t * L08_radialProfile t t
  rw [L08_radialProfile_self ht, mul_one]
  exact ht

theorem L08_radialProfile_zero_inner {t r : ℝ} (ht : 0 < t)
    (hr0 : 0 ≤ r) (hr : r ≤ t / 2) : L08_radialProfile t r = 0 := by
  apply L08_radialBump.zero_of_le_dist
  change (1 / 2 : ℝ) ≤ |r ^ 2 / t ^ 2 - 1|
  have hdiv : r ^ 2 / t ^ 2 ≤ 1 / 4 := by
    apply (div_le_iff₀ (sq_pos_of_pos ht)).mpr
    nlinarith [mul_nonneg (show 0 ≤ t / 2 - r by linarith)
      (show 0 ≤ t / 2 + r by linarith)]
  linarith [neg_le_abs (r ^ 2 / t ^ 2 - 1)]

theorem L08_radialProfile_zero_outer {t r : ℝ} (ht : 0 < t)
    (hr : 2 * t ≤ r) : L08_radialProfile t r = 0 := by
  apply L08_radialBump.zero_of_le_dist
  change (1 / 2 : ℝ) ≤ |r ^ 2 / t ^ 2 - 1|
  have hdiv : 4 ≤ r ^ 2 / t ^ 2 := by
    apply (le_div_iff₀ (sq_pos_of_pos ht)).mpr
    nlinarith [mul_nonneg (show 0 ≤ r - 2 * t by linarith)
      (show 0 ≤ r + 2 * t by linarith)]
  linarith [le_abs_self (r ^ 2 / t ^ 2 - 1)]

theorem L08_contDiff_radialKernel (t : ℝ) : ContDiff ℝ ∞ (L08_radialKernel t) := by
  exact (L08_radialBump.contDiff.comp ((contDiff_norm_sq ℝ).div_const _)).div_const _

theorem L08_radialKernel_nonneg {t : ℝ} (ht : 0 < t) (w : ℂ) :
    0 ≤ L08_radialKernel t w :=
  div_nonneg (L08_radialProfile_nonneg _ _) (L08_radialMass_pos ht).le

theorem L08_radialKernel_neg (t : ℝ) (w : ℂ) : L08_radialKernel t (-w) = L08_radialKernel t w := by
  simp only [L08_radialKernel, norm_neg]

theorem L08_radialKernel_tsupport_subset {t : ℝ} (ht : 0 < t) :
    tsupport (L08_radialKernel t) ⊆ Metric.closedBall 0 (2 * t) := by
  apply Metric.isClosed_closedBall.closure_subset_iff.mpr
  intro w hw
  by_contra h
  have hnorm : 2 * t ≤ ‖w‖ := by
    have h' : ¬‖w‖ ≤ 2 * t := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using h
    exact (not_le.mp h').le
  exact hw (by simp only [L08_radialKernel, L08_radialProfile_zero_outer ht hnorm, zero_div])

theorem L08_radialKernel_hasCompactSupport {t : ℝ} (ht : 0 < t) :
    HasCompactSupport (L08_radialKernel t) :=
  (isCompact_closedBall (0 : ℂ) (2 * t)).of_isClosed_subset (isClosed_tsupport _)
    (L08_radialKernel_tsupport_subset ht)

theorem L08_integral_radial_annulus {κ : ℝ → ℝ} (hκ : Continuous κ)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    (∫ w in {w : ℂ | a < ‖w‖ ∧ ‖w‖ < b}, κ ‖w‖) =
      2 * Real.pi * ∫ r in a..b, r * κ r := by
  rw [L08_integral_annulus_polar (h := fun w ↦ κ ‖w‖) ha hab
    (hκ.comp continuous_norm).continuousOn]
  have hinner (r : ℝ) (hr : r ∈ Set.Ioo a b) :
      (∫ θ in Set.Ioo (-Real.pi) Real.pi,
        r * κ ‖(r : ℂ) * (Real.cos θ + Real.sin θ * Complex.I)‖) =
        (2 * Real.pi) * (r * κ r) := by
    have hnorm (θ : ℝ) : ‖(r : ℂ) * (Real.cos θ + Real.sin θ * Complex.I)‖ = r := by
      rw [← Complex.exp_ofReal_mul_I, norm_mul, Complex.norm_real,
        Real.norm_eq_abs, Complex.norm_exp_ofReal_mul_I, mul_one, abs_of_pos (ha.trans hr.1)]
    simp_rw [hnorm]
    rw [← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos])]
    simp only [intervalIntegral.integral_const, smul_eq_mul]
    ring
  calc
    _ = ∫ r in Set.Ioo a b, (2 * Real.pi) * (r * κ r) := by
      apply setIntegral_congr_fun measurableSet_Ioo
      intro r hr
      exact hinner r hr
    _ = _ := by
      rw [integral_const_mul, intervalIntegral.integral_of_le hab.le, integral_Ioc_eq_integral_Ioo]

theorem L08_radialKernel_radialMass {t : ℝ} (ht : 0 < t) :
    2 * Real.pi * (∫ r in (t / 2)..(2 * t),
      r * (L08_radialProfile t r / L08_radialMass t)) = 1 := by
  simp_rw [← mul_div_assoc]
  rw [intervalIntegral.integral_div, ← mul_div_assoc]
  exact div_self (L08_radialMass_pos ht).ne'

theorem L08_radialKernel_zero_of_notMem_annulus {t : ℝ} (ht : 0 < t) {w : ℂ}
    (hw : w ∉ {w : ℂ | t / 2 < ‖w‖ ∧ ‖w‖ < 2 * t}) : L08_radialKernel t w = 0 := by
  by_cases hlow : t / 2 < ‖w‖
  · have hhigh : 2 * t ≤ ‖w‖ := le_of_not_gt (fun h ↦ hw ⟨hlow, h⟩)
    simp only [L08_radialKernel, L08_radialProfile_zero_outer ht hhigh, zero_div]
  · simp only [L08_radialKernel,
      L08_radialProfile_zero_inner ht (norm_nonneg w) (le_of_not_gt hlow), zero_div]

theorem L08_integral_radialKernel {t : ℝ} (ht : 0 < t) : ∫ w, L08_radialKernel t w = 1 := by
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero
    (fun w hw ↦ L08_radialKernel_zero_of_notMem_annulus ht hw)]
  change (∫ w in {w : ℂ | t / 2 < ‖w‖ ∧ ‖w‖ < 2 * t},
    (fun r ↦ L08_radialProfile t r / L08_radialMass t) ‖w‖) = 1
  rw [L08_integral_radial_annulus ((L08_continuous_radialProfile t).div_const _)
    (half_pos ht) (by linarith)]
  exact L08_radialKernel_radialMass ht

/-- The concrete smooth radial kernels majorize every original potential;
the proof supplies the bridge rather than assuming a mollifier property. -/
theorem L08_subharmonic_le_radialConvolution {O : Set ℂ} {u : ℂ → EReal}
    (hu : LeafCandidates.DiscSubharmonic O u) (hL1 : LeafCandidates.LocallyL1 O u)
    {t : ℝ} (ht : 0 < t) {z : ℂ} (hball : Metric.closedBall z (2 * t) ⊆ O) :
    u z ≤ ((∫ w, L08_radialKernel t (z - w) * (u w).toReal : ℝ) : EReal) := by
  have hmean := L08_subharmonic_radial_annulus_le hu hL1 (half_pos ht) (by linarith) hball
    ((L08_continuous_radialProfile t).div_const (L08_radialMass t))
    (fun r _ ↦ div_nonneg (L08_radialProfile_nonneg t r) (L08_radialMass_pos ht).le)
    (L08_radialKernel_radialMass ht)
  change u z ≤ ((∫ w in {w : ℂ | t / 2 < ‖w - z‖ ∧ ‖w - z‖ < 2 * t},
    L08_radialKernel t (w - z) * (u w).toReal : ℝ) : EReal) at hmean
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero
    (fun w hw ↦ by rw [L08_radialKernel_zero_of_notMem_annulus ht hw, zero_mul])] at hmean
  simpa only [L08_radialKernel, norm_sub_rev] using hmean

theorem L08_radialKernel_support_subset_ball {t : ℝ} (ht : 0 < t) :
    Function.support (L08_radialKernel t) ⊆ Metric.ball 0 (2 * t) := by
  intro w hw
  rw [Metric.mem_ball, dist_zero_right]
  by_contra h
  exact hw (by simp only [L08_radialKernel,
    L08_radialProfile_zero_outer ht (le_of_not_gt h), zero_div])

/-- The normalized kernels approximate every Lipschitz test function with
a first-order bound, uniform in the evaluation point. -/
theorem L08_radialConvolution_lipschitz_approx {t : ℝ} (ht : 0 < t)
    {χ : ℂ → ℝ} {C : NNReal} (hχ : LipschitzWith C χ) (z : ℂ) :
    |(∫ w, L08_radialKernel t w * χ (z - w)) - χ z| ≤ (C : ℝ) * (2 * t) := by
  have h := MeasureTheory.dist_convolution_le (μ := (volume : Measure ℂ))
    (g := χ) (x₀ := z) (R := 2 * t) (z₀ := χ z)
    (mul_nonneg C.coe_nonneg (by positivity : 0 ≤ 2 * t))
    (L08_radialKernel_support_subset_ball ht) (L08_radialKernel_nonneg ht)
    (L08_integral_radialKernel ht) hχ.continuous.aestronglyMeasurable
    (fun w hw ↦ (hχ.dist_le_mul w z).trans
      (mul_le_mul_of_nonneg_left (Metric.mem_ball.mp hw).le C.coe_nonneg))
  simpa only [convolution_def, ContinuousLinearMap.lsmul_apply, smul_eq_mul, Real.dist_eq] using h

theorem L08_contDiff_radialConvolution {t : ℝ} (ht : 0 < t) {g : ℂ → ℝ}
    (hg : Integrable g volume) :
    ContDiff ℝ ∞ (fun z : ℂ ↦ ∫ w, L08_radialKernel t (z - w) * g w) := by
  have h := (L08_radialKernel_hasCompactSupport ht).contDiff_convolution_right
    (ContinuousLinearMap.mul ℝ ℝ) hg.locallyIntegrable (L08_contDiff_radialKernel t)
  convert h using 1
  funext z
  rw [convolution_def]
  apply integral_congr_ae
  filter_upwards with w
  exact mul_comm _ _

/-- Fubini and symmetry move the smoothing kernel from an integrable
function onto a compactly supported continuous test function. -/
theorem L08_radialConvolution_adjoint {t : ℝ} (ht : 0 < t)
    {g χ : ℂ → ℝ} (hg : Integrable g volume) (hχ : Continuous χ)
    (hsχ : HasCompactSupport χ) :
    (∫ z, χ z * (∫ w, L08_radialKernel t (z - w) * g w)) =
      ∫ w, g w * (∫ z, L08_radialKernel t (w - z) * χ z) := by
  obtain ⟨B, hB⟩ := hsχ.exists_bound_of_continuous hχ
  have hρ : Integrable (L08_radialKernel t) volume :=
    integrable_of_integral_eq_one (L08_integral_radialKernel ht)
  have hbase := hg.convolution_integrand (ContinuousLinearMap.mul ℝ ℝ) hρ
  change Integrable (fun p : ℂ × ℂ ↦ g p.2 * L08_radialKernel t (p.1 - p.2))
    (volume.prod volume) at hbase
  have hprod : Integrable
      (fun p : ℂ × ℂ ↦ χ p.1 * (g p.2 * L08_radialKernel t (p.1 - p.2)))
      (volume.prod volume) := hbase.bdd_mul
    (hχ.comp continuous_fst).aestronglyMeasurable (Filter.Eventually.of_forall fun p ↦ hB p.1)
  calc
    _ = ∫ z, ∫ w, χ z * (g w * L08_radialKernel t (z - w)) := by
      apply integral_congr_ae
      filter_upwards with z
      rw [integral_const_mul]
      congr 1
      apply integral_congr_ae
      filter_upwards with w
      exact mul_comm _ _
    _ = ∫ w, ∫ z, χ z * (g w * L08_radialKernel t (z - w)) :=
      integral_integral_swap hprod
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with w
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with z
      have hsym : L08_radialKernel t (z - w) = L08_radialKernel t (w - z) := by
        simpa only [neg_sub] using L08_radialKernel_neg t (w - z)
      rw [hsym]
      ring

theorem L08_integrable_radialConvolution {t : ℝ} (ht : 0 < t) {g : ℂ → ℝ}
    (hg : Integrable g volume) :
    Integrable (fun z : ℂ ↦ ∫ w, L08_radialKernel t (z - w) * g w) volume := by
  have h := hg.integrable_convolution (ContinuousLinearMap.mul ℝ ℝ)
    (integrable_of_integral_eq_one (L08_integral_radialKernel ht))
  convert h using 1
  funext z
  rw [convolution_def]
  apply integral_congr_ae
  filter_upwards with w
  exact mul_comm _ _

theorem L08_radialConvolution_lipschitz_approx' {t : ℝ} (ht : 0 < t)
    {χ : ℂ → ℝ} {C : NNReal} (hχ : LipschitzWith C χ) (z : ℂ) :
    |(∫ w, L08_radialKernel t (z - w) * χ w) - χ z| ≤ (C : ℝ) * (2 * t) := by
  have h := L08_radialConvolution_lipschitz_approx ht hχ z
  have heq := convolution_eq_swap (L := ContinuousLinearMap.mul ℝ ℝ)
    (μ := (volume : Measure ℂ)) (f := L08_radialKernel t) (g := χ) (x := z)
  change (∫ w, L08_radialKernel t w * χ (z - w)) =
    ∫ w, L08_radialKernel t (z - w) * χ w at heq
  rwa [heq] at h

/-- The weighted smoothing defect is uniformly small for an L¹-bounded
family. Only a Lipschitz bound on the test function is required. -/
theorem L08_radialConvolution_weighted_defect_bound {t : ℝ} (ht : 0 < t)
    {g χ : ℂ → ℝ} (hg : Integrable g volume) {C : NNReal}
    (hχ : LipschitzWith C χ) (hsχ : HasCompactSupport χ) :
    |∫ z, χ z * ((∫ w, L08_radialKernel t (z - w) * g w) - g z)| ≤
      ((C : ℝ) * (2 * t)) * ∫ w, |g w| := by
  let p : ℂ → ℝ := fun z ↦ ∫ w, L08_radialKernel t (z - w) * g w
  let ψ : ℂ → ℝ := fun z ↦ ∫ w, L08_radialKernel t (z - w) * χ w
  let D := (C : ℝ) * (2 * t)
  obtain ⟨B, hB⟩ := hsχ.exists_bound_of_continuous hχ.continuous
  have hχi : Integrable χ volume := hχ.continuous.integrable_of_hasCompactSupport hsχ
  have hψ : Continuous ψ := (L08_contDiff_radialConvolution ht hχi).continuous
  have hD (w : ℂ) : ‖ψ w - χ w‖ ≤ D := L08_radialConvolution_lipschitz_approx' ht hχ w
  have he : Integrable (fun w ↦ g w * (ψ w - χ w)) volume :=
    hg.mul_bdd (hψ.sub hχ.continuous).aestronglyMeasurable (Filter.Eventually.of_forall hD)
  have hgχ : Integrable (fun w ↦ g w * χ w) volume :=
    hg.mul_bdd hχ.continuous.aestronglyMeasurable (Filter.Eventually.of_forall hB)
  have hgψ : Integrable (fun w ↦ g w * ψ w) volume := by
    apply (he.add hgχ).congr
    filter_upwards with w
    change g w * (ψ w - χ w) + g w * χ w = g w * ψ w
    ring
  have hχp : Integrable (fun w ↦ χ w * p w) volume :=
    (L08_integrable_radialConvolution ht hg).bdd_mul hχ.continuous.aestronglyMeasurable
      (Filter.Eventually.of_forall hB)
  have hχg : Integrable (fun w ↦ χ w * g w) volume := by
    simpa only [mul_comm] using hgχ
  have heq : (∫ z, χ z * (p z - g z)) = ∫ w, g w * (ψ w - χ w) := by
    calc
      _ = (∫ z, χ z * p z) - ∫ z, χ z * g z := by
        simp_rw [mul_sub]
        exact integral_sub hχp hχg
      _ = (∫ w, g w * ψ w) - ∫ w, g w * χ w := by
        rw [L08_radialConvolution_adjoint ht hg hχ.continuous hsχ]
        congr 1
        apply integral_congr_ae
        filter_upwards with w
        exact mul_comm _ _
      _ = _ := by
        rw [← integral_sub hgψ hgχ]
        apply integral_congr_ae
        filter_upwards with w
        ring
  change |∫ z, χ z * (p z - g z)| ≤ D * ∫ w, |g w|
  rw [heq]
  have hn := norm_integral_le_of_norm_le (hg.norm.mul_const D)
    (Filter.Eventually.of_forall fun w ↦
      (norm_mul (g w) (ψ w - χ w)).le.trans
        (mul_le_mul_of_nonneg_left (hD w) (norm_nonneg (g w))))
  rw [Real.norm_eq_abs, integral_mul_const] at hn
  exact hn.trans_eq (mul_comm _ _)

/-- Positivity on the support of a test function turns the weighted defect
estimate into a local L¹ estimate. The comparison is only needed a.e. -/
theorem L08_radialConvolution_L1_error_on {t : ℝ} (ht : 0 < t)
    {g χ : ℂ → ℝ} (hg : Integrable g volume) {C : NNReal}
    (hχ : LipschitzWith C χ) (hsχ : HasCompactSupport χ)
    (hχ0 : ∀ z, 0 ≤ χ z) {K : Set ℂ} (hK : MeasurableSet K)
    (hχ1 : ∀ z ∈ K, 1 ≤ χ z)
    (hmajor : ∀ᵐ z ∂volume, z ∈ Function.support χ →
      g z ≤ ∫ w, L08_radialKernel t (z - w) * g w) :
    (∫ z in K, |(∫ w, L08_radialKernel t (z - w) * g w) - g z|) ≤
      ((C : ℝ) * (2 * t)) * ∫ w, |g w| := by
  let p : ℂ → ℝ := fun z ↦ ∫ w, L08_radialKernel t (z - w) * g w
  have hp : Integrable p volume := L08_integrable_radialConvolution ht hg
  have hi : Integrable (fun z ↦ |p z - g z|) volume := (hp.sub hg).norm
  obtain ⟨B, hB⟩ := hsχ.exists_bound_of_continuous hχ.continuous
  have hw : Integrable (fun z ↦ χ z * (p z - g z)) volume :=
    (hp.sub hg).bdd_mul hχ.continuous.aestronglyMeasurable (Filter.Eventually.of_forall hB)
  have hn : ∀ᵐ z ∂volume, 0 ≤ χ z * (p z - g z) := by
    filter_upwards [hmajor] with z hz
    by_cases hzero : χ z = 0
    · simp only [hzero, zero_mul, le_refl]
    · exact mul_nonneg (hχ0 z) (sub_nonneg.mpr (hz hzero))
  have hpoint : ∀ᵐ z ∂volume.restrict K, |p z - g z| ≤ χ z * (p z - g z) := by
    filter_upwards [ae_restrict_of_ae hmajor, ae_restrict_mem hK] with z hz hzK
    have hpos : χ z ≠ 0 := ne_of_gt ((by norm_num : (0 : ℝ) < 1).trans_le (hχ1 z hzK))
    have hd : 0 ≤ p z - g z := sub_nonneg.mpr (hz hpos)
    rw [abs_of_nonneg hd]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (hχ1 z hzK) hd
  calc
    _ ≤ ∫ z in K, χ z * (p z - g z) :=
      integral_mono_ae (hi.mono_measure Measure.restrict_le_self)
        (hw.mono_measure Measure.restrict_le_self) hpoint
    _ ≤ ∫ z, χ z * (p z - g z) := setIntegral_le_integral hw hn
    _ ≤ |∫ z, χ z * (p z - g z)| := le_abs_self _
    _ ≤ _ := L08_radialConvolution_weighted_defect_bound ht hg hχ hsχ

/-- A compact truncation leaves the convolution unchanged whenever the
whole kernel neighborhood lies in that truncation. -/
theorem L08_radialConvolution_indicator_eq {t : ℝ} (ht : 0 < t)
    (f : ℂ → ℝ) {S : Set ℂ} {z : ℂ} (hball : Metric.closedBall z (2 * t) ⊆ S) :
    (∫ w, L08_radialKernel t (z - w) * S.indicator f w) =
      ∫ w, L08_radialKernel t (z - w) * f w := by
  apply integral_congr_ae
  filter_upwards with w
  by_cases hw : w ∈ S
  · rw [Set.indicator_of_mem hw]
  · have hk : L08_radialKernel t (z - w) = 0 := by
      by_contra hne
      have hs := L08_radialKernel_tsupport_subset ht (subset_tsupport _ hne)
      have hnorm : ‖z - w‖ ≤ 2 * t := by
        simpa only [Metric.mem_closedBall, dist_zero_right] using hs
      apply hw
      apply hball
      rw [Metric.mem_closedBall, dist_eq_norm]
      simpa only [norm_sub_rev] using hnorm
    rw [hk, zero_mul, zero_mul]

/-- The local L¹ smoothing estimate for the original extended-real
potential, after a compact truncation outside the kernel neighborhoods. -/
theorem L08_subharmonic_radial_L1_error {O S K : Set ℂ} {u : ℂ → EReal}
    (hu : LeafCandidates.DiscSubharmonic O u) (hL1 : LeafCandidates.LocallyL1 O u)
    (hS : IsCompact S) (hSO : S ⊆ O) (hK : MeasurableSet K)
    {χ : ℂ → ℝ} {C : NNReal} (hχ : LipschitzWith C χ) (hsχ : HasCompactSupport χ)
    (hχ0 : ∀ z, 0 ≤ χ z) (hχ1 : ∀ z ∈ K, 1 ≤ χ z) {t : ℝ} (ht : 0 < t)
    (hballs : ∀ z ∈ Function.support χ, Metric.closedBall z (2 * t) ⊆ S) :
    (∫ z in K, |(∫ w, L08_radialKernel t (z - w) *
      S.indicator (fun w ↦ (u w).toReal) w) - (u z).toReal|) ≤
      ((C : ℝ) * (2 * t)) * ∫ w in S, |(u w).toReal| := by
  let g : ℂ → ℝ := S.indicator (fun w ↦ (u w).toReal)
  have hgi : Integrable g volume := (integrable_indicator_iff hS.measurableSet).mpr (hL1 S hS hSO).2
  have hfin : ∀ᵐ z ∂volume, z ∈ S → u z ≠ ⊥ ∧ u z ≠ ⊤ :=
    (ae_restrict_iff' hS.measurableSet).mp (hL1 S hS hSO).1
  have hmajor : ∀ᵐ z ∂volume, z ∈ Function.support χ →
      g z ≤ ∫ w, L08_radialKernel t (z - w) * g w := by
    filter_upwards [hfin] with z hz
    intro hzχ
    have hball := hballs z hzχ
    have hzS := hball (Metric.mem_closedBall_self (by positivity : 0 ≤ 2 * t))
    obtain ⟨hzbot, hztop⟩ := hz hzS
    have h := L08_subharmonic_le_radialConvolution hu hL1 ht (hball.trans hSO)
    apply EReal.coe_le_coe_iff.mp
    change ((S.indicator (fun w ↦ (u w).toReal) z : ℝ) : EReal) ≤ _
    rw [Set.indicator_of_mem hzS, EReal.coe_toReal hztop hzbot,
      L08_radialConvolution_indicator_eq ht (fun w ↦ (u w).toReal) hball]
    exact h
  have hKS : K ⊆ S := by
    intro z hz
    have hzχ : z ∈ Function.support χ :=
      ne_of_gt ((by norm_num : (0 : ℝ) < 1).trans_le (hχ1 z hz))
    exact hballs z hzχ (Metric.mem_closedBall_self (by positivity : 0 ≤ 2 * t))
  have herr := L08_radialConvolution_L1_error_on ht hgi hχ hsχ hχ0 hK hχ1 hmajor
  have hleft : (∫ z in K, |(∫ w, L08_radialKernel t (z - w) * g w) - g z|) =
      ∫ z in K, |(∫ w, L08_radialKernel t (z - w) * g w) - (u z).toReal| := by
    apply setIntegral_congr_fun hK
    intro z hz
    change |(∫ w, L08_radialKernel t (z - w) * g w) - S.indicator (fun w ↦ (u w).toReal) z| = _
    rw [Set.indicator_of_mem (hKS hz)]
  have hright : (∫ w, |g w|) = ∫ w in S, |(u w).toReal| := by
    rw [← integral_indicator hS.measurableSet]
    apply integral_congr_ae
    filter_upwards with w
    by_cases hw : w ∈ S
    · simp only [g, Set.indicator_of_mem hw]
    · simp only [g, Set.indicator_of_notMem hw, abs_zero]
  rw [hleft, hright] at herr
  exact herr

theorem L08_exists_smooth_compact_majorant {O K : Set ℂ} (hO : IsOpen O)
    (hK : IsCompact K) (hKO : K ⊆ O) :
    ∃ χ : ℂ → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ O ∧
      (∀ z, 0 ≤ χ z) ∧ (∀ z ∈ K, χ z = 1) := by
  obtain ⟨δ, hδ, hδO⟩ := hK.exists_cthickening_subset_open hO hKO
  obtain ⟨χ, hχ, hχrange, hχsupp, hχone⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞)) Metric.isOpen_thickening hK.isClosed
      (Metric.self_subset_thickening hδ K)
  have hsupp : tsupport χ ⊆ Metric.cthickening δ K := by
    rw [tsupport, hχsupp]
    exact Metric.closure_thickening_subset_cthickening δ K
  have hcompact : HasCompactSupport χ :=
    hK.cthickening.of_isClosed_subset (isClosed_tsupport χ) hsupp
  exact ⟨χ, hχ, hcompact, hsupp.trans hδO,
    fun z ↦ (hχrange (Set.mem_range_self z)).1, fun z hz ↦ (hχone z).mp hz⟩

/-- The exact compactness assumptions give one compact truncation and a
uniform local L¹ smoothing error tending to zero with the radius. -/
theorem L08_uniform_radial_L1_approx {O : Set ℂ} {u : ℕ → ℂ → EReal}
    (hO : IsOpen O) (hu : ∀ j, LeafCandidates.DiscSubharmonic O (u j) ∧
      LeafCandidates.LocallyL1 O (u j))
    (hbound : ∀ S : Set ℂ, IsCompact S → S ⊆ O → ∃ B : ℝ, ∀ j,
      ∫ z in S, |(u j z).toReal| ≤ B)
    {K : Set ℂ} (hK : IsCompact K) (hKO : K ⊆ O) :
    ∃ (S : Set ℂ) (T M : ℝ), IsCompact S ∧ S ⊆ O ∧ K ⊆ S ∧ 0 < T ∧ 0 ≤ M ∧
      (∀ j, Integrable (S.indicator (fun w ↦ (u j w).toReal)) volume) ∧
      ∀ j t, 0 < t → t ≤ T →
        (∫ z in K, |(∫ w, L08_radialKernel t (z - w) *
          S.indicator (fun w ↦ (u j w).toReal) w) - (u j z).toReal|) ≤ M * t := by
  obtain ⟨χ, hχ, hsχ, hsχO, hχ0, hχ1⟩ := L08_exists_smooth_compact_majorant hO hK hKO
  obtain ⟨C, hLip⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hsχ hχ (by simp)
  obtain ⟨η, hη, hηO⟩ := hsχ.exists_cthickening_subset_open hO hsχO
  let S := Metric.cthickening η (tsupport χ)
  have hS : IsCompact S := hsχ.cthickening
  have hKS : K ⊆ S := by
    intro z hz
    apply Metric.self_subset_cthickening (tsupport χ)
    apply subset_tsupport χ
    change χ z ≠ 0
    rw [hχ1 z hz]
    norm_num
  obtain ⟨B, hB⟩ := hbound S hS hηO
  refine ⟨S, η / 2, (C : ℝ) * 2 * max B 0, hS, hηO, hKS, half_pos hη, by positivity, ?_, ?_⟩
  · intro j
    exact (integrable_indicator_iff hS.measurableSet).mpr ((hu j).2 S hS hηO).2
  · intro j t ht htT
    have hballs : ∀ z ∈ Function.support χ, Metric.closedBall z (2 * t) ⊆ S := by
      intro z hz
      exact (Metric.closedBall_subset_closedBall (show 2 * t ≤ η by linarith)).trans
        (Metric.closedBall_subset_cthickening (subset_tsupport χ hz) η)
    have herr := L08_subharmonic_radial_L1_error (hu j).1 (hu j).2 hS hηO hK.measurableSet
      hLip hsχ hχ0 (fun z hz ↦ by rw [hχ1 z hz]) ht hballs
    apply herr.trans
    calc
      _ ≤ ((C : ℝ) * (2 * t)) * max B 0 :=
        mul_le_mul_of_nonneg_left ((hB j).trans (le_max_left _ _)) (by positivity)
      _ = _ := by ring

theorem L08_integrable_radialConvolution_integrand {t : ℝ} (ht : 0 < t)
    {g : ℂ → ℝ} (hg : Integrable g volume) (z : ℂ) :
    Integrable (fun w ↦ L08_radialKernel t (z - w) * g w) volume := by
  obtain ⟨A, hA⟩ := (L08_radialKernel_hasCompactSupport ht).exists_bound_of_continuous
    (L08_contDiff_radialKernel t).continuous
  exact hg.bdd_mul
    ((L08_contDiff_radialKernel t).continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun w ↦ hA (z - w))

theorem L08_radialConvolution_norm_le {t : ℝ} (ht : 0 < t)
    {g : ℂ → ℝ} (hg : Integrable g volume) {A : ℝ}
    (hA : ∀ w, ‖L08_radialKernel t w‖ ≤ A) (z : ℂ) :
    ‖∫ w, L08_radialKernel t (z - w) * g w‖ ≤ A * ∫ w, |g w| := by
  have h := norm_integral_le_of_norm_le (hg.norm.const_mul A)
    (Filter.Eventually.of_forall fun w ↦
      (norm_mul (L08_radialKernel t (z - w)) (g w)).le.trans
        (mul_le_mul_of_nonneg_right (hA (z - w)) (norm_nonneg _)))
  simpa only [integral_const_mul, Real.norm_eq_abs] using h

/-- At a fixed scale, an L¹ bound gives a common Lipschitz constant for
all the smoothed functions. -/
theorem L08_radialConvolution_lipschitz {t : ℝ} (ht : 0 < t)
    {g : ℂ → ℝ} (hg : Integrable g volume) {C : NNReal}
    (hC : LipschitzWith C (L08_radialKernel t)) {M : ℝ} (hM : 0 ≤ M)
    (hgM : (∫ w, |g w|) ≤ M) :
    LipschitzWith (C * M.toNNReal) (fun z : ℂ ↦ ∫ w, L08_radialKernel t (z - w) * g w) := by
  apply LipschitzWith.of_dist_le_mul
  intro z z'
  rw [dist_eq_norm, ← integral_sub (L08_integrable_radialConvolution_integrand ht hg z)
    (L08_integrable_radialConvolution_integrand ht hg z')]
  have hb (w : ℂ) :
      ‖L08_radialKernel t (z - w) * g w - L08_radialKernel t (z' - w) * g w‖ ≤
        ((C : ℝ) * dist z z') * ‖g w‖ := by
    have h := hC.dist_le_mul (z - w) (z' - w)
    rw [dist_sub_right] at h
    rw [dist_eq_norm] at h
    rw [← sub_mul, norm_mul]
    exact mul_le_mul_of_nonneg_right h (norm_nonneg _)
  have hn := norm_integral_le_of_norm_le (hg.norm.const_mul ((C : ℝ) * dist z z'))
    (Filter.Eventually.of_forall hb)
  rw [integral_const_mul] at hn
  have hn' := hn.trans (mul_le_mul_of_nonneg_left hgM (by positivity : 0 ≤ (C : ℝ) * dist z z'))
  simp only [NNReal.coe_mul, Real.coe_toNNReal M hM]
  convert hn' using 1 <;> ring

theorem L08_radialConvolution_uniform_bounds {t : ℝ} (ht : 0 < t)
    {g : ℕ → ℂ → ℝ} (hg : ∀ j, Integrable (g j) volume)
    {B : ℝ} (hB : ∀ j, (∫ w, |g j w|) ≤ B) :
    ∃ (A : ℝ) (C : NNReal), 0 ≤ A ∧
      (∀ j z, |∫ w, L08_radialKernel t (z - w) * g j w| ≤ A) ∧
      (∀ j, LipschitzWith C (fun z : ℂ ↦ ∫ w, L08_radialKernel t (z - w) * g j w)) := by
  obtain ⟨D, hD⟩ := (L08_radialKernel_hasCompactSupport ht).exists_bound_of_continuous
    (L08_contDiff_radialKernel t).continuous
  obtain ⟨L, hLip⟩ := ContDiff.lipschitzWith_of_hasCompactSupport
    (L08_radialKernel_hasCompactSupport ht) (L08_contDiff_radialKernel t) (by simp)
  refine ⟨max D 0 * max B 0, L * (max B 0).toNNReal, by positivity, ?_, ?_⟩
  · intro j z
    have h := L08_radialConvolution_norm_le ht (hg j)
      (fun w ↦ (hD w).trans (le_max_left D 0)) z
    exact h.trans (mul_le_mul_of_nonneg_left ((hB j).trans (le_max_left B 0)) (le_max_right D 0))
  · intro j
    exact L08_radialConvolution_lipschitz ht (hg j) hLip (le_max_right B 0)
      ((hB j).trans (le_max_left B 0))

/-- Arzelà–Ascoli in the explicit uniform-Cauchy form used below. -/
theorem L08_uniformlyCauchy_subseq_of_bounded_lipschitz {K : Set ℂ} (hK : IsCompact K)
    {f : ℕ → ℂ → ℝ} {A : ℝ} {C : NNReal}
    (hA : ∀ j z, z ∈ K → |f j z| ≤ A) (hLip : ∀ j, LipschitzWith C (f j)) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ i ≥ N, ∀ j ≥ N, ∀ z ∈ K, |f (σ i) z - f (σ j) z| < ε := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let F : ℕ → (K →ᵇ ℝ) := fun j ↦ BoundedContinuousFunction.mkOfCompact
    ⟨fun z ↦ f j z, (hLip j).continuous.comp continuous_subtype_val⟩
  have hLF (j : ℕ) : LipschitzWith C (F j) := by
    have h := (hLip j).comp (LipschitzWith.subtype_val K)
    rw [mul_one] at h
    convert h using 1
    funext z
    exact BoundedContinuousFunction.mkOfCompact_apply _ z
  have heq : Equicontinuous ((↑) : Set.range F → K → ℝ) := by
    apply UniformEquicontinuous.equicontinuous
    apply LipschitzWith.uniformEquicontinuous _ C
    intro h
    obtain ⟨j, hj⟩ := h.2
    change LipschitzWith C (h.1 : K → ℝ)
    rw [← hj]
    exact hLF j
  have hc : IsCompact (closure (Set.range F)) := BoundedContinuousFunction.arzela_ascoli
    (Set.Icc (-A) A) isCompact_Icc (Set.range F)
    (fun h z hh ↦ by
      obtain ⟨j, rfl⟩ := hh
      exact abs_le.mp (hA j z z.2)) heq
  obtain ⟨v, _, σ, hσ, hconv⟩ := hc.tendsto_subseq (fun j ↦ subset_closure (Set.mem_range_self j))
  refine ⟨σ, hσ, ?_⟩
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hconv (ε / 2) (half_pos hε)
  refine ⟨N, ?_⟩
  intro i hi j hj z hz
  have hi' : dist (F (σ i)) v < ε / 2 := hN i hi
  have hj' : dist (F (σ j)) v < ε / 2 := hN j hj
  have hdist : dist (F (σ i)) (F (σ j)) < ε := by
    have := dist_triangle_right (F (σ i)) (F (σ j)) v
    linarith
  have hp := BoundedContinuousFunction.dist_coe_le_dist (f := F (σ i)) (g := F (σ j))
    (⟨z, hz⟩ : K)
  change |f (σ i) z - f (σ j) z| ≤ dist (F (σ i)) (F (σ j)) at hp
  exact hp.trans_lt hdist

theorem L08_isCompact_closure_bounded_lipschitz {X : Type*} [PseudoMetricSpace X]
    [CompactSpace X] (F : ℕ → (X →ᵇ ℝ)) {A : ℝ} {C : NNReal}
    (hA : ∀ j x, |F j x| ≤ A) (hLip : ∀ j, LipschitzWith C (F j)) :
    IsCompact (closure (Set.range F)) := by
  have heq : Equicontinuous ((↑) : Set.range F → X → ℝ) := by
    apply UniformEquicontinuous.equicontinuous
    apply LipschitzWith.uniformEquicontinuous _ C
    intro h
    obtain ⟨j, hj⟩ := h.2
    rw [← hj]
    exact hLip j
  exact BoundedContinuousFunction.arzela_ascoli (Set.Icc (-A) A) isCompact_Icc (Set.range F)
    (fun h x hh ↦ by obtain ⟨j, rfl⟩ := hh; exact abs_le.mp (hA j x)) heq

/-- A single subsequence is uniformly Cauchy for a countable collection of
bounded equicontinuous families on compact subsets. -/
theorem L08_uniformlyCauchy_subseq_countable {ι : Type*} [Countable ι]
    (K : ι → Set ℂ) (hK : ∀ m, IsCompact (K m))
    (f : ι → ℕ → ℂ → ℝ) (A : ι → ℝ) (C : ι → NNReal)
    (hA : ∀ m j z, z ∈ K m → |f m j z| ≤ A m)
    (hLip : ∀ m j, LipschitzWith (C m) (f m j)) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∀ m ε, 0 < ε →
      ∃ N : ℕ, ∀ i ≥ N, ∀ j ≥ N, ∀ z ∈ K m, |f m (σ i) z - f m (σ j) z| < ε := by
  letI (m : ι) : CompactSpace (K m) := isCompact_iff_compactSpace.mp (hK m)
  let F : ∀ m : ι, ℕ → ((K m) →ᵇ ℝ) := fun m j ↦ BoundedContinuousFunction.mkOfCompact
    ⟨fun z ↦ f m j z, (hLip m j).continuous.comp continuous_subtype_val⟩
  have hLF (m : ι) (j : ℕ) : LipschitzWith (C m) (F m j) := by
    have h := (hLip m j).comp (LipschitzWith.subtype_val (K m))
    rw [mul_one] at h
    convert h using 1
    funext z
    exact BoundedContinuousFunction.mkOfCompact_apply _ z
  have hcompact (m : ι) : IsCompact (closure (Set.range (F m))) :=
    L08_isCompact_closure_bounded_lipschitz (F m) (fun j z ↦ hA m j z z.2) (hLF m)
  let P := ∀ m : ι, {v : (K m) →ᵇ ℝ // v ∈ closure (Set.range (F m))}
  letI (m : ι) : CompactSpace {v : (K m) →ᵇ ℝ // v ∈ closure (Set.range (F m))} :=
    isCompact_iff_compactSpace.mp (hcompact m)
  let p : ℕ → P := fun j m ↦ ⟨F m j, subset_closure (Set.mem_range_self j)⟩
  obtain ⟨v, σ, hσ, hconv⟩ := CompactSpace.tendsto_subseq p
  refine ⟨σ, hσ, ?_⟩
  intro m ε hε
  have hproj : Continuous (fun q : P ↦ (q m).1) := continuous_subtype_val.comp (continuous_apply m)
  have hmconv := (hproj.tendsto v).comp hconv
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hmconv (ε / 2) (half_pos hε)
  refine ⟨N, ?_⟩
  intro i hi j hj z hz
  have hi' : dist (F m (σ i)) (v m).1 < ε / 2 := hN i hi
  have hj' : dist (F m (σ j)) (v m).1 < ε / 2 := hN j hj
  have hdist : dist (F m (σ i)) (F m (σ j)) < ε := by
    have := dist_triangle_right (F m (σ i)) (F m (σ j)) (v m).1
    linarith
  have hp := BoundedContinuousFunction.dist_coe_le_dist (f := F m (σ i)) (g := F m (σ j))
    (⟨z, hz⟩ : K m)
  change |f m (σ i) z - f m (σ j) z| ≤ dist (F m (σ i)) (F m (σ j)) at hp
  exact hp.trans_lt hdist

theorem L08_dist_toL1_eq_integral_abs {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g : α → ℝ} (hf : Integrable f μ) (hg : Integrable g μ) :
    dist (hf.toL1 f) (hg.toL1 g) = ∫ z, |f z - g z| ∂μ := by
  rw [L1.dist_eq_integral_dist]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toL1, hg.coeFn_toL1] with z hz hgz
  rw [hz, hgz, Real.dist_eq]

theorem L08_dist_toL1_on_le_const {K : Set ℂ} (hK : IsCompact K)
    {f g : ℂ → ℝ} (hf : IntegrableOn f K volume) (hg : IntegrableOn g K volume)
    {ε : ℝ} (hε : ∀ z ∈ K, |f z - g z| ≤ ε) :
    dist (hf.toL1 f) (hg.toL1 g) ≤ ε * volume.real K := by
  change Integrable f (volume.restrict K) at hf
  change Integrable g (volume.restrict K) at hg
  rw [L08_dist_toL1_eq_integral_abs]
  have h := norm_setIntegral_le_of_norm_le_const (μ := (volume : Measure ℂ))
    (s := K) (f := fun z ↦ |f z - g z|) hK.measure_lt_top
    (fun z hz ↦ (by simpa only [Real.norm_eq_abs, abs_abs] using hε z hz : ‖|f z - g z|‖ ≤ ε))
  simpa only [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ ↦ abs_nonneg _)] using h

theorem L08_integral_abs_indicator (f : ℂ → ℝ) {S : Set ℂ} (hS : MeasurableSet S) :
    (∫ w, |S.indicator f w|) = ∫ w in S, |f w| := by
  rw [← integral_indicator hS]
  apply integral_congr_ae
  filter_upwards with w
  by_cases hw : w ∈ S
  · simp only [Set.indicator_of_mem hw]
  · simp only [Set.indicator_of_notMem hw, abs_zero]

/-- Every planar open set has a nested sequence of compact subsets that
eventually contains each compact subset of the open set. -/
theorem L08_exists_compact_exhaustion {O : Set ℂ} (hO : IsOpen O) :
    ∃ K : ℕ → Set ℂ, (∀ n, IsCompact (K n)) ∧ (∀ n, K n ⊆ O) ∧ Monotone K ∧
      ∀ S : Set ℂ, IsCompact S → S ⊆ O → ∃ n, S ⊆ K n := by
  letI : LocallyCompactSpace O := hO.locallyCompactSpace
  let E := CompactExhaustion.choice O
  let K : ℕ → Set ℂ := fun n ↦ (Subtype.val : O → ℂ) '' E n
  refine ⟨K, fun n ↦ (E.isCompact n).image continuous_subtype_val, ?_, ?_, ?_⟩
  · intro n z hz
    obtain ⟨w, _, rfl⟩ := hz
    exact w.2
  · intro n m hnm
    exact Set.image_mono (E.subset hnm)
  · intro S hS hSO
    have hpre : IsCompact ((Subtype.val : O → ℂ) ⁻¹' S) := by
      apply Topology.IsEmbedding.subtypeVal.isCompact_iff.mpr
      rw [Set.image_preimage_eq_of_subset (by simpa only [Subtype.range_coe] using hSO)]
      exact hS
    obtain ⟨n, hn⟩ := E.exists_superset_of_isCompact hpre
    refine ⟨n, ?_⟩
    intro z hz
    exact ⟨⟨z, hSO hz⟩, hn hz, rfl⟩

theorem L08_integral_abs_triangle3 {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g p q : α → ℝ} (hf : Integrable f μ) (hg : Integrable g μ)
    (hp : Integrable p μ) (hq : Integrable q μ) :
    (∫ z, |f z - g z| ∂μ) ≤ (∫ z, |f z - p z| ∂μ) +
      (∫ z, |p z - q z| ∂μ) + ∫ z, |q z - g z| ∂μ := by
  have h : dist (hf.toL1 f) (hg.toL1 g) ≤
      dist (hf.toL1 f) (hp.toL1 p) + dist (hp.toL1 p) (hq.toL1 q) + dist (hq.toL1 q) (hg.toL1 g) := by
    calc
      _ ≤ dist (hf.toL1 f) (hp.toL1 p) + dist (hp.toL1 p) (hg.toL1 g) := dist_triangle _ _ _
      _ ≤ dist (hf.toL1 f) (hp.toL1 p) +
          (dist (hp.toL1 p) (hq.toL1 q) + dist (hq.toL1 q) (hg.toL1 g)) :=
        add_le_add le_rfl (dist_triangle _ _ _)
      _ = _ := by ring
  simpa only [L08_dist_toL1_eq_integral_abs] using h

theorem L08_tendsto_natScale (T : ℝ) :
    Tendsto (fun n : ℕ ↦ T / ((n : ℝ) + 1)) atTop (𝓝 0) := by
  exact tendsto_const_nhds.div_atTop
    (Filter.tendsto_atTop_add_const_right atTop 1 (tendsto_natCast_atTop_atTop (R := ℝ)))

theorem L08_integral_abs_le_const {K : Set ℂ} (hK : IsCompact K)
    {f : ℂ → ℝ} {ε : ℝ} (hε : ∀ z ∈ K, |f z| ≤ ε) :
    (∫ z in K, |f z|) ≤ ε * volume.real K := by
  have h := norm_setIntegral_le_of_norm_le_const (μ := (volume : Measure ℂ))
    (s := K) (f := fun z ↦ |f z|) hK.measure_lt_top
    (fun z hz ↦ (by simpa only [Real.norm_eq_abs, abs_abs] using hε z hz : ‖|f z|‖ ≤ ε))
  simpa only [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ ↦ abs_nonneg _)] using h

/-- Countably many local L¹ seminorms admit a common Cauchy subsequence,
using the concrete radial approximation and Arzelà–Ascoli results above. -/
theorem L08_subharmonic_L1Cauchy_subseq {O : Set ℂ} {u : ℕ → ℂ → EReal}
    (hO : IsOpen O) (hu : ∀ j, LeafCandidates.DiscSubharmonic O (u j) ∧
      LeafCandidates.LocallyL1 O (u j))
    (hbound : ∀ S : Set ℂ, IsCompact S → S ⊆ O → ∃ B : ℝ, ∀ j,
      ∫ z in S, |(u j z).toReal| ≤ B)
    (K : ℕ → Set ℂ) (hK : ∀ m, IsCompact (K m)) (hKO : ∀ m, K m ⊆ O) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∀ m ε, 0 < ε →
      ∃ N : ℕ, ∀ i ≥ N, ∀ j ≥ N,
        (∫ z in K m, |(u (σ i) z).toReal - (u (σ j) z).toReal|) < ε := by
  choose S T M hS hSO hKS hT hM hgi herr using
    (fun m ↦ L08_uniform_radial_L1_approx hO hu hbound (hK m) (hKO m))
  let g : ℕ → ℕ → ℂ → ℝ := fun m j ↦ (S m).indicator (fun z ↦ (u j z).toReal)
  have hgbound (m : ℕ) : ∃ B : ℝ, ∀ j, (∫ w, |g m j w|) ≤ B := by
    obtain ⟨B, hB⟩ := hbound (S m) (hS m) (hSO m)
    refine ⟨B, ?_⟩
    intro j
    rw [L08_integral_abs_indicator _ (hS m).measurableSet]
    exact hB j
  choose B hB using hgbound
  let t : ℕ × ℕ → ℝ := fun p ↦ T p.1 / ((p.2 : ℝ) + 1)
  have ht (p : ℕ × ℕ) : 0 < t p := div_pos (hT p.1) (by positivity)
  have htT (p : ℕ × ℕ) : t p ≤ T p.1 := by
    apply (div_le_iff₀ (by positivity : 0 < (p.2 : ℝ) + 1)).mpr
    nlinarith [mul_nonneg (hT p.1).le (Nat.cast_nonneg p.2 : 0 ≤ (p.2 : ℝ))]
  let f : (ℕ × ℕ) → ℕ → ℂ → ℝ := fun p j z ↦
    ∫ w, L08_radialKernel (t p) (z - w) * g p.1 j w
  have hfbounds (p : ℕ × ℕ) : ∃ (A : ℝ) (C : NNReal), 0 ≤ A ∧
      (∀ j z, |f p j z| ≤ A) ∧ (∀ j, LipschitzWith C (f p j)) :=
    L08_radialConvolution_uniform_bounds (ht p) (hgi p.1) (hB p.1)
  choose A C hA0 hA hLip using hfbounds
  obtain ⟨σ, hσ, hσC⟩ := L08_uniformlyCauchy_subseq_countable (fun p : ℕ × ℕ ↦ K p.1)
    (fun p ↦ hK p.1) f A C (fun p j z _ ↦ hA p j z) hLip
  refine ⟨σ, hσ, ?_⟩
  intro m ε hε
  have hsmall : Tendsto (fun l : ℕ ↦ M m * t (m, l)) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul (L08_tendsto_natScale (T m))
  obtain ⟨l, hl⟩ := ((tendsto_order.mp hsmall).2 (ε / 3) (by linarith)).exists
  let δ := ε / (3 * (volume.real (K m) + 1))
  have hδ : 0 < δ := by positivity
  obtain ⟨N, hN⟩ := hσC (m, l) δ hδ
  refine ⟨N, ?_⟩
  intro i hi j hj
  have hierr : (∫ z in K m, |(u (σ i) z).toReal - f (m, l) (σ i) z|) ≤ M m * t (m, l) := by
    simpa only [abs_sub_comm] using herr m (σ i) (t (m, l)) (ht _) (htT _)
  have hjerr : (∫ z in K m, |f (m, l) (σ j) z - (u (σ j) z).toReal|) ≤ M m * t (m, l) :=
    herr m (σ j) (t (m, l)) (ht _) (htT _)
  have hmid : (∫ z in K m, |f (m, l) (σ i) z - f (m, l) (σ j) z|) ≤
      δ * volume.real (K m) := L08_integral_abs_le_const (hK m) (fun z hz ↦ (hN i hi j hj z hz).le)
  have hmidε : δ * volume.real (K m) ≤ ε / 3 := by
    calc
      _ ≤ δ * (volume.real (K m) + 1) := mul_le_mul_of_nonneg_left (by linarith) hδ.le
      _ = _ := by
        dsimp only [δ]
        field_simp [ne_of_gt (show 0 < volume.real (K m) + 1 by positivity)]
  have htri := L08_integral_abs_triangle3 ((hu (σ i)).2 (K m) (hK m) (hKO m)).2
    ((hu (σ j)).2 (K m) (hK m) (hKO m)).2
    ((L08_integrable_radialConvolution (ht (m, l)) (hgi m (σ i))).mono_measure Measure.restrict_le_self)
    ((L08_integrable_radialConvolution (ht (m, l)) (hgi m (σ j))).mono_measure Measure.restrict_le_self)
  change (∫ z in K m, |(u (σ i) z).toReal - (u (σ j) z).toReal|) ≤
    (∫ z in K m, |(u (σ i) z).toReal - f (m, l) (σ i) z|) +
      (∫ z in K m, |f (m, l) (σ i) z - f (m, l) (σ j) z|) +
      ∫ z in K m, |f (m, l) (σ j) z - (u (σ j) z).toReal| at htri
  linarith

theorem L08_exists_L1_limit {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (f : ℕ → α → ℝ) (hf : ∀ j, Integrable (f j) μ)
    (hCauchy : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ i ≥ N, ∀ j ≥ N,
      (∫ z, |f i z - f j z| ∂μ) < ε) :
    ∃ g : α → ℝ, Integrable g μ ∧
      Tendsto (fun j ↦ ∫ z, |f j z - g z| ∂μ) atTop (𝓝 0) := by
  let U : ℕ → Lp ℝ 1 μ := fun j ↦ (hf j).toL1 (f j)
  have hU : CauchySeq U := by
    apply Metric.cauchySeq_iff.mpr
    intro ε hε
    obtain ⟨N, hN⟩ := hCauchy ε hε
    refine ⟨N, ?_⟩
    intro i hi j hj
    change dist ((hf i).toL1 (f i)) ((hf j).toL1 (f j)) < ε
    rw [L08_dist_toL1_eq_integral_abs]
    exact hN i hi j hj
  obtain ⟨v, hv⟩ := cauchySeq_tendsto_of_complete hU
  refine ⟨v, L1.integrable_coeFn v, ?_⟩
  have hd := tendsto_iff_dist_tendsto_zero.mp hv
  apply hd.congr'
  apply Filter.Eventually.of_forall
  intro j
  change dist ((hf j).toL1 (f j)) v = _
  rw [L1.dist_eq_integral_dist]
  apply integral_congr_ae
  filter_upwards [(hf j).coeFn_toL1] with z hz
  rw [hz, Real.dist_eq]

theorem L08_tendsto_toL1_of_integral {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : ℕ → α → ℝ} (hf : ∀ j, Integrable (f j) μ) {g : α → ℝ} (hg : Integrable g μ)
    (hconv : Tendsto (fun j ↦ ∫ z, |f j z - g z| ∂μ) atTop (𝓝 0)) :
    Tendsto (fun j ↦ (hf j).toL1 (f j)) atTop (𝓝 (hg.toL1 g)) := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  exact hconv.congr' (Filter.Eventually.of_forall fun j ↦ (L08_dist_toL1_eq_integral_abs (hf j) hg).symm)

theorem L08_L1_limit_unique {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : ℕ → α → ℝ} (hf : ∀ j, Integrable (f j) μ) {g h : α → ℝ}
    (hg : Integrable g μ) (hh : Integrable h μ)
    (hgconv : Tendsto (fun j ↦ ∫ z, |f j z - g z| ∂μ) atTop (𝓝 0))
    (hhconv : Tendsto (fun j ↦ ∫ z, |f j z - h z| ∂μ) atTop (𝓝 0)) : g =ᵐ[μ] h := by
  apply (Integrable.toL1_eq_toL1_iff g h hg hh).mp
  exact tendsto_nhds_unique (L08_tendsto_toL1_of_integral hf hg hgconv)
    (L08_tendsto_toL1_of_integral hf hh hhconv)

theorem L08_L1_convergence_mono_set {S T : Set ℂ} (hST : S ⊆ T)
    {f : ℕ → ℂ → ℝ} (hf : ∀ j, IntegrableOn (f j) T volume) {g : ℂ → ℝ}
    (hg : IntegrableOn g T volume)
    (hconv : Tendsto (fun j ↦ ∫ z in T, |f j z - g z|) atTop (𝓝 0)) :
    Tendsto (fun j ↦ ∫ z in S, |f j z - g z|) atTop (𝓝 0) := by
  apply squeeze_zero (fun _ ↦ integral_nonneg fun _ ↦ abs_nonneg _) _ hconv
  intro j
  exact setIntegral_mono_set ((hf j).sub hg).norm (Filter.Eventually.of_forall fun _ ↦ abs_nonneg _)
    (Filter.Eventually.of_forall hST)

/-- The compactness assumptions already yield a single real local L¹
limit. The subharmonic representative is constructed separately. -/
theorem L08_subharmonic_exists_real_L1_limit {O : Set ℂ} {u : ℕ → ℂ → EReal}
    (hO : IsOpen O) (hu : ∀ j, LeafCandidates.DiscSubharmonic O (u j) ∧
      LeafCandidates.LocallyL1 O (u j))
    (hbound : ∀ S : Set ℂ, IsCompact S → S ⊆ O → ∃ B : ℝ, ∀ j,
      ∫ z in S, |(u j z).toReal| ≤ B) :
    ∃ (σ : ℕ → ℕ) (v : ℂ → ℝ), StrictMono σ ∧
      (∀ S : Set ℂ, IsCompact S → S ⊆ O → IntegrableOn v S volume) ∧
      ∀ S : Set ℂ, IsCompact S → S ⊆ O →
        Tendsto (fun j ↦ ∫ z in S, |(u (σ j) z).toReal - v z|) atTop (𝓝 0) := by
  classical
  obtain ⟨K, hK, hKO, hmono, hcover⟩ := L08_exists_compact_exhaustion hO
  obtain ⟨σ, hσ, hCauchy⟩ := L08_subharmonic_L1Cauchy_subseq hO hu hbound K hK hKO
  have hloc (m : ℕ) : ∃ f : ℂ → ℝ, IntegrableOn f (K m) volume ∧
      Tendsto (fun j ↦ ∫ z in K m, |(u (σ j) z).toReal - f z|) atTop (𝓝 0) :=
    L08_exists_L1_limit (fun j z ↦ (u (σ j) z).toReal)
      (fun j ↦ ((hu (σ j)).2 (K m) (hK m) (hKO m)).2) (hCauchy m)
  choose f hf hconv using hloc
  have hcompat (n m : ℕ) (hnm : n ≤ m) : f n =ᵐ[volume.restrict (K n)] f m := by
    apply L08_L1_limit_unique (fun j ↦ ((hu (σ j)).2 (K n) (hK n) (hKO n)).2)
      (hf n) ((hf m).mono_set (hmono hnm)) (hconv n)
    exact L08_L1_convergence_mono_set (hmono hnm)
      (fun j ↦ ((hu (σ j)).2 (K m) (hK m) (hKO m)).2) (hf m) (hconv m)
  have hmem (z : ℂ) (hz : z ∈ O) : ∃ n, z ∈ K n := by
    obtain ⟨n, hn⟩ := hcover {z} isCompact_singleton (Set.singleton_subset_iff.mpr hz)
    exact ⟨n, hn (Set.mem_singleton z)⟩
  let idx : O → ℕ := fun z ↦ Nat.find (hmem z z.2)
  let v : ℂ → ℝ := fun z ↦ if hz : z ∈ O then f (idx ⟨z, hz⟩) z else 0
  have hveq (m : ℕ) : v =ᵐ[volume.restrict (K m)] f m := by
    have hall : ∀ᵐ z ∂volume, ∀ n : ℕ, n ≤ m → z ∈ K n → f n z = f m z := by
      apply ae_all_iff.mpr
      intro n
      by_cases hnm : n ≤ m
      · have hn := (ae_restrict_iff' (hK n).measurableSet).mp (hcompat n m hnm)
        exact hn.mono fun z hz _ ↦ hz
      · exact Filter.Eventually.of_forall fun _ hn ↦ (hnm hn).elim
    filter_upwards [ae_restrict_of_ae hall, ae_restrict_mem (hK m).measurableSet] with z hz hzK
    have hzO := hKO m hzK
    have hidx : idx ⟨z, hzO⟩ ≤ m := Nat.find_min' (hmem z hzO) hzK
    have hidxmem : z ∈ K (idx ⟨z, hzO⟩) := Nat.find_spec (hmem z hzO)
    change (if hz : z ∈ O then f (idx ⟨z, hz⟩) z else 0) = f m z
    rw [dif_pos hzO]
    exact hz _ hidx hidxmem
  have hvint (m : ℕ) : IntegrableOn v (K m) volume := (hf m).congr (hveq m).symm
  have hvconv (m : ℕ) :
      Tendsto (fun j ↦ ∫ z in K m, |(u (σ j) z).toReal - v z|) atTop (𝓝 0) := by
    apply (hconv m).congr'
    apply Filter.Eventually.of_forall
    intro j
    apply integral_congr_ae
    filter_upwards [hveq m] with z hz
    rw [hz]
  refine ⟨σ, v, hσ, ?_, ?_⟩
  · intro S hS hSO
    obtain ⟨m, hm⟩ := hcover S hS hSO
    exact (hvint m).mono_set hm
  · intro S hS hSO
    obtain ⟨m, hm⟩ := hcover S hS hSO
    exact L08_L1_convergence_mono_set hm
      (fun j ↦ ((hu (σ j)).2 (K m) (hK m) (hKO m)).2) (hvint m) (hvconv m)

theorem L08_exists_ae_subseq_of_L1 {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : ℕ → α → ℝ} (hf : ∀ j, Integrable (f j) μ) {g : α → ℝ} (hg : Integrable g μ)
    (hconv : Tendsto (fun j ↦ ∫ z, |f j z - g z| ∂μ) atTop (𝓝 0)) :
    ∃ τ : ℕ → ℕ, StrictMono τ ∧
      ∀ᵐ z ∂μ, Tendsto (fun j ↦ f (τ j) z) atTop (𝓝 (g z)) := by
  have hLp := L08_tendsto_toL1_of_integral hf hg hconv
  have hm := tendstoInMeasure_of_tendsto_Lp hLp
  have hm' : TendstoInMeasure μ f atTop g :=
    TendstoInMeasure.congr (fun j ↦ (hf j).coeFn_toL1) hg.coeFn_toL1 hm
  exact hm'.exists_seq_tendsto_ae

theorem L08_radialConvolution_sub_norm_le {t : ℝ} (ht : 0 < t)
    {g h : ℂ → ℝ} (hg : Integrable g volume) (hh : Integrable h volume) {A : ℝ}
    (hA : ∀ w, ‖L08_radialKernel t w‖ ≤ A) (z : ℂ) :
    |(∫ w, L08_radialKernel t (z - w) * g w) -
      (∫ w, L08_radialKernel t (z - w) * h w)| ≤ A * ∫ w, |g w - h w| := by
  have heq : (∫ w, L08_radialKernel t (z - w) * g w) -
      (∫ w, L08_radialKernel t (z - w) * h w) =
      ∫ w, L08_radialKernel t (z - w) * (g w - h w) := by
    rw [← integral_sub (L08_integrable_radialConvolution_integrand ht hg z)
      (L08_integrable_radialConvolution_integrand ht hh z)]
    apply integral_congr_ae
    filter_upwards with w
    ring
  rw [heq]
  exact L08_radialConvolution_norm_le ht (hg.sub hh) hA z

/-- Localizing an L¹ limit makes convergence of each fixed-scale smoothing
uniform in the evaluation point. -/
theorem L08_radialConvolution_uniform_of_L1 {t : ℝ} (ht : 0 < t)
    {g : ℕ → ℂ → ℝ} (hg : ∀ j, Integrable (g j) volume) {h : ℂ → ℝ}
    (hh : Integrable h volume)
    (hconv : Tendsto (fun j ↦ ∫ w, |g j w - h w|) atTop (𝓝 0)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ j in atTop, ∀ z : ℂ,
      |(∫ w, L08_radialKernel t (z - w) * g j w) -
        (∫ w, L08_radialKernel t (z - w) * h w)| < ε := by
  obtain ⟨A, hA⟩ := (L08_radialKernel_hasCompactSupport ht).exists_bound_of_continuous
    (L08_contDiff_radialKernel t).continuous
  have hlim : Tendsto (fun j ↦ max A 0 * ∫ w, |g j w - h w|) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hconv
  intro ε hε
  filter_upwards [(tendsto_order.mp hlim).2 ε hε] with j hj
  intro z
  exact (L08_radialConvolution_sub_norm_le ht (hg j) hh
    (fun w ↦ (hA w).trans (le_max_left A 0)) z).trans_lt hj

def L08_radialDomain (O : Set ℂ) (t : ℝ) : Set ℂ :=
  {z | Metric.closedBall z (2 * t) ⊆ O}

theorem L08_isOpen_radialDomain {O : Set ℂ} (hO : IsOpen O) (t : ℝ) :
    IsOpen (L08_radialDomain O t) := by
  apply isOpen_iff_mem_nhds.mpr
  intro z hz
  have hcont : Continuous (fun p : ℂ × ℂ ↦ p.1 + p.2) := continuous_fst.add continuous_snd
  have hnear := (isCompact_closedBall (0 : ℂ) (2 * t)).eventually_forall_of_forall_eventually
    (P := fun x w : ℂ ↦ x + w ∈ O) (x₀ := z) (fun w hw ↦
      (hcont.tendsto (z, w)).eventually (hO.mem_nhds (hz (by
        simpa only [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, sub_zero] using hw))))
  filter_upwards [hnear] with x hx
  intro w hw
  have hsub : w - x ∈ Metric.closedBall (0 : ℂ) (2 * t) := by
    simpa only [Metric.mem_closedBall, dist_eq_norm, sub_zero] using hw
  simpa only [add_sub_cancel] using hx (w - x) hsub

/-- The full local convolution is smooth wherever its compact kernel
neighborhood is contained in the open domain. -/
theorem L08_contDiffAt_radialConvolution_local {O : Set ℂ} (hO : IsOpen O)
    {f : ℂ → ℝ} (hf : ∀ S : Set ℂ, IsCompact S → S ⊆ O → IntegrableOn f S volume)
    {t : ℝ} (ht : 0 < t) {z : ℂ} (hz : z ∈ L08_radialDomain O t) :
    ContDiffAt ℝ ∞ (fun x : ℂ ↦ ∫ w, L08_radialKernel t (x - w) * f w) z := by
  obtain ⟨δ, hδ, hδD⟩ := Metric.isOpen_iff.mp (L08_isOpen_radialDomain hO t) z hz
  let S : Set ℂ := (fun p : ℂ × ℂ ↦ p.1 + p.2) ''
    (Metric.closedBall z (δ / 2) ×ˢ Metric.closedBall 0 (2 * t))
  have hS : IsCompact S := ((isCompact_closedBall z (δ / 2)).prod
    (isCompact_closedBall (0 : ℂ) (2 * t))).image (continuous_fst.add continuous_snd)
  have hSO : S ⊆ O := by
    rintro w ⟨⟨x, y⟩, hxy, rfl⟩
    have hxD := hδD ((Metric.closedBall_subset_ball (half_lt_self hδ)) hxy.1)
    apply hxD
    simpa only [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, sub_zero] using hxy.2
  have hgi : Integrable (S.indicator f) volume :=
    (integrable_indicator_iff hS.measurableSet).mpr (hf S hS hSO)
  apply (L08_contDiff_radialConvolution ht hgi).contDiffAt.congr_of_eventuallyEq
  filter_upwards [Metric.ball_mem_nhds z (half_pos hδ)] with x hx
  symm
  apply L08_radialConvolution_indicator_eq ht f
  intro w hw
  refine ⟨(x, w - x), ⟨Metric.ball_subset_closedBall hx, ?_⟩, by simp⟩
  simpa only [Metric.mem_closedBall, dist_eq_norm, sub_zero] using hw

def L08_radialRegularization (O : Set ℂ) (f : ℂ → ℝ) (t : ℝ) (z : ℂ) : EReal :=
  by
    classical
    exact if z ∈ L08_radialDomain O t then
      ((∫ w, L08_radialKernel t (z - w) * f w : ℝ) : EReal) else ⊤

theorem L08_upperSemicontinuous_radialRegularization {O : Set ℂ} (hO : IsOpen O)
    {f : ℂ → ℝ} (hf : ∀ S : Set ℂ, IsCompact S → S ⊆ O → IntegrableOn f S volume)
    {t : ℝ} (ht : 0 < t) : UpperSemicontinuous (L08_radialRegularization O f t) := by
  intro z
  by_cases hz : z ∈ L08_radialDomain O t
  · have hlocal : ContinuousAt (fun x : ℂ ↦
        ((∫ w, L08_radialKernel t (x - w) * f w : ℝ) : EReal)) z :=
      continuous_coe_real_ereal.continuousAt.comp (L08_contDiffAt_radialConvolution_local hO hf ht hz).continuousAt
    have heq : L08_radialRegularization O f t =ᶠ[𝓝 z]
        (fun x : ℂ ↦ ((∫ w, L08_radialKernel t (x - w) * f w : ℝ) : EReal)) := by
      filter_upwards [(L08_isOpen_radialDomain hO t).mem_nhds hz] with x hx
      simp only [L08_radialRegularization, if_pos hx]
    exact (hlocal.congr_of_eventuallyEq heq).upperSemicontinuousAt
  · intro a ha
    have htop : L08_radialRegularization O f t z = ⊤ := by
      simp only [L08_radialRegularization, if_neg hz]
    rw [htop] at ha
    exact (not_top_lt ha).elim

def L08_natRadius (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

def L08_uscRepresentative (O : Set ℂ) (f : ℂ → ℝ) (z : ℂ) : EReal :=
  ⨅ n : ℕ, L08_radialRegularization O f (L08_natRadius n) z

theorem L08_upperSemicontinuous_uscRepresentative {O : Set ℂ} (hO : IsOpen O)
    {f : ℂ → ℝ} (hf : ∀ S : Set ℂ, IsCompact S → S ⊆ O → IntegrableOn f S volume) :
    UpperSemicontinuous (L08_uscRepresentative O f) :=
  upperSemicontinuous_iInf fun n ↦ L08_upperSemicontinuous_radialRegularization hO hf (by
    dsimp only [L08_natRadius]
    positivity)

theorem L08_uscRepresentative_lt_top {O : Set ℂ} (hO : IsOpen O)
    (f : ℂ → ℝ) {z : ℂ} (hz : z ∈ O) : L08_uscRepresentative O f z < ⊤ := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hO z hz
  have htends : Tendsto (fun n : ℕ ↦ 2 * L08_natRadius n) atTop (𝓝 0) := by
    simpa only [L08_natRadius, mul_zero] using tendsto_const_nhds.mul (L08_tendsto_natScale 1)
  obtain ⟨n, hn⟩ := ((tendsto_order.mp htends).2 r hr).exists
  have hD : z ∈ L08_radialDomain O (L08_natRadius n) :=
    (Metric.closedBall_subset_ball hn).trans hball
  have hle := iInf_le (fun n ↦ L08_radialRegularization O f (L08_natRadius n) z) n
  rw [L08_radialRegularization, if_pos hD] at hle
  exact hle.trans_lt (EReal.coe_lt_top _)

theorem L08_integral_abs_indicator_sub (f g : ℂ → ℝ) {S : Set ℂ} (hS : MeasurableSet S) :
    (∫ w, |S.indicator f w - S.indicator g w|) = ∫ w in S, |f w - g w| := by
  have heq (w : ℂ) : S.indicator f w - S.indicator g w = S.indicator (fun w ↦ f w - g w) w := by
    by_cases hw : w ∈ S
    · simp only [Set.indicator_of_mem hw]
    · simp only [Set.indicator_of_notMem hw, sub_self]
  simp_rw [heq]
  exact L08_integral_abs_indicator _ hS

theorem L08_radialConvolution_uniform_on_compact_of_localL1 {O : Set ℂ}
    {u : ℕ → ℂ → EReal} (hL1 : ∀ j, LeafCandidates.LocallyL1 O (u j)) {f : ℂ → ℝ}
    (hf : ∀ S : Set ℂ, IsCompact S → S ⊆ O → IntegrableOn f S volume)
    (hconv : ∀ S : Set ℂ, IsCompact S → S ⊆ O →
      Tendsto (fun j ↦ ∫ w in S, |(u j w).toReal - f w|) atTop (𝓝 0))
    {t : ℝ} (ht : 0 < t) {K : Set ℂ} (hK : IsCompact K) (hKD : K ⊆ L08_radialDomain O t) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ j in atTop, ∀ z ∈ K,
      |(∫ w, L08_radialKernel t (z - w) * (u j w).toReal) -
        (∫ w, L08_radialKernel t (z - w) * f w)| < ε := by
  let S : Set ℂ := (fun p : ℂ × ℂ ↦ p.1 + p.2) '' (K ×ˢ Metric.closedBall 0 (2 * t))
  have hS : IsCompact S := (hK.prod (isCompact_closedBall (0 : ℂ) (2 * t))).image
    (continuous_fst.add continuous_snd)
  have hSO : S ⊆ O := by
    rintro w ⟨⟨x, y⟩, hxy, rfl⟩
    apply hKD hxy.1
    simpa only [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, sub_zero] using hxy.2
  have hballs {z : ℂ} (hz : z ∈ K) : Metric.closedBall z (2 * t) ⊆ S := by
    intro w hw
    refine ⟨(z, w - z), ⟨hz, ?_⟩, by simp⟩
    simpa only [Metric.mem_closedBall, dist_eq_norm, sub_zero] using hw
  have hgi (j : ℕ) : Integrable (S.indicator (fun w ↦ (u j w).toReal)) volume :=
    (integrable_indicator_iff hS.measurableSet).mpr (hL1 j S hS hSO).2
  have hfi : Integrable (S.indicator f) volume :=
    (integrable_indicator_iff hS.measurableSet).mpr (hf S hS hSO)
  have hIconv : Tendsto (fun j ↦ ∫ w, |S.indicator (fun w ↦ (u j w).toReal) w - S.indicator f w|)
      atTop (𝓝 0) := by
    apply (hconv S hS hSO).congr'
    exact Filter.Eventually.of_forall fun j ↦ (L08_integral_abs_indicator_sub _ _ hS.measurableSet).symm
  intro ε hε
  filter_upwards [L08_radialConvolution_uniform_of_L1 ht hgi hfi hIconv ε hε] with j hj
  intro z hz
  rw [← L08_radialConvolution_indicator_eq ht (fun w ↦ (u j w).toReal) (hballs hz),
    ← L08_radialConvolution_indicator_eq ht f (hballs hz)]
  exact hj z

/-- Every fixed admissible smoothing majorizes the local L¹ limit a.e.;
this inequality is inherited from the original subharmonic sequence. -/
theorem L08_real_L1_limit_le_radialConvolution_ae {O : Set ℂ} {u : ℕ → ℂ → EReal}
    (hu : ∀ j, LeafCandidates.DiscSubharmonic O (u j) ∧ LeafCandidates.LocallyL1 O (u j))
    {f : ℂ → ℝ} (hf : ∀ S : Set ℂ, IsCompact S → S ⊆ O → IntegrableOn f S volume)
    (hconv : ∀ S : Set ℂ, IsCompact S → S ⊆ O →
      Tendsto (fun j ↦ ∫ w in S, |(u j w).toReal - f w|) atTop (𝓝 0))
    {t : ℝ} (ht : 0 < t) {K : Set ℂ} (hK : IsCompact K) (hKD : K ⊆ L08_radialDomain O t) :
    ∀ᵐ z ∂volume.restrict K, f z ≤ ∫ w, L08_radialKernel t (z - w) * f w := by
  have hKO : K ⊆ O := fun z hz ↦ hKD hz (Metric.mem_closedBall_self (by positivity : 0 ≤ 2 * t))
  obtain ⟨τ, hτ, hτae⟩ := L08_exists_ae_subseq_of_L1
    (fun j ↦ ((hu j).2 K hK hKO).2) (hf K hK hKO) (hconv K hK hKO)
  have hineq (j : ℕ) : ∀ᵐ z ∂volume.restrict K,
      (u j z).toReal ≤ ∫ w, L08_radialKernel t (z - w) * (u j w).toReal := by
    filter_upwards [((hu j).2 K hK hKO).1, ae_restrict_mem hK.measurableSet] with z hz hzK
    apply EReal.coe_le_coe_iff.mp
    rw [EReal.coe_toReal hz.2 hz.1]
    exact L08_subharmonic_le_radialConvolution (hu j).1 (hu j).2 ht (hKD hzK)
  have hall : ∀ᵐ z ∂volume.restrict K, ∀ j, (u j z).toReal ≤
      ∫ w, L08_radialKernel t (z - w) * (u j w).toReal := ae_all_iff.mpr hineq
  have huni := L08_radialConvolution_uniform_on_compact_of_localL1 (fun j ↦ (hu j).2) hf hconv ht hK hKD
  filter_upwards [hτae, hall, ae_restrict_mem hK.measurableSet] with z hz hineqz hzK
  have hpt : Tendsto (fun j ↦ ∫ w, L08_radialKernel t (z - w) * (u j w).toReal) atTop
      (𝓝 (∫ w, L08_radialKernel t (z - w) * f w)) := by
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    obtain ⟨N, hN⟩ := eventually_atTop.mp (huni ε hε)
    exact ⟨N, fun j hj ↦ by simpa only [Real.dist_eq] using hN j hj z hzK⟩
  exact le_of_tendsto_of_tendsto hz (hpt.comp hτ.tendsto_atTop)
    (Filter.Eventually.of_forall fun j ↦ hineqz (τ j))

theorem L08_real_L1_limit_le_uscRepresentative_ae {O : Set ℂ} (hO : IsOpen O)
    {u : ℕ → ℂ → EReal}
    (hu : ∀ j, LeafCandidates.DiscSubharmonic O (u j) ∧ LeafCandidates.LocallyL1 O (u j))
    {f : ℂ → ℝ} (hf : ∀ S : Set ℂ, IsCompact S → S ⊆ O → IntegrableOn f S volume)
    (hconv : ∀ S : Set ℂ, IsCompact S → S ⊆ O →
      Tendsto (fun j ↦ ∫ w in S, |(u j w).toReal - f w|) atTop (𝓝 0)) :
    ∀ᵐ z ∂volume, (f z : EReal) ≤ L08_uscRepresentative O f z := by
  have hdom (t : ℝ) (ht : 0 < t) : ∀ᵐ z ∂volume, z ∈ L08_radialDomain O t →
      f z ≤ ∫ w, L08_radialKernel t (z - w) * f w := by
    obtain ⟨K, hK, hKD, _, hcover⟩ := L08_exists_compact_exhaustion (L08_isOpen_radialDomain hO t)
    have hall : ∀ᵐ z ∂volume, ∀ m : ℕ, z ∈ K m →
        f z ≤ ∫ w, L08_radialKernel t (z - w) * f w := by
      apply ae_all_iff.mpr
      intro m
      exact (ae_restrict_iff' (hK m).measurableSet).mp
        (L08_real_L1_limit_le_radialConvolution_ae hu hf hconv ht (hK m) (hKD m))
    filter_upwards [hall] with z hz
    intro hzD
    obtain ⟨m, hm⟩ := hcover {z} isCompact_singleton (Set.singleton_subset_iff.mpr hzD)
    exact hz m (hm (Set.mem_singleton z))
  have hall : ∀ᵐ z ∂volume, ∀ n : ℕ, z ∈ L08_radialDomain O (L08_natRadius n) →
      f z ≤ ∫ w, L08_radialKernel (L08_natRadius n) (z - w) * f w :=
    ae_all_iff.mpr fun n ↦ hdom _ (by dsimp only [L08_natRadius]; positivity)
  filter_upwards [hall] with z hz
  apply le_iInf
  intro n
  by_cases hzD : z ∈ L08_radialDomain O (L08_natRadius n)
  · simp only [L08_radialRegularization, if_pos hzD]
    exact EReal.coe_le_coe_iff.mpr (hz n hzD)
  · simp only [L08_radialRegularization, if_neg hzD]
    exact le_top

theorem L08_L1_of_uniform_on_compact {K : Set ℂ} (hK : IsCompact K)
    {f : ℕ → ℂ → ℝ} {g : ℂ → ℝ}
    (huni : ∀ ε : ℝ, 0 < ε → ∀ᶠ j in atTop, ∀ z ∈ K, |f j z - g z| < ε) :
    Tendsto (fun j ↦ ∫ z in K, |f j z - g z|) atTop (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Filter.Eventually.of_forall fun _ ↦ ha.trans_le (integral_nonneg fun _ ↦ abs_nonneg _)
  · intro b hb
    let δ := b / (volume.real K + 1)
    have hδ : 0 < δ := by positivity
    have hδeq : δ * (volume.real K + 1) = b := by
      dsimp only [δ]
      exact div_mul_cancel₀ _ (ne_of_gt (by positivity : 0 < volume.real K + 1))
    filter_upwards [huni δ hδ] with j hj
    have hbound := L08_integral_abs_le_const hK (fun z hz ↦ (hj z hz).le)
    have hsmall : δ * volume.real K < b := by nlinarith
    exact hbound.trans_lt hsmall

theorem L08_uniform_radial_L1_approx_with_neighborhoods {O : Set ℂ} {u : ℕ → ℂ → EReal}
    (hO : IsOpen O) (hu : ∀ j, LeafCandidates.DiscSubharmonic O (u j) ∧
      LeafCandidates.LocallyL1 O (u j))
    (hbound : ∀ S : Set ℂ, IsCompact S → S ⊆ O → ∃ B : ℝ, ∀ j,
      ∫ z in S, |(u j z).toReal| ≤ B)
    {K : Set ℂ} (hK : IsCompact K) (hKO : K ⊆ O) :
    ∃ (S : Set ℂ) (T M : ℝ), IsCompact S ∧ S ⊆ O ∧ K ⊆ S ∧ 0 < T ∧ 0 ≤ M ∧
      (∀ j, Integrable (S.indicator (fun w ↦ (u j w).toReal)) volume) ∧
      (∀ t, 0 < t → t ≤ T → ∀ z ∈ K, Metric.closedBall z (2 * t) ⊆ S) ∧
      ∀ j t, 0 < t → t ≤ T →
        (∫ z in K, |(∫ w, L08_radialKernel t (z - w) *
          S.indicator (fun w ↦ (u j w).toReal) w) - (u j z).toReal|) ≤ M * t := by
  obtain ⟨η, hη, hηO⟩ := hK.exists_cthickening_subset_open hO hKO
  let K' := Metric.cthickening η K
  have hK' : IsCompact K' := hK.cthickening
  have hKK' : K ⊆ K' := Metric.self_subset_cthickening K
  obtain ⟨S, T, M, hS, hSO, hK'S, hT, hM, hgi, herr⟩ :=
    L08_uniform_radial_L1_approx hO hu hbound hK' hηO
  refine ⟨S, min T (η / 2), M, hS, hSO, hKK'.trans hK'S,
    lt_min hT (half_pos hη), hM, hgi, ?_, ?_⟩
  · intro t ht htT z hz
    exact (Metric.closedBall_subset_closedBall (show 2 * t ≤ η by linarith [htT.trans (min_le_right T (η / 2))])).trans
      ((Metric.closedBall_subset_cthickening hz η).trans hK'S)
  · intro j t ht htT
    have hdiff : IntegrableOn (fun z ↦ |(∫ w, L08_radialKernel t (z - w) *
        S.indicator (fun w ↦ (u j w).toReal) w) - (u j z).toReal|) K' volume :=
      (((L08_integrable_radialConvolution ht (hgi j)).mono_measure Measure.restrict_le_self).sub
        ((hu j).2 K' hK' hηO).2).norm
    exact (setIntegral_mono_set hdiff (Filter.Eventually.of_forall fun _ ↦ abs_nonneg _)
      (Filter.Eventually.of_forall hKK')).trans (herr j t ht (htT.trans (min_le_left T (η / 2))))

/-- The uniform smoothing estimate passes to the real local L¹ limit. -/
theorem L08_real_L1_limit_radial_approx {O : Set ℂ} (hO : IsOpen O)
    {u : ℕ → ℂ → EReal}
    (hu : ∀ j, LeafCandidates.DiscSubharmonic O (u j) ∧ LeafCandidates.LocallyL1 O (u j))
    (hbound : ∀ S : Set ℂ, IsCompact S → S ⊆ O → ∃ B : ℝ, ∀ j,
      ∫ z in S, |(u j z).toReal| ≤ B)
    {f : ℂ → ℝ} (hf : ∀ S : Set ℂ, IsCompact S → S ⊆ O → IntegrableOn f S volume)
    (hconv : ∀ S : Set ℂ, IsCompact S → S ⊆ O →
      Tendsto (fun j ↦ ∫ w in S, |(u j w).toReal - f w|) atTop (𝓝 0))
    {K : Set ℂ} (hK : IsCompact K) (hKO : K ⊆ O) :
    ∃ T M : ℝ, 0 < T ∧ 0 ≤ M ∧ ∀ t, 0 < t → t ≤ T →
      K ⊆ L08_radialDomain O t ∧
      (∫ z in K, |(∫ w, L08_radialKernel t (z - w) * f w) - f z|) ≤ M * t := by
  obtain ⟨S, T, M, hS, hSO, _, hT, hM, hgi, hballs, herr⟩ :=
    L08_uniform_radial_L1_approx_with_neighborhoods hO hu hbound hK hKO
  refine ⟨T, M, hT, hM, ?_⟩
  intro t ht htT
  have hKD : K ⊆ L08_radialDomain O t := fun z hz ↦ (hballs t ht htT z hz).trans hSO
  refine ⟨hKD, ?_⟩
  let g : ℕ → ℂ → ℝ := fun j ↦ S.indicator (fun w ↦ (u j w).toReal)
  let h : ℂ → ℝ := S.indicator f
  let p : ℕ → ℂ → ℝ := fun j z ↦ ∫ w, L08_radialKernel t (z - w) * g j w
  let q : ℂ → ℝ := fun z ↦ ∫ w, L08_radialKernel t (z - w) * h w
  have hhi : Integrable h volume := (integrable_indicator_iff hS.measurableSet).mpr (hf S hS hSO)
  have hIconv : Tendsto (fun j ↦ ∫ w, |g j w - h w|) atTop (𝓝 0) := by
    apply (hconv S hS hSO).congr'
    exact Filter.Eventually.of_forall fun j ↦ (L08_integral_abs_indicator_sub _ _ hS.measurableSet).symm
  have hpconv : Tendsto (fun j ↦ ∫ z in K, |p j z - q z|) atTop (𝓝 0) :=
    L08_L1_of_uniform_on_compact hK (fun ε hε ↦
      (L08_radialConvolution_uniform_of_L1 ht hgi hhi hIconv ε hε).mono fun j hj z _ ↦ hj z)
  have hrawi (j : ℕ) : Integrable (fun z ↦ (u j z).toReal) (volume.restrict K) :=
    ((hu j).2 K hK hKO).2
  have hfi : Integrable f (volume.restrict K) := hf K hK hKO
  have hpi (j : ℕ) : Integrable (p j) (volume.restrict K) :=
    (L08_integrable_radialConvolution ht (hgi j)).mono_measure Measure.restrict_le_self
  have hqi : Integrable q (volume.restrict K) :=
    (L08_integrable_radialConvolution ht hhi).mono_measure Measure.restrict_le_self
  have hdist := (L08_tendsto_toL1_of_integral hrawi hfi (hconv K hK hKO)).dist
    (L08_tendsto_toL1_of_integral hpi hqi hpconv)
  have herrconv : Tendsto (fun j ↦ ∫ z in K, |p j z - (u j z).toReal|) atTop
      (𝓝 (∫ z in K, |q z - f z|)) := by
    simpa only [L08_dist_toL1_eq_integral_abs, abs_sub_comm] using hdist
  have hlim : (∫ z in K, |q z - f z|) ≤ M * t :=
    le_of_tendsto herrconv (Filter.Eventually.of_forall fun j ↦ herr j t ht htT)
  have heq : (∫ z in K, |q z - f z|) =
      ∫ z in K, |(∫ w, L08_radialKernel t (z - w) * f w) - f z| := by
    apply setIntegral_congr_fun hK.measurableSet
    intro z hz
    change |(∫ w, L08_radialKernel t (z - w) * S.indicator f w) - f z| = _
    rw [L08_radialConvolution_indicator_eq ht f (hballs t ht htT z hz)]
  rwa [heq] at hlim


theorem L08_natRadius_pos (n : ℕ) : 0 < L08_natRadius n := by
  dsimp only [L08_natRadius]
  positivity

theorem L08_tendsto_natRadius : Tendsto L08_natRadius atTop (𝓝 0) :=
  L08_tendsto_natScale 1

theorem L08_real_L1_limit_radial_tendsto {O : Set ℂ} (hO : IsOpen O)
    {u : ℕ → ℂ → EReal}
    (hu : ∀ j, LeafCandidates.DiscSubharmonic O (u j) ∧ LeafCandidates.LocallyL1 O (u j))
    (hbound : ∀ S : Set ℂ, IsCompact S → S ⊆ O → ∃ B : ℝ, ∀ j,
      ∫ z in S, |(u j z).toReal| ≤ B)
    {f : ℂ → ℝ} (hf : ∀ S : Set ℂ, IsCompact S → S ⊆ O → IntegrableOn f S volume)
    (hconv : ∀ S : Set ℂ, IsCompact S → S ⊆ O →
      Tendsto (fun j ↦ ∫ w in S, |(u j w).toReal - f w|) atTop (𝓝 0))
    {K : Set ℂ} (hK : IsCompact K) (hKO : K ⊆ O) :
    (∀ᶠ n in atTop, K ⊆ L08_radialDomain O (L08_natRadius n)) ∧
    Tendsto (fun n ↦ ∫ z in K,
      |(∫ w, L08_radialKernel (L08_natRadius n) (z - w) * f w) - f z|) atTop (𝓝 0) := by
  obtain ⟨T, M, hT, hM, happ⟩ := L08_real_L1_limit_radial_approx hO hu hbound hf hconv hK hKO
  have he : ∀ᶠ n in atTop, L08_natRadius n ≤ T :=
    ((tendsto_order.mp L08_tendsto_natRadius).2 T hT).mono fun _ h ↦ h.le
  refine ⟨he.mono fun n hn ↦ (happ _ (L08_natRadius_pos n) hn).1, ?_⟩
  apply squeeze_zero' (Filter.Eventually.of_forall fun n ↦ integral_nonneg fun z ↦ abs_nonneg _)
    (he.mono fun n hn ↦ (happ _ (L08_natRadius_pos n) hn).2)
  simpa only [mul_zero] using tendsto_const_nhds.mul L08_tendsto_natRadius

theorem L08_uscRepresentative_ae_eq_coe {O : Set ℂ} (hO : IsOpen O)
    {u : ℕ → ℂ → EReal}
    (hu : ∀ j, LeafCandidates.DiscSubharmonic O (u j) ∧ LeafCandidates.LocallyL1 O (u j))
    (hbound : ∀ S : Set ℂ, IsCompact S → S ⊆ O → ∃ B : ℝ, ∀ j,
      ∫ z in S, |(u j z).toReal| ≤ B)
    {f : ℂ → ℝ} (hf : ∀ S : Set ℂ, IsCompact S → S ⊆ O → IntegrableOn f S volume)
    (hconv : ∀ S : Set ℂ, IsCompact S → S ⊆ O →
      Tendsto (fun j ↦ ∫ w in S, |(u j w).toReal - f w|) atTop (𝓝 0))
    {K : Set ℂ} (hK : IsCompact K) (hKO : K ⊆ O) :
    ∀ᵐ z ∂volume.restrict K, L08_uscRepresentative O f z = (f z : EReal) := by
  obtain ⟨hD, hlim⟩ := L08_real_L1_limit_radial_tendsto hO hu hbound hf hconv hK hKO
  obtain ⟨N, hN⟩ := eventually_atTop.mp hD
  let F : ℕ → ℂ → ℝ := fun n z ↦ ∫ w,
    L08_radialKernel (L08_natRadius (n + N)) (z - w) * f w
  have hFi (n : ℕ) : IntegrableOn (F n) K volume := by
    apply ContinuousOn.integrableOn_compact hK
    intro z hz
    exact (L08_contDiffAt_radialConvolution_local hO hf (L08_natRadius_pos (n + N))
      (hN (n + N) (by omega) hz)).continuousAt.continuousWithinAt
  have hFlim : Tendsto (fun n ↦ ∫ z in K, |F n z - f z|) atTop (𝓝 0) :=
    hlim.comp (tendsto_add_atTop_nat N)
  obtain ⟨τ, hτ, hτae⟩ := L08_exists_ae_subseq_of_L1 hFi (hf K hK hKO) hFlim
  have hle : ∀ᵐ z ∂volume.restrict K, (f z : EReal) ≤ L08_uscRepresentative O f z :=
    ae_restrict_of_ae (L08_real_L1_limit_le_uscRepresentative_ae hO hu hf hconv)
  filter_upwards [hτae, hle, ae_restrict_mem hK.measurableSet] with z hz hlez hzK
  apply le_antisymm _ hlez
  have hcoe : Tendsto (fun j ↦ (F (τ j) z : EReal)) atTop (𝓝 (f z : EReal)) :=
    continuous_coe_real_ereal.continuousAt.tendsto.comp hz
  apply ge_of_tendsto hcoe
  apply Filter.Eventually.of_forall
  intro j
  have hbound := iInf_le (fun n ↦ L08_radialRegularization O f (L08_natRadius n) z) (τ j + N)
  have hreg : L08_radialRegularization O f (L08_natRadius (τ j + N)) z =
      (F (τ j) z : EReal) := by
    simp only [L08_radialRegularization, if_pos (hN (τ j + N) (by omega) hzK), F]
  rw [hreg] at hbound
  exact hbound

theorem L08_uscRepresentative_locallyL1 {O : Set ℂ} (hO : IsOpen O)
    {u : ℕ → ℂ → EReal}
    (hu : ∀ j, LeafCandidates.DiscSubharmonic O (u j) ∧ LeafCandidates.LocallyL1 O (u j))
    (hbound : ∀ S : Set ℂ, IsCompact S → S ⊆ O → ∃ B : ℝ, ∀ j,
      ∫ z in S, |(u j z).toReal| ≤ B)
    {f : ℂ → ℝ} (hf : ∀ S : Set ℂ, IsCompact S → S ⊆ O → IntegrableOn f S volume)
    (hconv : ∀ S : Set ℂ, IsCompact S → S ⊆ O →
      Tendsto (fun j ↦ ∫ w in S, |(u j w).toReal - f w|) atTop (𝓝 0)) :
    LeafCandidates.LocallyL1 O (L08_uscRepresentative O f) := by
  intro K hK hKO
  have heq := L08_uscRepresentative_ae_eq_coe hO hu hbound hf hconv hK hKO
  constructor
  · filter_upwards [heq] with z hz
    rw [hz]
    exact ⟨EReal.coe_ne_bot _, EReal.coe_ne_top _⟩
  · apply (hf K hK hKO).congr
    filter_upwards [heq] with z hz
    simp only [hz, EReal.toReal_coe]

theorem L08_uscRepresentative_locallyL1Converges {O : Set ℂ} (hO : IsOpen O)
    {u : ℕ → ℂ → EReal}
    (hu : ∀ j, LeafCandidates.DiscSubharmonic O (u j) ∧ LeafCandidates.LocallyL1 O (u j))
    (hbound : ∀ S : Set ℂ, IsCompact S → S ⊆ O → ∃ B : ℝ, ∀ j,
      ∫ z in S, |(u j z).toReal| ≤ B)
    {f : ℂ → ℝ} (hf : ∀ S : Set ℂ, IsCompact S → S ⊆ O → IntegrableOn f S volume)
    (hconv : ∀ S : Set ℂ, IsCompact S → S ⊆ O →
      Tendsto (fun j ↦ ∫ w in S, |(u j w).toReal - f w|) atTop (𝓝 0)) :
    LeafCandidates.LocallyL1Converges O u (L08_uscRepresentative O f) := by
  refine ⟨L08_uscRepresentative_locallyL1 hO hu hbound hf hconv, ?_⟩
  intro K hK hKO
  have heq := L08_uscRepresentative_ae_eq_coe hO hu hbound hf hconv hK hKO
  apply (hconv K hK hKO).congr'
  apply Filter.Eventually.of_forall
  intro j
  apply integral_congr_ae
  filter_upwards [heq] with z hz
  simp only [hz, EReal.toReal_coe]


theorem L08_integrable_radial_shift_prod {t : ℝ} (ht : 0 < t)
    {g : ℂ → ℝ} (hg : Integrable g volume) {S : Set ℂ} (hS : volume S ≠ ⊤) (z : ℂ) :
    Integrable (fun p : ℂ × ℂ ↦ L08_radialKernel t (z - p.1) * g (p.1 + p.2))
      (volume.prod (volume.restrict S)) := by
  have h1 : Integrable (fun _ : ℂ ↦ (1 : ℝ)) (volume.restrict S) := integrableOn_const hS
  have hbase := hg.mul_prod h1
  have hshift := (measurePreserving_add_prod volume (volume.restrict S)).integrable_comp_of_integrable hbase
  have hgi : Integrable (fun p : ℂ × ℂ ↦ g (p.1 + p.2))
      (volume.prod (volume.restrict S)) := by
    simpa only [Function.comp_def, mul_one] using hshift
  obtain ⟨B, hB⟩ := (L08_radialKernel_hasCompactSupport ht).exists_bound_of_continuous
    (L08_contDiff_radialKernel t).continuous
  exact hgi.bdd_mul
    ((L08_contDiff_radialKernel t).continuous.comp (continuous_const.sub continuous_fst)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun p ↦ hB (z - p.1))

theorem L08_radialConvolution_area_fubini {t : ℝ} (ht : 0 < t)
    {g : ℂ → ℝ} (hg : Integrable g volume) {S : Set ℂ} (hS : volume S ≠ ⊤) (z : ℂ) :
    (∫ w, L08_radialKernel t (z - w) * (∫ s in S, g (w + s))) =
      ∫ s in S, (∫ w, L08_radialKernel t (z + s - w) * g w) := by
  calc
    _ = ∫ w, ∫ s in S, L08_radialKernel t (z - w) * g (w + s) := by
      simp_rw [integral_const_mul]
    _ = ∫ s in S, ∫ w, L08_radialKernel t (z - w) * g (w + s) :=
      integral_integral_swap (L08_integrable_radial_shift_prod ht hg hS z)
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with s
      have h := integral_add_right_eq_self (μ := (volume : Measure ℂ))
        (fun w : ℂ ↦ L08_radialKernel t (z + s - w) * g w) s
      simpa only [add_sub_add_right_eq_sub] using h


/-- A fixed radial smoothing inherits the genuine annulus area submean. -/
theorem L08_radialConvolution_annulus_bound {O : Set ℂ} {u : ℂ → EReal}
    (hu : LeafCandidates.DiscSubharmonic O u) (hL1 : LeafCandidates.LocallyL1 O u)
    {z : ℂ} {a b t : ℝ} (ha : 0 < a) (hab : a < b) (ht : 0 < t)
    (hball : Metric.closedBall z (b + 2 * t) ⊆ O) :
    (∫ w, L08_radialKernel t (z - w) * (u w).toReal) * (Real.pi * (b ^ 2 - a ^ 2)) ≤
      ∫ s in {s : ℂ | a < ‖s‖ ∧ ‖s‖ < b},
        (∫ w, L08_radialKernel t (z + s - w) * (u w).toReal) := by
  let K := Metric.closedBall z (b + 2 * t)
  let S := {s : ℂ | a < ‖s‖ ∧ ‖s‖ < b}
  let A := Real.pi * (b ^ 2 - a ^ 2)
  let g : ℂ → ℝ := K.indicator (fun w ↦ (u w).toReal)
  have hK : IsCompact K := isCompact_closedBall z _
  have hS : MeasurableSet S :=
    ((isOpen_lt continuous_const continuous_norm).inter
      (isOpen_lt continuous_norm continuous_const)).measurableSet
  have hSK : S ⊆ Metric.closedBall (0 : ℂ) b := fun s hs ↦ by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hs.2.le
  have hSfin : volume S ≠ ⊤ :=
    ((measure_mono hSK).trans_lt (isCompact_closedBall (0 : ℂ) b).measure_lt_top).ne
  have hgi : Integrable g volume :=
    (integrable_indicator_iff hK.measurableSet).mpr (hL1 K hK hball).2
  have hnear {w : ℂ} (hw : L08_radialKernel t (z - w) ≠ 0) : ‖w - z‖ < 2 * t := by
    have hmem := L08_radialKernel_support_subset_ball ht hw
    simpa only [Metric.mem_ball, dist_zero_right, norm_sub_rev] using hmem
  have hwK {w : ℂ} (hw : ‖w - z‖ < 2 * t) : w ∈ K := by
    change dist w z ≤ b + 2 * t
    rw [dist_eq_norm]
    linarith
  have hsumK {w s : ℂ} (hw : ‖w - z‖ < 2 * t) (hs : ‖s‖ ≤ b) : w + s ∈ K := by
    change dist (w + s) z ≤ b + 2 * t
    rw [dist_eq_norm, show w + s - z = (w - z) + s by abel]
    exact (norm_add_le _ _).trans (by linarith)
  have hfinite : ∀ᵐ w ∂volume, w ∈ K → u w ≠ ⊥ ∧ u w ≠ ⊤ :=
    (ae_restrict_iff' hK.measurableSet).mp (hL1 K hK hball).1
  have hpoint : ∀ᵐ w ∂volume,
      L08_radialKernel t (z - w) * (g w * A) ≤
        L08_radialKernel t (z - w) * (∫ s in S, g (w + s)) := by
    filter_upwards [hfinite] with w hw
    by_cases hzero : L08_radialKernel t (z - w) = 0
    · simp only [hzero, zero_mul, le_refl]
    have hn := hnear hzero
    have hww := hw (hwK hn)
    have hwb : Metric.closedBall w b ⊆ O := by
      intro x hx
      have hnorm : ‖x - w‖ ≤ b := by simpa only [Metric.mem_closedBall, dist_eq_norm] using hx
      apply hball
      change dist x z ≤ b + 2 * t
      rw [dist_eq_norm, show x - z = (x - w) + (w - z) by abel]
      exact (norm_add_le _ _).trans (by linarith)
    have h := L08_subharmonic_annulus_bound hu hL1 ha hab hwb
      (EReal.coe_toReal hww.2 hww.1).le
    rw [← L08_integral_translate_annulus] at h
    have heq : (∫ s in S, g (w + s)) = ∫ s in S, (u (w + s)).toReal := by
      apply setIntegral_congr_fun hS
      intro s hs
      exact Set.indicator_of_mem (hsumK hn hs.2.le) _
    rw [heq]
    have hgweq : g w = (u w).toReal := Set.indicator_of_mem (hwK hn) _
    rw [hgweq]
    exact mul_le_mul_of_nonneg_left h (L08_radialKernel_nonneg ht _)
  have hprod := L08_integrable_radial_shift_prod ht hgi hSfin z
  have hright : Integrable (fun w ↦ L08_radialKernel t (z - w) * (∫ s in S, g (w + s))) volume := by
    simpa only [integral_const_mul] using hprod.integral_prod_left
  have hleft : Integrable (fun w ↦ L08_radialKernel t (z - w) * (g w * A)) volume := by
    simpa only [mul_assoc] using (L08_integrable_radialConvolution_integrand ht hgi z).mul_const A
  have hineq := integral_mono_ae hleft hright hpoint
  have hleft_eq : (∫ w, L08_radialKernel t (z - w) * (g w * A)) =
      (∫ w, L08_radialKernel t (z - w) * g w) * A := by
    simp_rw [← mul_assoc, integral_mul_const]
  rw [hleft_eq, L08_radialConvolution_area_fubini ht hgi hSfin z] at hineq
  have hballs (s : ℂ) (hs : ‖s‖ ≤ b) : Metric.closedBall (z + s) (2 * t) ⊆ K := by
    intro w hw
    have hnorm : ‖w - (z + s)‖ ≤ 2 * t := by
      simpa only [Metric.mem_closedBall, dist_eq_norm] using hw
    change dist w z ≤ b + 2 * t
    rw [dist_eq_norm, show w - z = (w - (z + s)) + s by abel]
    exact (norm_add_le _ _).trans (by linarith)
  have hballz : Metric.closedBall z (2 * t) ⊆ K := by
    simpa only [add_zero] using hballs 0 (by simpa using (ha.trans hab).le)
  change (∫ w, L08_radialKernel t (z - w) * K.indicator (fun w ↦ (u w).toReal) w) * A ≤ _ at hineq
  rw [L08_radialConvolution_indicator_eq ht _ hballz] at hineq
  convert hineq using 1
  symm
  apply setIntegral_congr_fun hS
  intro s hs
  exact L08_radialConvolution_indicator_eq ht _ (hballs s hs.2.le)


theorem L08_tendsto_integral_of_integral_abs {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {g : ℕ → α → ℝ} {f : α → ℝ} (hg : ∀ j, Integrable (g j) μ) (hf : Integrable f μ)
    (hconv : Tendsto (fun j ↦ ∫ w, |g j w - f w| ∂μ) atTop (𝓝 0)) :
    Tendsto (fun j ↦ ∫ w, g j w ∂μ) atTop (𝓝 (∫ w, f w ∂μ)) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.mp ((tendsto_order.mp hconv).2 ε hε)
  refine ⟨N, fun j hj ↦ ?_⟩
  rw [Real.dist_eq, ← integral_sub (hg j) hf]
  have hnorm := norm_integral_le_integral_norm (fun w ↦ g j w - f w) (μ := μ)
  have hnorm' : |∫ w, g j w - f w ∂μ| ≤ ∫ w, |g j w - f w| ∂μ := by
    simpa only [Real.norm_eq_abs] using hnorm
  exact hnorm'.trans_lt (hN j hj)

theorem L08_radialConvolution_tendsto_on_compact {O : Set ℂ}
    {u : ℕ → ℂ → EReal} (hL1 : ∀ j, LeafCandidates.LocallyL1 O (u j)) {f : ℂ → ℝ}
    (hf : ∀ S : Set ℂ, IsCompact S → S ⊆ O → IntegrableOn f S volume)
    (hconv : ∀ S : Set ℂ, IsCompact S → S ⊆ O →
      Tendsto (fun j ↦ ∫ w in S, |(u j w).toReal - f w|) atTop (𝓝 0))
    {t : ℝ} (ht : 0 < t) {K : Set ℂ} (hK : IsCompact K) (hKD : K ⊆ L08_radialDomain O t)
    {z : ℂ} (hz : z ∈ K) :
    Tendsto (fun j ↦ ∫ w, L08_radialKernel t (z - w) * (u j w).toReal) atTop
      (𝓝 (∫ w, L08_radialKernel t (z - w) * f w)) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (L08_radialConvolution_uniform_on_compact_of_localL1 hL1 hf hconv ht hK hKD ε hε)
  exact ⟨N, fun j hj ↦ by simpa only [Real.dist_eq] using hN j hj z hz⟩

theorem L08_real_L1_limit_radial_annulus_bound {O : Set ℂ} (hO : IsOpen O)
    {u : ℕ → ℂ → EReal}
    (hu : ∀ j, LeafCandidates.DiscSubharmonic O (u j) ∧ LeafCandidates.LocallyL1 O (u j))
    {f : ℂ → ℝ} (hf : ∀ S : Set ℂ, IsCompact S → S ⊆ O → IntegrableOn f S volume)
    (hconv : ∀ S : Set ℂ, IsCompact S → S ⊆ O →
      Tendsto (fun j ↦ ∫ w in S, |(u j w).toReal - f w|) atTop (𝓝 0))
    {z : ℂ} {a b t : ℝ} (ha : 0 < a) (hab : a < b) (ht : 0 < t)
    (hball : Metric.closedBall z (b + 2 * t) ⊆ O) :
    (∫ w, L08_radialKernel t (z - w) * f w) * (Real.pi * (b ^ 2 - a ^ 2)) ≤
      ∫ w in {w : ℂ | a < ‖w - z‖ ∧ ‖w - z‖ < b},
        (∫ s, L08_radialKernel t (w - s) * f s) := by
  let K := Metric.closedBall z b
  let S := {w : ℂ | a < ‖w - z‖ ∧ ‖w - z‖ < b}
  have hK : IsCompact K := isCompact_closedBall z b
  have hS : MeasurableSet S :=
    ((isOpen_lt continuous_const (continuous_id.sub continuous_const).norm).inter
      (isOpen_lt (continuous_id.sub continuous_const).norm continuous_const)).measurableSet
  have hSK : S ⊆ K := fun w hw ↦ by
    change dist w z ≤ b
    simpa only [dist_eq_norm] using hw.2.le
  have hKD : K ⊆ L08_radialDomain O t := by
    intro w hw x hx
    apply hball
    have hw' : dist w z ≤ b := hw
    have hx' : dist x w ≤ 2 * t := hx
    exact (dist_triangle x w z).trans (by linarith)
  let p : ℕ → ℂ → ℝ := fun j x ↦ ∫ w, L08_radialKernel t (x - w) * (u j w).toReal
  let q : ℂ → ℝ := fun x ↦ ∫ w, L08_radialKernel t (x - w) * f w
  have hpi (j : ℕ) : IntegrableOn (p j) K volume := by
    apply ContinuousOn.integrableOn_compact hK
    intro x hx
    exact (L08_contDiffAt_radialConvolution_local hO
      (fun T hT hTO ↦ ((hu j).2 T hT hTO).2) ht (hKD hx)).continuousAt.continuousWithinAt
  have hqi : IntegrableOn q K volume := by
    apply ContinuousOn.integrableOn_compact hK
    intro x hx
    exact (L08_contDiffAt_radialConvolution_local hO hf ht (hKD hx)).continuousAt.continuousWithinAt
  have hL1 := L08_L1_of_uniform_on_compact hK
    (L08_radialConvolution_uniform_on_compact_of_localL1 (fun j ↦ (hu j).2) hf hconv ht hK hKD)
  have hSconv := L08_tendsto_integral_of_integral_abs
    (fun j ↦ (hpi j).mono_set hSK) (hqi.mono_set hSK)
    (L08_L1_convergence_mono_set hSK hpi hqi hL1)
  have hzK : z ∈ K := Metric.mem_closedBall_self (ha.trans hab).le
  have hpt := (L08_radialConvolution_tendsto_on_compact (fun j ↦ (hu j).2) hf hconv ht hK hKD hzK).mul_const
    (Real.pi * (b ^ 2 - a ^ 2))
  apply le_of_tendsto_of_tendsto hpt hSconv
  apply Filter.Eventually.of_forall
  intro j
  have h := L08_radialConvolution_annulus_bound (hu j).1 (hu j).2 ha hab ht hball
  change p j z * (Real.pi * (b ^ 2 - a ^ 2)) ≤
    ∫ s in {s : ℂ | a < ‖s‖ ∧ ‖s‖ < b}, p j (z + s) at h
  rw [L08_integral_translate_annulus] at h
  exact h


theorem L08_exists_larger_closedBall {O : Set ℂ} (hO : IsOpen O)
    {z : ℂ} {b : ℝ} (hb : 0 ≤ b) (hball : Metric.closedBall z b ⊆ O) :
    ∃ R : ℝ, b < R ∧ Metric.closedBall z R ⊆ O := by
  obtain ⟨δ, hδ, hδO⟩ := (isCompact_closedBall z b).exists_cthickening_subset_open hO hball
  refine ⟨δ + b, by linarith, ?_⟩
  simpa only [cthickening_closedBall hδ.le hb z] using hδO

/-- The upper semicontinuous representative retains annulus area means;
no closure theorem for arbitrary infima of subharmonic functions is used. -/
theorem L08_uscRepresentative_annulus_bound {O : Set ℂ} (hO : IsOpen O)
    {u : ℕ → ℂ → EReal}
    (hu : ∀ j, LeafCandidates.DiscSubharmonic O (u j) ∧ LeafCandidates.LocallyL1 O (u j))
    (hbound : ∀ S : Set ℂ, IsCompact S → S ⊆ O → ∃ B : ℝ, ∀ j,
      ∫ z in S, |(u j z).toReal| ≤ B)
    {f : ℂ → ℝ} (hf : ∀ S : Set ℂ, IsCompact S → S ⊆ O → IntegrableOn f S volume)
    (hconv : ∀ S : Set ℂ, IsCompact S → S ⊆ O →
      Tendsto (fun j ↦ ∫ w in S, |(u j w).toReal - f w|) atTop (𝓝 0))
    {z : ℂ} {a b q : ℝ} (ha : 0 < a) (hab : a < b)
    (hball : Metric.closedBall z b ⊆ O) (hq : (q : EReal) ≤ L08_uscRepresentative O f z) :
    q * (Real.pi * (b ^ 2 - a ^ 2)) ≤
      ∫ w in {w : ℂ | a < ‖w - z‖ ∧ ‖w - z‖ < b}, f w := by
  let K := Metric.closedBall z b
  let S := {w : ℂ | a < ‖w - z‖ ∧ ‖w - z‖ < b}
  have hK : IsCompact K := isCompact_closedBall z b
  have hSK : S ⊆ K := fun w hw ↦ by
    change dist w z ≤ b
    simpa only [dist_eq_norm] using hw.2.le
  obtain ⟨R, hbR, hRO⟩ := L08_exists_larger_closedBall hO (ha.trans hab).le hball
  obtain ⟨hD, hlim⟩ := L08_real_L1_limit_radial_tendsto hO hu hbound hf hconv hK hball
  have hsmall : ∀ᶠ n in atTop, b + 2 * L08_natRadius n ≤ R := by
    have ht : Tendsto (fun n ↦ b + 2 * L08_natRadius n) atTop (𝓝 b) := by
      simpa only [mul_zero, add_zero] using tendsto_const_nhds.add
        (tendsto_const_nhds.mul L08_tendsto_natRadius)
    exact ((tendsto_order.mp ht).2 R hbR).mono fun _ h ↦ h.le
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hD.and hsmall)
  let F : ℕ → ℂ → ℝ := fun n x ↦ ∫ w,
    L08_radialKernel (L08_natRadius (n + N)) (x - w) * f w
  have hFi (n : ℕ) : IntegrableOn (F n) K volume := by
    apply ContinuousOn.integrableOn_compact hK
    intro x hx
    exact (L08_contDiffAt_radialConvolution_local hO hf (L08_natRadius_pos (n + N))
      ((hN (n + N) (by omega)).1 hx)).continuousAt.continuousWithinAt
  have hFconv : Tendsto (fun n ↦ ∫ w in K, |F n w - f w|) atTop (𝓝 0) :=
    hlim.comp (tendsto_add_atTop_nat N)
  have hSconv := L08_tendsto_integral_of_integral_abs
    (fun n ↦ (hFi n).mono_set hSK) ((hf K hK hball).mono_set hSK)
    (L08_L1_convergence_mono_set hSK hFi (hf K hK hball) hFconv)
  apply ge_of_tendsto hSconv
  apply Filter.Eventually.of_forall
  intro n
  have hle : (q : EReal) ≤ (F n z : EReal) := by
    apply hq.trans
    have h := iInf_le (fun k ↦ L08_radialRegularization O f (L08_natRadius k) z) (n + N)
    have hzD := (hN (n + N) (by omega)).1 (Metric.mem_closedBall_self (ha.trans hab).le)
    have hreg : L08_radialRegularization O f (L08_natRadius (n + N)) z = (F n z : EReal) := by
      simp only [L08_radialRegularization, if_pos hzD, F]
    rw [hreg] at h
    exact h
  have hA : 0 ≤ Real.pi * (b ^ 2 - a ^ 2) := by
    exact mul_nonneg Real.pi_pos.le (sub_nonneg.mpr
      ((sq_lt_sq₀ ha.le (ha.trans hab).le).mpr hab).le)
  have hfirst := mul_le_mul_of_nonneg_right (EReal.coe_le_coe_iff.mp hle) hA
  exact hfirst.trans (L08_real_L1_limit_radial_annulus_bound hO hu hf hconv ha hab
    (L08_natRadius_pos (n + N))
    ((Metric.closedBall_subset_closedBall (hN (n + N) (by omega)).2).trans hRO))


theorem L08_circleAverage_mono_add {ψ φ : ℝ → ℝ} (hψ : Continuous ψ) (hφ : Continuous φ)
    (ε : ℝ) (hbound : ∀ θ ∈ Set.Icc 0 (2 * Real.pi), ψ θ ≤ φ θ + ε) :
    Yau.circleAverage ψ ≤ Yau.circleAverage φ + ε := by
  have hpos : 0 < 2 * Real.pi := by positivity
  have h := intervalIntegral.integral_mono_on (μ := volume) hpos.le (hψ.intervalIntegrable _ _)
    ((hφ.add continuous_const).intervalIntegrable _ _) hbound
  have hmul := mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hpos.le)
  have heq : (2 * Real.pi)⁻¹ * (∫ θ in (0 : ℝ)..2 * Real.pi, φ θ + ε) =
      Yau.circleAverage φ + ε := by
    rw [intervalIntegral.integral_add (hφ.intervalIntegrable _ _) (intervalIntegrable_const),
      intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_add,
      ← mul_assoc, inv_mul_cancel₀ hpos.ne', one_mul]
    rfl
  exact hmul.trans_eq heq

theorem L08_continuous_annulus_upper_bound {F : ℂ → ℝ} (hF : Continuous F)
    {z : ℂ} {a b C : ℝ} (ha : 0 < a) (hab : a < b)
    (hcircle : ∀ r ∈ Set.Icc a b,
      Yau.circleAverage (fun θ ↦ F (z + r * Complex.exp (θ * Complex.I))) ≤ C) :
    (∫ w in {w : ℂ | a < ‖w - z‖ ∧ ‖w - z‖ < b}, F w) ≤
      C * (Real.pi * (b ^ 2 - a ^ 2)) := by
  let J : ℝ → ℝ := fun r ↦ ∫ θ in (-Real.pi)..Real.pi, F (z + r • L08_unitCircle θ)
  have hpath : Continuous (fun p : ℝ × ℝ ↦ z + p.1 • L08_unitCircle p.2) :=
    continuous_const.add (continuous_fst.smul (L08_continuous_unitCircle.comp continuous_snd))
  have hJ : Continuous J := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun r θ ↦ F (z + r • L08_unitCircle θ))
    exact hF.comp hpath
  have hpoint (r : ℝ) (hr : r ∈ Set.Icc a b) : J r ≤ C * (2 * Real.pi) := by
    have h := hcircle r hr
    rw [L08_circleAverage_eq_angularIntegral] at h
    change (2 * Real.pi)⁻¹ * J r ≤ C at h
    have hpos : 0 < 2 * Real.pi := by positivity
    have hm := mul_le_mul_of_nonneg_right h hpos.le
    field_simp at hm
    nlinarith
  have hmono := intervalIntegral.integral_mono_on (μ := volume) hab.le
    ((continuous_id.mul hJ).intervalIntegrable a b)
    ((continuous_id.mul continuous_const).intervalIntegrable a b)
    (fun r hr ↦ mul_le_mul_of_nonneg_left (hpoint r hr) (ha.trans_le hr.1).le)
  change (∫ r in a..b, r * J r) ≤ ∫ r in a..b, r * (C * (2 * Real.pi)) at hmono
  have hright : (∫ r in a..b, r * (C * (2 * Real.pi))) =
      C * (Real.pi * (b ^ 2 - a ^ 2)) := by
    rw [intervalIntegral.integral_mul_const, integral_id]
    ring
  rw [hright] at hmono
  rw [← L08_integral_translate_annulus]
  convert hmono using 1
  rw [L08_integral_annulus_polar (h := fun w ↦ F (z + w)) ha hab
    ((hF.comp (continuous_const.add continuous_id)).continuousOn),
    intervalIntegral.integral_of_le hab.le, integral_Ioc_eq_integral_Ioo]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro r _
  dsimp only
  rw [integral_const_mul]
  congr 1
  unfold J
  rw [intervalIntegral.integral_of_le (by linarith [Real.pi_pos]), integral_Ioc_eq_integral_Ioo]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro θ _
  have hq : L08_unitCircle θ = Real.cos θ + Real.sin θ * Complex.I :=
    Complex.exp_ofReal_mul_I θ
  dsimp only
  rw [← hq, ← Complex.real_smul]

/-- Upper semicontinuity on a larger closed disc permits one continuous
majorant whose circle bound persists on a thin annulus. -/
theorem L08_usc_circle_majorant_thin_annulus {v : ℂ → EReal} {z : ℂ} {r R : ℝ}
    (hr : 0 < r) (hrR : r < R)
    (hv : UpperSemicontinuousOn v (Metric.closedBall z R))
    (hfinite : ∀ w ∈ Metric.closedBall z R, v w < ⊤)
    {φ : ℝ → ℝ} (hφ : Continuous φ)
    (hmajor : ∀ θ : ℝ, v (z + r * Complex.exp (θ * Complex.I)) ≤ (φ θ : EReal))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (F : ℂ → ℝ) (a b : ℝ), Continuous F ∧
      (∀ w ∈ Metric.closedBall z R, v w ≤ (F w : EReal)) ∧
      0 < a ∧ a < b ∧ b < R ∧
      ∀ s ∈ Set.Icc a b, ∀ θ ∈ Set.Icc 0 (2 * Real.pi),
        F (z + s • L08_unitCircle θ) ≤ φ θ + ε := by
  let K := Metric.closedBall z R
  have hK : IsCompact K := isCompact_closedBall z R
  have hKn : K.Nonempty := ⟨z, Metric.mem_closedBall_self (hr.trans hrR).le⟩
  obtain ⟨x, hx, hmax⟩ := hv.exists_isMaxOn hKn hK
  obtain ⟨B, hB, _⟩ := EReal.exists_between_coe_real (hfinite x hx)
  let C := max B 0
  have hC0 : 0 ≤ C := le_max_right _ _
  have hC : ∀ w ∈ K, v w ≤ (C : EReal) :=
    fun w hw ↦ (hmax hw).trans (hB.le.trans (EReal.coe_le_coe_iff.mpr (le_max_left _ _)))
  let M : ℕ → ℂ → ℝ := L08_majorantEnvelope K v
  have hLip (n : ℕ) : LipschitzWith (n : NNReal) (M n) :=
    L08_majorantEnvelope_lipschitz hKn hC0 hC n
  have hcircleK (θ : ℝ) : z + r • L08_unitCircle θ ∈ K := by
    apply Metric.closedBall_subset_closedBall hrR.le
    simpa only [Complex.real_smul, L08_unitCircle, circleMap] using circleMap_mem_closedBall z hr.le θ
  let U : ℕ → Set ℝ := fun n ↦ {θ | M n (z + r • L08_unitCircle θ) < φ θ + ε / 2}
  have hUopen (n : ℕ) : IsOpen (U n) :=
    isOpen_lt ((hLip n).continuous.comp
      (continuous_const.add (L08_continuous_unitCircle.const_smul r)))
      (hφ.add continuous_const)
  have hcover : Set.Icc 0 (2 * Real.pi) ⊆ ⋃ n, U n := by
    intro θ _
    have hlim := L08_tendsto_majorantEnvelope hC0 hC hv (hcircleK θ)
    have hmaj : v (z + r • L08_unitCircle θ) ≤ (φ θ : EReal) := by
      simpa only [Complex.real_smul, L08_unitCircle] using hmajor θ
    have hlt : v (z + r • L08_unitCircle θ) < ((φ θ + ε / 2 : ℝ) : EReal) :=
      hmaj.trans_lt (EReal.coe_lt_coe_iff.mpr (by linarith))
    obtain ⟨n, hn⟩ := ((tendsto_order.mp hlim).2 _ hlt).exists
    exact Set.mem_iUnion.mpr ⟨n, EReal.coe_lt_coe_iff.mp hn⟩
  have hdir : Directed (· ⊆ ·) U := by
    intro i j
    refine ⟨max i j, ?_, ?_⟩
    · intro θ hθ
      exact (L08_majorantEnvelope_antitone hKn hC0 hC _ (le_max_left i j)).trans_lt hθ
    · intro θ hθ
      exact (L08_majorantEnvelope_antitone hKn hC0 hC _ (le_max_right i j)).trans_lt hθ
  obtain ⟨N, hN⟩ := isCompact_Icc.elim_directed_cover U hUopen hcover hdir
  have hmin : 0 < min (r / 2) (min ((R - r) / 2) (ε / (2 * ((N : ℝ) + 1)))) := by positivity
  obtain ⟨δ, hδ, hδmin⟩ := exists_between hmin
  have hδr : δ < r / 2 := hδmin.trans_le (min_le_left _ _)
  have hδR : δ < (R - r) / 2 :=
    hδmin.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hδε : δ < ε / (2 * ((N : ℝ) + 1)) :=
    hδmin.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hNδ : (N : ℝ) * δ ≤ ε / 2 := by
    have h := (lt_div_iff₀ (by positivity : 0 < 2 * ((N : ℝ) + 1))).mp hδε
    nlinarith
  refine ⟨M N, r - δ, r + δ, (hLip N).continuous,
    (fun w hw ↦ L08_le_coe_majorantEnvelope hC0 hC N hw), by linarith,
    by linarith, by linarith, ?_⟩
  intro s hs θ hθ
  have hd : dist (z + s • L08_unitCircle θ) (z + r • L08_unitCircle θ) ≤ δ := by
    rw [dist_eq_norm, show z + s • L08_unitCircle θ - (z + r • L08_unitCircle θ) =
      (s - r) • L08_unitCircle θ by module, norm_smul, L08_norm_unitCircle, Real.norm_eq_abs, mul_one]
    exact abs_le.mpr ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hl := (hLip N).le_add_mul (z + s • L08_unitCircle θ) (z + r • L08_unitCircle θ)
  have hnd : (N : ℝ) * dist (z + s • L08_unitCircle θ) (z + r • L08_unitCircle θ) ≤ ε / 2 :=
    (mul_le_mul_of_nonneg_left hd (Nat.cast_nonneg N)).trans hNδ
  have hNθ := hN hθ
  change M N (z + r • L08_unitCircle θ) < φ θ + ε / 2 at hNθ
  have hl' : M N (z + s • L08_unitCircle θ) ≤ M N (z + r • L08_unitCircle θ) +
      (N : ℝ) * dist (z + s • L08_unitCircle θ) (z + r • L08_unitCircle θ) := by
    simpa only [NNReal.coe_natCast] using hl
  linarith


/-- The reconstructed representative satisfies the original continuous
circle-majorant definition of subharmonicity. -/
theorem L08_uscRepresentative_discSubharmonic {O : Set ℂ} (hO : IsOpen O)
    {u : ℕ → ℂ → EReal}
    (hu : ∀ j, LeafCandidates.DiscSubharmonic O (u j) ∧ LeafCandidates.LocallyL1 O (u j))
    (hbound : ∀ S : Set ℂ, IsCompact S → S ⊆ O → ∃ B : ℝ, ∀ j,
      ∫ z in S, |(u j z).toReal| ≤ B)
    {f : ℂ → ℝ} (hf : ∀ S : Set ℂ, IsCompact S → S ⊆ O → IntegrableOn f S volume)
    (hconv : ∀ S : Set ℂ, IsCompact S → S ⊆ O →
      Tendsto (fun j ↦ ∫ w in S, |(u j w).toReal - f w|) atTop (𝓝 0)) :
    LeafCandidates.DiscSubharmonic O (L08_uscRepresentative O f) := by
  have hUSC := L08_upperSemicontinuous_uscRepresentative hO hf
  refine ⟨fun z hz ↦ L08_uscRepresentative_lt_top hO f hz, hUSC.upperSemicontinuousOn O, ?_⟩
  intro z r hr hball φ hφ hmajor
  by_contra hnot
  have hlt : (Yau.circleAverage φ : EReal) < L08_uscRepresentative O f z := lt_of_not_ge hnot
  obtain ⟨q, hcq, hqv⟩ := EReal.exists_between_coe_real hlt
  have hcq' : Yau.circleAverage φ < q := EReal.coe_lt_coe_iff.mp hcq
  let ε := (q - Yau.circleAverage φ) / 2
  have hε : 0 < ε := by dsimp only [ε]; linarith
  obtain ⟨R, hrR, hRO⟩ := L08_exists_larger_closedBall hO hr.le hball
  obtain ⟨F, a, b, hF, hFmajor, ha, hab, hbR, hthin⟩ :=
    L08_usc_circle_majorant_thin_annulus hr hrR
      (hUSC.upperSemicontinuousOn (Metric.closedBall z R))
      (fun w hw ↦ L08_uscRepresentative_lt_top hO f (hRO hw)) hφ hmajor hε
  have hbO : Metric.closedBall z b ⊆ O :=
    (Metric.closedBall_subset_closedBall hbR.le).trans hRO
  have hlower := L08_uscRepresentative_annulus_bound hO hu hbound hf hconv ha hab hbO hqv.le
  let K := Metric.closedBall z R
  let S := {w : ℂ | a < ‖w - z‖ ∧ ‖w - z‖ < b}
  have hK : IsCompact K := isCompact_closedBall z R
  have hS : MeasurableSet S :=
    ((isOpen_lt continuous_const (continuous_id.sub continuous_const).norm).inter
      (isOpen_lt (continuous_id.sub continuous_const).norm continuous_const)).measurableSet
  have hSK : S ⊆ K := fun w hw ↦ by
    change dist w z ≤ R
    rw [dist_eq_norm]
    exact hw.2.le.trans hbR.le
  have heq : ∀ᵐ w ∂volume.restrict S, L08_uscRepresentative O f w = (f w : EReal) :=
    ae_restrict_of_ae_restrict_of_subset hSK
      (L08_uscRepresentative_ae_eq_coe hO hu hbound hf hconv hK hRO)
  have hle : ∀ᵐ w ∂volume.restrict S, f w ≤ F w := by
    filter_upwards [heq, ae_restrict_mem hS] with w hw hwS
    have h := hFmajor w (hSK hwS)
    rw [hw] at h
    exact EReal.coe_le_coe_iff.mp h
  have hcompare : (∫ w in S, f w) ≤ ∫ w in S, F w :=
    integral_mono_ae ((hf K hK hRO).mono_set hSK)
      ((hF.continuousOn.integrableOn_compact hK).mono_set hSK) hle
  have hupper : (∫ w in S, F w) ≤
      (Yau.circleAverage φ + ε) * (Real.pi * (b ^ 2 - a ^ 2)) := by
    apply L08_continuous_annulus_upper_bound hF ha hab
    intro s hs
    apply L08_circleAverage_mono_add (hF.comp (continuous_circleMap z s)) hφ ε
    intro θ hθ
    simpa only [Function.comp_def, circleMap, Complex.real_smul, L08_unitCircle] using hthin s hs θ hθ
  have htotal := hlower.trans (hcompare.trans hupper)
  have hA : 0 < Real.pi * (b ^ 2 - a ^ 2) :=
    mul_pos Real.pi_pos (sub_pos.mpr ((sq_lt_sq₀ ha.le (ha.trans hab).le).mpr hab))
  have hq : q ≤ Yau.circleAverage φ + ε :=
    (mul_le_mul_iff_left₀ hA).mp htotal
  dsimp only [ε] at hq
  linarith

theorem L08_subharmonicL1Compactness : LeafCandidates.SubharmonicL1Compactness := by
  intro O u hO hu hbound
  obtain ⟨σ, f, hσ, hf, hconv⟩ := L08_subharmonic_exists_real_L1_limit hO hu hbound
  have hsub : ∀ j, LeafCandidates.DiscSubharmonic O (u (σ j)) ∧
      LeafCandidates.LocallyL1 O (u (σ j)) := fun j ↦ hu (σ j)
  have hbound' : ∀ S : Set ℂ, IsCompact S → S ⊆ O → ∃ B : ℝ, ∀ j,
      ∫ z in S, |(u (σ j) z).toReal| ≤ B := by
    intro S hS hSO
    obtain ⟨B, hB⟩ := hbound S hS hSO
    exact ⟨B, fun j ↦ hB (σ j)⟩
  exact ⟨σ, L08_uscRepresentative O f, hσ,
    L08_uscRepresentative_discSubharmonic hO hsub hbound' hf hconv,
    L08_uscRepresentative_locallyL1Converges hO hsub hbound' hf hconv⟩

/-- Demailly's local subharmonic compactness, Hartogs bound, smooth Riesz
representation, and finiteness of large atoms, with no additional input. -/
theorem L08 : Yau.LeafObligations.L08 := by
  exact ⟨L08_subharmonicL1Compactness, L08_subharmonicHartogs,
    L08_smoothPlanarRieszDecomposition, L08_locallyFiniteLargeAtoms⟩

end Yau.LeafProofs
