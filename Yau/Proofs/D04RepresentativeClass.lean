import Yau.Proofs.D04Compactness

open MeasureTheory Filter
open scoped Topology ContDiff Convolution

noncomputable section

namespace Yau.Proofs.D04Aux

open Yau Yau.Blueprint

variable {d : ℕ}

/-- Convergence of the same finite-a.e. local real class. -/
def CoordinateLocallyL1Converges (O : Set (ComplexVector d))
    (u : ℕ → ComplexVector d → EReal) (v : ComplexVector d → EReal) : Prop :=
  CoordinateLocallyL1 O v ∧ ∀ K : Set (ComplexVector d), IsCompact K → K ⊆ O →
    Tendsto (fun j => ∫ z in K, |(u j z).toReal - (v z).toReal|) atTop (𝓝 0)

/-! The representative is the infimum of countably many actual local
regularizations. Finite-a.e. equality below retains the same real L¹ limit.
Its plurisubharmonicity is proved in the subsequent representative module. -/

theorem radialConvolution_sub_norm_le {t : ℝ} (ht : 0 < t)
    {g h : (ComplexVector d) → ℝ} (hg : Integrable g volume) (hh : Integrable h volume) {A : ℝ}
    (hA : ∀ w, ‖radialKernel (n := d) t w‖ ≤ A) (z : (ComplexVector d)) :
    |(∫ w, radialKernel (n := d) t (z - w) * g w) -
      (∫ w, radialKernel (n := d) t (z - w) * h w)| ≤ A * ∫ w, |g w - h w| := by
  have heq : (∫ w, radialKernel (n := d) t (z - w) * g w) -
      (∫ w, radialKernel (n := d) t (z - w) * h w) =
      ∫ w, radialKernel (n := d) t (z - w) * (g w - h w) := by
    rw [← integral_sub (integrable_radialConvolution_integrand ht hg z)
      (integrable_radialConvolution_integrand ht hh z)]
    apply integral_congr_ae
    filter_upwards with w
    ring
  rw [heq]
  exact radialConvolution_norm_le ht (hg.sub hh) hA z

/-- Localizing an L¹ limit makes convergence of each fixed-scale smoothing
uniform in the evaluation point. -/
theorem radialConvolution_uniform_of_L1 {t : ℝ} (ht : 0 < t)
    {g : ℕ → (ComplexVector d) → ℝ} (hg : ∀ j, Integrable (g j) volume) {h : (ComplexVector d) → ℝ}
    (hh : Integrable h volume)
    (hconv : Tendsto (fun j ↦ ∫ w, |g j w - h w|) atTop (𝓝 0)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ j in atTop, ∀ z : (ComplexVector d),
      |(∫ w, radialKernel (n := d) t (z - w) * g j w) -
        (∫ w, radialKernel (n := d) t (z - w) * h w)| < ε := by
  obtain ⟨A, hA⟩ := (radialKernel_hasCompactSupport (n := d) ht).exists_bound_of_continuous
    (contDiff_radialKernel (n := d) t).continuous
  have hlim : Tendsto (fun j ↦ max A 0 * ∫ w, |g j w - h w|) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hconv
  intro ε hε
  filter_upwards [(tendsto_order.mp hlim).2 ε hε] with j hj
  intro z
  exact (radialConvolution_sub_norm_le ht (hg j) hh
    (fun w ↦ (hA w).trans (le_max_left A 0)) z).trans_lt hj

def radialDomain (O : Set (ComplexVector d)) (t : ℝ) : Set (ComplexVector d) :=
  {z | Metric.closedBall z (2 * t) ⊆ O}

theorem isOpen_radialDomain {O : Set (ComplexVector d)} (hO : IsOpen O) (t : ℝ) :
    IsOpen (radialDomain O t) := by
  apply isOpen_iff_mem_nhds.mpr
  intro z hz
  have hcont : Continuous (fun p : (ComplexVector d) × (ComplexVector d) ↦ p.1 + p.2) := continuous_fst.add continuous_snd
  have hnear := (isCompact_closedBall (0 : (ComplexVector d)) (2 * t)).eventually_forall_of_forall_eventually
    (P := fun x w : (ComplexVector d) ↦ x + w ∈ O) (x₀ := z) (fun w hw ↦
      (hcont.tendsto (z, w)).eventually (hO.mem_nhds (hz (by
        simpa only [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, sub_zero] using hw))))
  filter_upwards [hnear] with x hx
  intro w hw
  have hsub : w - x ∈ Metric.closedBall (0 : (ComplexVector d)) (2 * t) := by
    simpa only [Metric.mem_closedBall, dist_eq_norm, sub_zero] using hw
  simpa only [add_sub_cancel] using hx (w - x) hsub

/-- The full local convolution is smooth wherever its compact kernel
neighborhood is contained in the open domain. -/
theorem contDiffAt_radialConvolution_local {O : Set (ComplexVector d)} (hO : IsOpen O)
    {f : (ComplexVector d) → ℝ} (hf : ∀ S : Set (ComplexVector d), IsCompact S → S ⊆ O → IntegrableOn f S volume)
    {t : ℝ} (ht : 0 < t) {z : (ComplexVector d)} (hz : z ∈ radialDomain O t) :
    ContDiffAt ℝ ∞ (fun x : (ComplexVector d) ↦ ∫ w, radialKernel (n := d) t (x - w) * f w) z := by
  obtain ⟨δ, hδ, hδD⟩ := Metric.isOpen_iff.mp (isOpen_radialDomain hO t) z hz
  let S : Set (ComplexVector d) := (fun p : (ComplexVector d) × (ComplexVector d) ↦ p.1 + p.2) ''
    (Metric.closedBall z (δ / 2) ×ˢ Metric.closedBall 0 (2 * t))
  have hS : IsCompact S := ((isCompact_closedBall z (δ / 2)).prod
    (isCompact_closedBall (0 : (ComplexVector d)) (2 * t))).image (continuous_fst.add continuous_snd)
  have hSO : S ⊆ O := by
    rintro w ⟨⟨x, y⟩, hxy, rfl⟩
    have hxD := hδD ((Metric.closedBall_subset_ball (half_lt_self hδ)) hxy.1)
    apply hxD
    simpa only [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, sub_zero] using hxy.2
  have hgi : Integrable (S.indicator f) volume :=
    (integrable_indicator_iff hS.measurableSet).mpr (hf S hS hSO)
  apply (contDiff_radialConvolution ht hgi).contDiffAt.congr_of_eventuallyEq
  filter_upwards [Metric.ball_mem_nhds z (half_pos hδ)] with x hx
  symm
  apply radialConvolution_indicator_eq ht f
  intro w hw
  refine ⟨(x, w - x), ⟨Metric.ball_subset_closedBall hx, ?_⟩, by simp⟩
  simpa only [Metric.mem_closedBall, dist_eq_norm, sub_zero] using hw

def radialRegularization (O : Set (ComplexVector d)) (f : (ComplexVector d) → ℝ) (t : ℝ) (z : (ComplexVector d)) : EReal :=
  by
    classical
    exact if z ∈ radialDomain O t then
      ((∫ w, radialKernel (n := d) t (z - w) * f w : ℝ) : EReal) else ⊤

theorem upperSemicontinuous_radialRegularization {O : Set (ComplexVector d)} (hO : IsOpen O)
    {f : (ComplexVector d) → ℝ} (hf : ∀ S : Set (ComplexVector d), IsCompact S → S ⊆ O → IntegrableOn f S volume)
    {t : ℝ} (ht : 0 < t) : UpperSemicontinuous (radialRegularization O f t) := by
  intro z
  by_cases hz : z ∈ radialDomain O t
  · have hlocal : ContinuousAt (fun x : (ComplexVector d) ↦
        ((∫ w, radialKernel (n := d) t (x - w) * f w : ℝ) : EReal)) z :=
      continuous_coe_real_ereal.continuousAt.comp (contDiffAt_radialConvolution_local hO hf ht hz).continuousAt
    have heq : radialRegularization O f t =ᶠ[𝓝 z]
        (fun x : (ComplexVector d) ↦ ((∫ w, radialKernel (n := d) t (x - w) * f w : ℝ) : EReal)) := by
      filter_upwards [(isOpen_radialDomain hO t).mem_nhds hz] with x hx
      simp only [radialRegularization, ite_eq_left hx]
    exact (hlocal.congr_of_eventuallyEq heq).upperSemicontinuousAt
  · intro a ha
    have htop : radialRegularization O f t z = ⊤ := by
      simp only [radialRegularization, ite_eq_right hz]
    rw [htop] at ha
    exact (not_top_lt ha).elim

def natRadius (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

def uscRepresentative (O : Set (ComplexVector d)) (f : (ComplexVector d) → ℝ) (z : (ComplexVector d)) : EReal :=
  ⨅ n : ℕ, radialRegularization O f (natRadius n) z

theorem upperSemicontinuous_uscRepresentative {O : Set (ComplexVector d)} (hO : IsOpen O)
    {f : (ComplexVector d) → ℝ} (hf : ∀ S : Set (ComplexVector d), IsCompact S → S ⊆ O → IntegrableOn f S volume) :
    UpperSemicontinuous (uscRepresentative O f) :=
  upperSemicontinuous_iInf fun n ↦ upperSemicontinuous_radialRegularization hO hf (by
    dsimp only [natRadius]
    positivity)

theorem uscRepresentative_lt_top {O : Set (ComplexVector d)} (hO : IsOpen O)
    (f : (ComplexVector d) → ℝ) {z : (ComplexVector d)} (hz : z ∈ O) : uscRepresentative O f z < ⊤ := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hO z hz
  have htends : Tendsto (fun n : ℕ ↦ 2 * natRadius n) atTop (𝓝 0) := by
    simpa only [natRadius, mul_zero] using tendsto_const_nhds.mul (Yau.LeafProofs.L08_tendsto_natScale 1)
  obtain ⟨n, hn⟩ := ((tendsto_order.mp htends).2 r hr).exists
  have hD : z ∈ radialDomain O (natRadius n) :=
    (Metric.closedBall_subset_ball hn).trans hball
  have hle := iInf_le (fun n ↦ radialRegularization O f (natRadius n) z) n
  rw [radialRegularization, ite_eq_left hD] at hle
  exact hle.trans_lt (EReal.coe_lt_top _)

theorem integral_abs_indicator_sub (f g : (ComplexVector d) → ℝ) {S : Set (ComplexVector d)} (hS : MeasurableSet S) :
    (∫ w, |S.indicator f w - S.indicator g w|) = ∫ w in S, |f w - g w| := by
  have heq (w : (ComplexVector d)) : S.indicator f w - S.indicator g w = S.indicator (fun w ↦ f w - g w) w := by
    by_cases hw : w ∈ S
    · simp only [Set.indicator_of_mem hw]
    · simp only [Set.indicator_of_notMem hw, sub_self]
  simp_rw [heq]
  exact integral_abs_indicator _ hS

theorem radialConvolution_uniform_on_compact_of_localL1 {O : Set (ComplexVector d)}
    {u : ℕ → (ComplexVector d) → EReal} (hL1 : ∀ j, CoordinateLocallyL1 O (u j)) {f : (ComplexVector d) → ℝ}
    (hf : ∀ S : Set (ComplexVector d), IsCompact S → S ⊆ O → IntegrableOn f S volume)
    (hconv : ∀ S : Set (ComplexVector d), IsCompact S → S ⊆ O →
      Tendsto (fun j ↦ ∫ w in S, |(u j w).toReal - f w|) atTop (𝓝 0))
    {t : ℝ} (ht : 0 < t) {K : Set (ComplexVector d)} (hK : IsCompact K) (hKD : K ⊆ radialDomain O t) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ j in atTop, ∀ z ∈ K,
      |(∫ w, radialKernel (n := d) t (z - w) * (u j w).toReal) -
        (∫ w, radialKernel (n := d) t (z - w) * f w)| < ε := by
  let S : Set (ComplexVector d) := (fun p : (ComplexVector d) × (ComplexVector d) ↦ p.1 + p.2) '' (K ×ˢ Metric.closedBall 0 (2 * t))
  have hS : IsCompact S := (hK.prod (isCompact_closedBall (0 : (ComplexVector d)) (2 * t))).image
    (continuous_fst.add continuous_snd)
  have hSO : S ⊆ O := by
    rintro w ⟨⟨x, y⟩, hxy, rfl⟩
    apply hKD hxy.1
    simpa only [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, sub_zero] using hxy.2
  have hballs {z : (ComplexVector d)} (hz : z ∈ K) : Metric.closedBall z (2 * t) ⊆ S := by
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
    exact Filter.Eventually.of_forall fun j ↦ (integral_abs_indicator_sub _ _ hS.measurableSet).symm
  intro ε hε
  filter_upwards [radialConvolution_uniform_of_L1 ht hgi hfi hIconv ε hε] with j hj
  intro z hz
  rw [← radialConvolution_indicator_eq ht (fun w ↦ (u j w).toReal) (hballs hz),
    ← radialConvolution_indicator_eq ht f (hballs hz)]
  exact hj z

/-- Every fixed admissible smoothing majorizes the local L¹ limit a.e.;
this inequality is inherited from the original subharmonic sequence. -/
theorem real_L1_limit_le_radialConvolution_ae {O : Set (ComplexVector d)} {u : ℕ → (ComplexVector d) → EReal}
    (hu : ∀ j, IsPshOn (u j) O ∧ CoordinateLocallyL1 O (u j))
    {f : (ComplexVector d) → ℝ} (hf : ∀ S : Set (ComplexVector d), IsCompact S → S ⊆ O → IntegrableOn f S volume)
    (hconv : ∀ S : Set (ComplexVector d), IsCompact S → S ⊆ O →
      Tendsto (fun j ↦ ∫ w in S, |(u j w).toReal - f w|) atTop (𝓝 0))
    {t : ℝ} (ht : 0 < t) {K : Set (ComplexVector d)} (hK : IsCompact K) (hKD : K ⊆ radialDomain O t) :
    ∀ᵐ z ∂volume.restrict K, f z ≤ ∫ w, radialKernel (n := d) t (z - w) * f w := by
  have hKO : K ⊆ O := fun z hz ↦ hKD hz (Metric.mem_closedBall_self (by positivity : 0 ≤ 2 * t))
  obtain ⟨τ, hτ, hτae⟩ := Yau.LeafProofs.L08_exists_ae_subseq_of_L1
    (fun j ↦ ((hu j).2 K hK hKO).2) (hf K hK hKO) (hconv K hK hKO)
  have hineq (j : ℕ) : ∀ᵐ z ∂volume.restrict K,
      (u j z).toReal ≤ ∫ w, radialKernel (n := d) t (z - w) * (u j w).toReal := by
    filter_upwards [((hu j).2 K hK hKO).1, ae_restrict_mem hK.measurableSet] with z hz hzK
    apply EReal.coe_le_coe_iff.mp
    rw [EReal.coe_toReal hz.2 hz.1]
    exact psh_le_radialConvolution (hu j).1 (hu j).2 ht (hKD hzK)
  have hall : ∀ᵐ z ∂volume.restrict K, ∀ j, (u j z).toReal ≤
      ∫ w, radialKernel (n := d) t (z - w) * (u j w).toReal := ae_all_iff.mpr hineq
  have huni := radialConvolution_uniform_on_compact_of_localL1 (fun j ↦ (hu j).2) hf hconv ht hK hKD
  filter_upwards [hτae, hall, ae_restrict_mem hK.measurableSet] with z hz hineqz hzK
  have hpt : Tendsto (fun j ↦ ∫ w, radialKernel (n := d) t (z - w) * (u j w).toReal) atTop
      (𝓝 (∫ w, radialKernel (n := d) t (z - w) * f w)) := by
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    obtain ⟨N, hN⟩ := eventually_atTop.mp (huni ε hε)
    exact ⟨N, fun j hj ↦ by simpa only [Real.dist_eq] using hN j hj z hzK⟩
  exact le_of_tendsto_of_tendsto hz (hpt.comp hτ.tendsto_atTop)
    (Filter.Eventually.of_forall fun j ↦ hineqz (τ j))

theorem real_L1_limit_le_uscRepresentative_ae {O : Set (ComplexVector d)} (hO : IsOpen O)
    {u : ℕ → (ComplexVector d) → EReal}
    (hu : ∀ j, IsPshOn (u j) O ∧ CoordinateLocallyL1 O (u j))
    {f : (ComplexVector d) → ℝ} (hf : ∀ S : Set (ComplexVector d), IsCompact S → S ⊆ O → IntegrableOn f S volume)
    (hconv : ∀ S : Set (ComplexVector d), IsCompact S → S ⊆ O →
      Tendsto (fun j ↦ ∫ w in S, |(u j w).toReal - f w|) atTop (𝓝 0)) :
    ∀ᵐ z ∂volume, (f z : EReal) ≤ uscRepresentative O f z := by
  have hdom (t : ℝ) (ht : 0 < t) : ∀ᵐ z ∂volume, z ∈ radialDomain O t →
      f z ≤ ∫ w, radialKernel (n := d) t (z - w) * f w := by
    obtain ⟨K, hK, hKD, _, hcover⟩ := exists_compact_exhaustion (isOpen_radialDomain hO t)
    have hall : ∀ᵐ z ∂volume, ∀ m : ℕ, z ∈ K m →
        f z ≤ ∫ w, radialKernel (n := d) t (z - w) * f w := by
      apply ae_all_iff.mpr
      intro m
      exact (ae_restrict_iff' (hK m).measurableSet).mp
        (real_L1_limit_le_radialConvolution_ae hu hf hconv ht (hK m) (hKD m))
    filter_upwards [hall] with z hz
    intro hzD
    obtain ⟨m, hm⟩ := hcover {z} isCompact_singleton (Set.singleton_subset_iff.mpr hzD)
    exact hz m (hm (Set.mem_singleton z))
  have hall : ∀ᵐ z ∂volume, ∀ n : ℕ, z ∈ radialDomain O (natRadius n) →
      f z ≤ ∫ w, radialKernel (natRadius n) (z - w) * f w :=
    ae_all_iff.mpr fun n ↦ hdom _ (by dsimp only [natRadius]; positivity)
  filter_upwards [hall] with z hz
  apply le_iInf
  intro n
  by_cases hzD : z ∈ radialDomain O (natRadius n)
  · simp only [radialRegularization, ite_eq_left hzD]
    exact EReal.coe_le_coe_iff.mpr (hz n hzD)
  · simp only [radialRegularization, ite_eq_right hzD]
    exact le_top

theorem L1_of_uniform_on_compact {K : Set (ComplexVector d)} (hK : IsCompact K)
    {f : ℕ → (ComplexVector d) → ℝ} {g : (ComplexVector d) → ℝ}
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
    have hbound := integral_abs_le_const hK (fun z hz ↦ (hj z hz).le)
    have hsmall : δ * volume.real K < b := by nlinarith
    exact hbound.trans_lt hsmall

theorem uniform_radial_L1_approx_with_neighborhoods {O : Set (ComplexVector d)} {u : ℕ → (ComplexVector d) → EReal}
    (hO : IsOpen O) (hu : ∀ j, IsPshOn (u j) O ∧
      CoordinateLocallyL1 O (u j))
    (hbound : ∀ S : Set (ComplexVector d), IsCompact S → S ⊆ O → ∃ B : ℝ, ∀ j,
      ∫ z in S, |(u j z).toReal| ≤ B)
    {K : Set (ComplexVector d)} (hK : IsCompact K) (hKO : K ⊆ O) :
    ∃ (S : Set (ComplexVector d)) (T M : ℝ), IsCompact S ∧ S ⊆ O ∧ K ⊆ S ∧ 0 < T ∧ 0 ≤ M ∧
      (∀ j, Integrable (S.indicator (fun w ↦ (u j w).toReal)) volume) ∧
      (∀ t, 0 < t → t ≤ T → ∀ z ∈ K, Metric.closedBall z (2 * t) ⊆ S) ∧
      ∀ j t, 0 < t → t ≤ T →
        (∫ z in K, |(∫ w, radialKernel (n := d) t (z - w) *
          S.indicator (fun w ↦ (u j w).toReal) w) - (u j z).toReal|) ≤ M * t := by
  obtain ⟨η, hη, hηO⟩ := hK.exists_cthickening_subset_open hO hKO
  let K' := Metric.cthickening η K
  have hK' : IsCompact K' := hK.cthickening
  have hKK' : K ⊆ K' := Metric.self_subset_cthickening K
  obtain ⟨S, T, M, hS, hSO, hK'S, hT, hM, hgi, herr⟩ :=
    uniform_radial_L1_approx hO hu hbound hK' hηO
  refine ⟨S, min T (η / 2), M, hS, hSO, hKK'.trans hK'S,
    lt_min hT (half_pos hη), hM, hgi, ?_, ?_⟩
  · intro t ht htT z hz
    exact (Metric.closedBall_subset_closedBall (show 2 * t ≤ η by linarith [htT.trans (min_le_right T (η / 2))])).trans
      ((Metric.closedBall_subset_cthickening hz η).trans hK'S)
  · intro j t ht htT
    have hdiff : IntegrableOn (fun z ↦ |(∫ w, radialKernel (n := d) t (z - w) *
        S.indicator (fun w ↦ (u j w).toReal) w) - (u j z).toReal|) K' volume :=
      (((integrable_radialConvolution ht (hgi j)).mono_measure Measure.restrict_le_self).sub
        ((hu j).2 K' hK' hηO).2).norm
    exact (setIntegral_mono_set hdiff (Filter.Eventually.of_forall fun _ ↦ abs_nonneg _)
      (Filter.Eventually.of_forall hKK')).trans (herr j t ht (htT.trans (min_le_left T (η / 2))))

/-- The uniform smoothing estimate passes to the real local L¹ limit. -/
theorem real_L1_limit_radial_approx {O : Set (ComplexVector d)} (hO : IsOpen O)
    {u : ℕ → (ComplexVector d) → EReal}
    (hu : ∀ j, IsPshOn (u j) O ∧ CoordinateLocallyL1 O (u j))
    (hbound : ∀ S : Set (ComplexVector d), IsCompact S → S ⊆ O → ∃ B : ℝ, ∀ j,
      ∫ z in S, |(u j z).toReal| ≤ B)
    {f : (ComplexVector d) → ℝ} (hf : ∀ S : Set (ComplexVector d), IsCompact S → S ⊆ O → IntegrableOn f S volume)
    (hconv : ∀ S : Set (ComplexVector d), IsCompact S → S ⊆ O →
      Tendsto (fun j ↦ ∫ w in S, |(u j w).toReal - f w|) atTop (𝓝 0))
    {K : Set (ComplexVector d)} (hK : IsCompact K) (hKO : K ⊆ O) :
    ∃ T M : ℝ, 0 < T ∧ 0 ≤ M ∧ ∀ t, 0 < t → t ≤ T →
      K ⊆ radialDomain O t ∧
      (∫ z in K, |(∫ w, radialKernel (n := d) t (z - w) * f w) - f z|) ≤ M * t := by
  obtain ⟨S, T, M, hS, hSO, _, hT, hM, hgi, hballs, herr⟩ :=
    uniform_radial_L1_approx_with_neighborhoods hO hu hbound hK hKO
  refine ⟨T, M, hT, hM, ?_⟩
  intro t ht htT
  have hKD : K ⊆ radialDomain O t := fun z hz ↦ (hballs t ht htT z hz).trans hSO
  refine ⟨hKD, ?_⟩
  let g : ℕ → (ComplexVector d) → ℝ := fun j ↦ S.indicator (fun w ↦ (u j w).toReal)
  let h : (ComplexVector d) → ℝ := S.indicator f
  let p : ℕ → (ComplexVector d) → ℝ := fun j z ↦ ∫ w, radialKernel (n := d) t (z - w) * g j w
  let q : (ComplexVector d) → ℝ := fun z ↦ ∫ w, radialKernel (n := d) t (z - w) * h w
  have hhi : Integrable h volume := (integrable_indicator_iff hS.measurableSet).mpr (hf S hS hSO)
  have hIconv : Tendsto (fun j ↦ ∫ w, |g j w - h w|) atTop (𝓝 0) := by
    apply (hconv S hS hSO).congr'
    exact Filter.Eventually.of_forall fun j ↦ (integral_abs_indicator_sub _ _ hS.measurableSet).symm
  have hpconv : Tendsto (fun j ↦ ∫ z in K, |p j z - q z|) atTop (𝓝 0) :=
    L1_of_uniform_on_compact hK (fun ε hε ↦
      (radialConvolution_uniform_of_L1 ht hgi hhi hIconv ε hε).mono fun j hj z _ ↦ hj z)
  have hrawi (j : ℕ) : Integrable (fun z ↦ (u j z).toReal) (volume.restrict K) :=
    ((hu j).2 K hK hKO).2
  have hfi : Integrable f (volume.restrict K) := hf K hK hKO
  have hpi (j : ℕ) : Integrable (p j) (volume.restrict K) :=
    (integrable_radialConvolution ht (hgi j)).mono_measure Measure.restrict_le_self
  have hqi : Integrable q (volume.restrict K) :=
    (integrable_radialConvolution ht hhi).mono_measure Measure.restrict_le_self
  have hdist := (Yau.LeafProofs.L08_tendsto_toL1_of_integral hrawi hfi (hconv K hK hKO)).dist
    (Yau.LeafProofs.L08_tendsto_toL1_of_integral hpi hqi hpconv)
  have herrconv : Tendsto (fun j ↦ ∫ z in K, |p j z - (u j z).toReal|) atTop
      (𝓝 (∫ z in K, |q z - f z|)) := by
    simpa only [Yau.LeafProofs.L08_dist_toL1_eq_integral_abs, abs_sub_comm] using hdist
  have hlim : (∫ z in K, |q z - f z|) ≤ M * t :=
    le_of_tendsto herrconv (Filter.Eventually.of_forall fun j ↦ herr j t ht htT)
  have heq : (∫ z in K, |q z - f z|) =
      ∫ z in K, |(∫ w, radialKernel (n := d) t (z - w) * f w) - f z| := by
    apply setIntegral_congr_fun hK.measurableSet
    intro z hz
    change |(∫ w, radialKernel (n := d) t (z - w) * S.indicator f w) - f z| = _
    rw [radialConvolution_indicator_eq ht f (hballs t ht htT z hz)]
  rwa [heq] at hlim


theorem natRadius_pos (n : ℕ) : 0 < natRadius n := by
  dsimp only [natRadius]
  positivity

theorem tendsto_natRadius : Tendsto natRadius atTop (𝓝 0) :=
  Yau.LeafProofs.L08_tendsto_natScale 1

theorem real_L1_limit_radial_tendsto {O : Set (ComplexVector d)} (hO : IsOpen O)
    {u : ℕ → (ComplexVector d) → EReal}
    (hu : ∀ j, IsPshOn (u j) O ∧ CoordinateLocallyL1 O (u j))
    (hbound : ∀ S : Set (ComplexVector d), IsCompact S → S ⊆ O → ∃ B : ℝ, ∀ j,
      ∫ z in S, |(u j z).toReal| ≤ B)
    {f : (ComplexVector d) → ℝ} (hf : ∀ S : Set (ComplexVector d), IsCompact S → S ⊆ O → IntegrableOn f S volume)
    (hconv : ∀ S : Set (ComplexVector d), IsCompact S → S ⊆ O →
      Tendsto (fun j ↦ ∫ w in S, |(u j w).toReal - f w|) atTop (𝓝 0))
    {K : Set (ComplexVector d)} (hK : IsCompact K) (hKO : K ⊆ O) :
    (∀ᶠ n in atTop, K ⊆ radialDomain O (natRadius n)) ∧
    Tendsto (fun n ↦ ∫ z in K,
      |(∫ w, radialKernel (natRadius n) (z - w) * f w) - f z|) atTop (𝓝 0) := by
  obtain ⟨T, M, hT, hM, happ⟩ := real_L1_limit_radial_approx hO hu hbound hf hconv hK hKO
  have he : ∀ᶠ n in atTop, natRadius n ≤ T :=
    ((tendsto_order.mp tendsto_natRadius).2 T hT).mono fun _ h ↦ h.le
  refine ⟨he.mono fun n hn ↦ (happ _ (natRadius_pos n) hn).1, ?_⟩
  apply squeeze_zero' (Filter.Eventually.of_forall fun n ↦ integral_nonneg fun z ↦ abs_nonneg _)
    (he.mono fun n hn ↦ (happ _ (natRadius_pos n) hn).2)
  simpa only [mul_zero] using tendsto_const_nhds.mul tendsto_natRadius

theorem uscRepresentative_ae_eq_coe {O : Set (ComplexVector d)} (hO : IsOpen O)
    {u : ℕ → (ComplexVector d) → EReal}
    (hu : ∀ j, IsPshOn (u j) O ∧ CoordinateLocallyL1 O (u j))
    (hbound : ∀ S : Set (ComplexVector d), IsCompact S → S ⊆ O → ∃ B : ℝ, ∀ j,
      ∫ z in S, |(u j z).toReal| ≤ B)
    {f : (ComplexVector d) → ℝ} (hf : ∀ S : Set (ComplexVector d), IsCompact S → S ⊆ O → IntegrableOn f S volume)
    (hconv : ∀ S : Set (ComplexVector d), IsCompact S → S ⊆ O →
      Tendsto (fun j ↦ ∫ w in S, |(u j w).toReal - f w|) atTop (𝓝 0))
    {K : Set (ComplexVector d)} (hK : IsCompact K) (hKO : K ⊆ O) :
    ∀ᵐ z ∂volume.restrict K, uscRepresentative O f z = (f z : EReal) := by
  obtain ⟨hD, hlim⟩ := real_L1_limit_radial_tendsto hO hu hbound hf hconv hK hKO
  obtain ⟨N, hN⟩ := eventually_atTop.mp hD
  let F : ℕ → (ComplexVector d) → ℝ := fun n z ↦ ∫ w,
    radialKernel (natRadius (n + N)) (z - w) * f w
  have hFi (n : ℕ) : IntegrableOn (F n) K volume := by
    apply ContinuousOn.integrableOn_compact hK
    intro z hz
    exact (contDiffAt_radialConvolution_local hO hf (natRadius_pos (n + N))
      (hN (n + N) (by omega) hz)).continuousAt.continuousWithinAt
  have hFlim : Tendsto (fun n ↦ ∫ z in K, |F n z - f z|) atTop (𝓝 0) :=
    hlim.comp (tendsto_add_atTop_nat N)
  obtain ⟨τ, hτ, hτae⟩ := Yau.LeafProofs.L08_exists_ae_subseq_of_L1 hFi (hf K hK hKO) hFlim
  have hle : ∀ᵐ z ∂volume.restrict K, (f z : EReal) ≤ uscRepresentative O f z :=
    ae_restrict_of_ae (real_L1_limit_le_uscRepresentative_ae hO hu hf hconv)
  filter_upwards [hτae, hle, ae_restrict_mem hK.measurableSet] with z hz hlez hzK
  apply le_antisymm _ hlez
  have hcoe : Tendsto (fun j ↦ (F (τ j) z : EReal)) atTop (𝓝 (f z : EReal)) :=
    continuous_coe_real_ereal.continuousAt.tendsto.comp hz
  apply ge_of_tendsto hcoe
  apply Filter.Eventually.of_forall
  intro j
  have hbound := iInf_le (fun n ↦ radialRegularization O f (natRadius n) z) (τ j + N)
  have hreg : radialRegularization O f (natRadius (τ j + N)) z =
      (F (τ j) z : EReal) := by
    simp only [radialRegularization, ite_eq_left (hN (τ j + N) (by omega) hzK), F]
  rw [hreg] at hbound
  exact hbound

theorem uscRepresentative_locallyL1 {O : Set (ComplexVector d)} (hO : IsOpen O)
    {u : ℕ → (ComplexVector d) → EReal}
    (hu : ∀ j, IsPshOn (u j) O ∧ CoordinateLocallyL1 O (u j))
    (hbound : ∀ S : Set (ComplexVector d), IsCompact S → S ⊆ O → ∃ B : ℝ, ∀ j,
      ∫ z in S, |(u j z).toReal| ≤ B)
    {f : (ComplexVector d) → ℝ} (hf : ∀ S : Set (ComplexVector d), IsCompact S → S ⊆ O → IntegrableOn f S volume)
    (hconv : ∀ S : Set (ComplexVector d), IsCompact S → S ⊆ O →
      Tendsto (fun j ↦ ∫ w in S, |(u j w).toReal - f w|) atTop (𝓝 0)) :
    CoordinateLocallyL1 O (uscRepresentative O f) := by
  intro K hK hKO
  have heq := uscRepresentative_ae_eq_coe hO hu hbound hf hconv hK hKO
  constructor
  · filter_upwards [heq] with z hz
    rw [hz]
    exact ⟨EReal.coe_ne_bot _, EReal.coe_ne_top _⟩
  · apply (hf K hK hKO).congr
    filter_upwards [heq] with z hz
    simp only [hz, EReal.toReal_coe]

theorem uscRepresentative_locallyL1Converges {O : Set (ComplexVector d)} (hO : IsOpen O)
    {u : ℕ → (ComplexVector d) → EReal}
    (hu : ∀ j, IsPshOn (u j) O ∧ CoordinateLocallyL1 O (u j))
    (hbound : ∀ S : Set (ComplexVector d), IsCompact S → S ⊆ O → ∃ B : ℝ, ∀ j,
      ∫ z in S, |(u j z).toReal| ≤ B)
    {f : (ComplexVector d) → ℝ} (hf : ∀ S : Set (ComplexVector d), IsCompact S → S ⊆ O → IntegrableOn f S volume)
    (hconv : ∀ S : Set (ComplexVector d), IsCompact S → S ⊆ O →
      Tendsto (fun j ↦ ∫ w in S, |(u j w).toReal - f w|) atTop (𝓝 0)) :
    CoordinateLocallyL1Converges O u (uscRepresentative O f) := by
  refine ⟨uscRepresentative_locallyL1 hO hu hbound hf hconv, ?_⟩
  intro K hK hKO
  have heq := uscRepresentative_ae_eq_coe hO hu hbound hf hconv hK hKO
  apply (hconv K hK hKO).congr'
  apply Filter.Eventually.of_forall
  intro j
  apply integral_congr_ae
  filter_upwards [heq] with z hz
  simp only [hz, EReal.toReal_coe]


end Yau.Proofs.D04Aux
