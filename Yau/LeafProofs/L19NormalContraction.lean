import Yau.LeafProofs.L19ScalarEnergyCompletion
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! Normal contractions of the actual completed scalar energy. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff InnerProductSpace

namespace Yau.LeafProofs.L19Aux
set_option backward.isDefEq.respectTransparency false

/-- Bounded Hilbert approximants with a strong image limit retain the sharp
limiting norm bound. The weak limit is obtained from the actual Riesz dual,
using Banach--Alaoglu; no closed-form or Markov assumption is used. -/
theorem hilbert_strong_image_limit
    {H Z : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
    (J : H →L[ℝ] Z) (w : ℕ → H) (z : Z) (a : ℕ → ℝ) (A B : ℝ)
    (hbound : ∀ᶠ j in atTop, ‖w j‖ ≤ B)
    (hstrong : Tendsto (fun j => J (w j)) atTop (𝓝 z))
    (hupper : ∀ᶠ j in atTop, ‖w j‖ ^ 2 ≤ a j)
    (ha : Tendsto a atTop (𝓝 A)) :
    ∃ v : H, J v = z ∧ ‖v‖ ^ 2 ≤ A := by
  let d : ℕ → WeakDual ℝ H := fun j =>
    StrongDual.toWeakDual (InnerProductSpace.toDual ℝ H (w j))
  have hmem : ∀ᶠ j in atTop,
      d j ∈ WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual ℝ H) B := by
    filter_upwards [hbound] with j hj
    simpa [d, Metric.mem_closedBall, dist_zero_right] using hj
  obtain ⟨φ, _, hφ⟩ := IsCompact.exists_mapClusterPt_of_frequently
    (WeakDual.isCompact_closedBall (0 : StrongDual ℝ H) B) hmem.frequently
  let F : Filter ℕ := atTop ⊓ comap d (𝓝 φ)
  have : NeBot F := by
    apply neBot_inf_comap_iff_map.mpr
    simpa [inf_comm] using hφ.neBot
  have hd : Tendsto d F (𝓝 φ) := tendsto_comap.mono_left inf_le_right
  let v : H := (InnerProductSpace.toDual ℝ H).symm (WeakDual.toStrongDual φ)
  have hv (x : H) : Tendsto (fun j => ⟪w j, x⟫_ℝ) F (𝓝 ⟪v, x⟫_ℝ) := by
    have ht := (WeakDual.eval_continuous x).tendsto φ |>.comp hd
    change Tendsto (fun j => ⟪w j, x⟫_ℝ) F (𝓝 (φ x)) at ht
    simpa [v, InnerProductSpace.toDual_symm_apply] using ht
  refine ⟨v, ?_, ?_⟩
  · apply ext_inner_right ℝ
    intro y
    have hleft := hv (J.adjoint y)
    simp only [ContinuousLinearMap.adjoint_inner_right] at hleft
    have hright := ((hstrong.mono_left inf_le_left).inner tendsto_const_nhds :
      Tendsto (fun j => ⟪J (w j), y⟫_ℝ) F (𝓝 ⟪z, y⟫_ℝ))
    exact tendsto_nhds_unique hleft hright
  · have hineq : ∀ᶠ j in F, 2 * ⟪w j, v⟫_ℝ ≤ a j + ‖v‖ ^ 2 := by
      filter_upwards [hupper.filter_mono inf_le_left] with j hj
      have hh := norm_sub_sq_real (w j) v
      nlinarith [sq_nonneg ‖w j - v‖]
    have ht := le_of_tendsto_of_tendsto
      ((hv v).const_mul 2) ((ha.mono_left inf_le_left).add tendsto_const_nhds) hineq
    rw [real_inner_self_eq_norm_sq] at ht
    linarith

/-- The genuine projection to the normal interval. -/
def normalClip (K r : ℝ) : ℝ := max 0 (min K r)

theorem normalClip_zero {K : ℝ} (hK : 0 ≤ K) : normalClip K 0 = 0 := by
  simp [normalClip, min_eq_right hK]

theorem normalClip_lipschitz (K : ℝ) : LipschitzWith 1 (normalClip K) :=
  (LipschitzWith.id.const_min K).const_max 0

/-- A smooth absolute value with a strictly positive regularizing parameter. -/
def regularAbs (ε r : ℝ) : ℝ := Real.sqrt (r ^ 2 + ε ^ 2)

theorem regularAbs_pos {ε : ℝ} (hε : 0 < ε) (r : ℝ) : 0 < regularAbs ε r := by
  apply Real.sqrt_pos.2
  nlinarith [sq_nonneg r]

theorem regularAbs_contDiff {ε : ℝ} (hε : 0 < ε) : ContDiff ℝ ∞ (regularAbs ε) := by
  apply (contDiff_id.pow 2 |>.add contDiff_const).sqrt
  intro r
  nlinarith [sq_nonneg r]

theorem regularAbs_hasDerivAt {ε : ℝ} (hε : 0 < ε) (r : ℝ) :
    HasDerivAt (regularAbs ε) (r / regularAbs ε r) r := by
  have hp : r ^ 2 + ε ^ 2 ≠ 0 := by nlinarith [sq_nonneg r]
  convert (((hasDerivAt_id r).pow 2).add_const (ε ^ 2)).sqrt hp using 1
  · rfl
  · dsimp [regularAbs]
    ring

theorem regularAbs_ratio_abs_le {ε : ℝ} (hε : 0 < ε) (r : ℝ) :
    |r / regularAbs ε r| ≤ 1 := by
  rw [abs_div, abs_of_pos (regularAbs_pos hε r), div_le_one (regularAbs_pos hε r)]
  apply (Real.le_sqrt (abs_nonneg _) (by positivity)).2
  simp only [sq_abs]
  nlinarith [sq_nonneg ε]

/-- Smooth zero-preserving approximations of the interval projection. -/
def smoothNormalClip (K ε r : ℝ) : ℝ :=
  (regularAbs ε r - regularAbs ε (r - K) + regularAbs ε K - ε) / 2

theorem smoothNormalClip_zero (K : ℝ) {ε : ℝ} (hε : 0 < ε) :
    smoothNormalClip K ε 0 = 0 := by
  simp [smoothNormalClip, regularAbs, Real.sqrt_sq hε.le]

theorem smoothNormalClip_contDiff (K : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ContDiff ℝ ∞ (smoothNormalClip K ε) := by
  exact (((regularAbs_contDiff hε).sub ((regularAbs_contDiff hε).comp
    (contDiff_id.sub contDiff_const))).add contDiff_const |>.sub contDiff_const).div_const 2

theorem smoothNormalClip_hasDerivAt (K : ℝ) {ε : ℝ} (hε : 0 < ε) (r : ℝ) :
    HasDerivAt (smoothNormalClip K ε)
      ((r / regularAbs ε r - (r - K) / regularAbs ε (r - K)) / 2) r := by
  convert (((regularAbs_hasDerivAt hε r).sub
    ((regularAbs_hasDerivAt hε (r - K)).comp r ((hasDerivAt_id r).sub_const K))).add_const
    (regularAbs ε K) |>.sub_const ε).div_const 2 using 1
  · rfl
  · simp

theorem smoothNormalClip_deriv_abs_le (K : ℝ) {ε : ℝ} (hε : 0 < ε) (r : ℝ) :
    |deriv (smoothNormalClip K ε) r| ≤ 1 := by
  rw [(smoothNormalClip_hasDerivAt K hε r).deriv, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  apply (div_le_one (by norm_num : (0 : ℝ) < 2)).2
  have h := abs_sub (r / regularAbs ε r) ((r - K) / regularAbs ε (r - K))
  linarith [regularAbs_ratio_abs_le hε r, regularAbs_ratio_abs_le hε (r - K)]

theorem smoothNormalClip_lipschitz (K : ℝ) {ε : ℝ} (hε : 0 < ε) :
    LipschitzWith 1 (smoothNormalClip K ε) := by
  apply lipschitzWith_of_nnnorm_deriv_le ((smoothNormalClip_contDiff K hε).differentiable (by simp))
  intro r
  exact_mod_cast (smoothNormalClip_deriv_abs_le K hε r)

theorem smoothNormalClip_at_zero {K : ℝ} (hK : 0 ≤ K) (r : ℝ) :
    smoothNormalClip K 0 r = normalClip K r := by
  simp only [smoothNormalClip, regularAbs, zero_pow (by decide : 2 ≠ 0), add_zero,
    Real.sqrt_sq_eq_abs, sub_zero, abs_of_nonneg hK]
  rcases le_total r 0 with hr | hr
  · rw [abs_of_nonpos hr, abs_of_nonpos (by linarith : r - K ≤ 0)]
    simp only [normalClip, min_eq_right (by linarith : r ≤ K), max_eq_left hr]
    ring
  · rcases le_total r K with hrK | hrK
    · rw [abs_of_nonneg hr, abs_of_nonpos (by linarith : r - K ≤ 0)]
      simp only [normalClip, min_eq_right hrK, max_eq_right hr]
      ring
    · rw [abs_of_nonneg hr, abs_of_nonneg (by linarith : 0 ≤ r - K)]
      simp only [normalClip, min_eq_left hrK, max_eq_right hK]
      ring

theorem smoothNormalClip_tendsto {K : ℝ} (hK : 0 ≤ K) (r : ℝ)
    {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun j => smoothNormalClip K (ε j) r) atTop (𝓝 (normalClip K r)) := by
  have hc : Continuous (fun e : ℝ => smoothNormalClip K e r) := by
    unfold smoothNormalClip regularAbs
    fun_prop
  simpa only [Function.comp_def, smoothNormalClip_at_zero hK r] using hc.continuousAt.tendsto.comp hε

/-- Clipping on the genuine scalar L² space. -/
def normalClipL2 {X : Type*} [MeasurableSpace X] (μ : Measure X) (K : ℝ)
    (hK : 0 ≤ K) (f : Lp ℝ 2 μ) : Lp ℝ 2 μ :=
  (normalClip_lipschitz K).compLp (normalClip_zero hK) f

theorem normalClipL2_coe {X : Type*} [MeasurableSpace X] (μ : Measure X) (K : ℝ)
    (hK : 0 ≤ K) (f : Lp ℝ 2 μ) :
    normalClipL2 μ K hK f =ᵐ[μ] (fun x => normalClip K (f x)) :=
  (normalClip_lipschitz K).coeFn_compLp (normalClip_zero hK) f

def smoothNormalClipL2 {X : Type*} [MeasurableSpace X] (μ : Measure X) (K : ℝ)
    (ε : ℝ) (hε : 0 < ε) (f : Lp ℝ 2 μ) : Lp ℝ 2 μ :=
  (smoothNormalClip_lipschitz K hε).compLp (smoothNormalClip_zero K hε) f

theorem smoothNormalClipL2_coe {X : Type*} [MeasurableSpace X] (μ : Measure X) (K : ℝ)
    (ε : ℝ) (hε : 0 < ε) (f : Lp ℝ 2 μ) :
    smoothNormalClipL2 μ K ε hε f =ᵐ[μ] (fun x => smoothNormalClip K ε (f x)) :=
  (smoothNormalClip_lipschitz K hε).coeFn_compLp (smoothNormalClip_zero K hε) f

theorem smoothNormalClip_abs_le (K : ℝ) {ε : ℝ} (hε : 0 < ε) (r : ℝ) :
    |smoothNormalClip K ε r| ≤ |r| := by
  simpa [Real.dist_eq, smoothNormalClip_zero K hε] using
    (smoothNormalClip_lipschitz K hε).dist_le_mul r 0

theorem normalClip_abs_le {K : ℝ} (hK : 0 ≤ K) (r : ℝ) : |normalClip K r| ≤ |r| := by
  simpa [Real.dist_eq, normalClip_zero hK] using (normalClip_lipschitz K).dist_le_mul r 0

/-- The explicit smooth clips converge in L² even when the volume is infinite. -/
theorem smoothNormalClipL2_tendsto {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (K : ℝ) (hK : 0 ≤ K) (f : Lp ℝ 2 μ)
    (ε : ℕ → ℝ) (hεpos : ∀ j, 0 < ε j) (hε : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun j => smoothNormalClipL2 μ K (ε j) (hεpos j) f) atTop
      (𝓝 (normalClipL2 μ K hK f)) := by
  let F : ℕ → X → ℝ := fun j x =>
    (smoothNormalClip K (ε j) (f x) - normalClip K (f x)) ^ 2
  have hmeas (j : ℕ) : AEStronglyMeasurable (F j) μ := by
    exact (((smoothNormalClip_contDiff K (hεpos j)).continuous.comp_aestronglyMeasurable
      (Lp.memLp f).aestronglyMeasurable).sub ((normalClip_lipschitz K).continuous.comp_aestronglyMeasurable
      (Lp.memLp f).aestronglyMeasurable)).pow 2
  have hdom (j : ℕ) : ∀ᵐ x ∂μ, ‖F j x‖ ≤ 4 * f x ^ 2 := by
    apply ae_of_all
    intro x
    have hc := smoothNormalClip_abs_le K (hεpos j) (f x)
    have hz := normalClip_abs_le hK (f x)
    have hdiff : |smoothNormalClip K (ε j) (f x) - normalClip K (f x)| ≤ 2 * |f x| :=
      (abs_sub _ _).trans (by linarith)
    have hs := (sq_le_sq₀ (abs_nonneg _) (by positivity)).2 hdiff
    simp only [mul_pow, sq_abs] at hs
    norm_num only [show (2 : ℝ) ^ 2 = 4 by norm_num] at hs
    simpa [F, Real.norm_eq_abs] using hs
  have hlim : ∀ᵐ x ∂μ, Tendsto (fun j => F j x) atTop (𝓝 (0 : ℝ)) := by
    apply ae_of_all
    intro x
    simpa [F] using ((smoothNormalClip_tendsto hK (f x) hε).sub
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => normalClip K (f x)) atTop
        (𝓝 (normalClip K (f x))))).pow 2
  have ht := tendsto_integral_of_dominated_convergence (fun x => 4 * f x ^ 2)
    hmeas ((Lp.memLp f).integrable_sq.const_mul 4) hdom hlim
  have hn (j : ℕ) :
      ‖smoothNormalClipL2 μ K (ε j) (hεpos j) f - normalClipL2 μ K hK f‖ ^ 2 =
        ∫ x, F j x ∂μ := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (smoothNormalClipL2 μ K (ε j) (hεpos j) f)
      (normalClipL2 μ K hK f), smoothNormalClipL2_coe μ K (ε j) (hεpos j) f,
      normalClipL2_coe μ K hK f] with x hsub hs hc
    simp only [hsub, Pi.sub_apply, hs, hc, F, RCLike.inner_apply, conj_trivial, pow_two]
  apply tendsto_iff_norm_sub_tendsto_zero.2
  have ht' : Tendsto (fun j =>
      ‖smoothNormalClipL2 μ K (ε j) (hεpos j) f - normalClipL2 μ K hK f‖ ^ 2)
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [hn, integral_zero] using ht
  have hs := Real.continuous_sqrt.continuousAt.tendsto.comp ht'
  simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hs

theorem smoothNormalClipL2_tendsto_moving {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (K : ℝ) (hK : 0 ≤ K) (f : ℕ → Lp ℝ 2 μ) (z : Lp ℝ 2 μ)
    (hf : Tendsto f atTop (𝓝 z)) (ε : ℕ → ℝ) (hεpos : ∀ j, 0 < ε j)
    (hε : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun j => smoothNormalClipL2 μ K (ε j) (hεpos j) (f j)) atTop
      (𝓝 (normalClipL2 μ K hK z)) := by
  have hfixed := smoothNormalClipL2_tendsto μ K hK z ε hεpos hε
  apply tendsto_iff_norm_sub_tendsto_zero.2
  have hsum := (tendsto_iff_norm_sub_tendsto_zero.1 hf).add
    (tendsto_iff_norm_sub_tendsto_zero.1 hfixed)
  simp only [add_zero] at hsum
  apply squeeze_zero (fun j => norm_nonneg _) _ hsum
  intro j
  calc
    ‖smoothNormalClipL2 μ K (ε j) (hεpos j) (f j) - normalClipL2 μ K hK z‖ ≤
        ‖smoothNormalClipL2 μ K (ε j) (hεpos j) (f j) -
          smoothNormalClipL2 μ K (ε j) (hεpos j) z‖ +
        ‖smoothNormalClipL2 μ K (ε j) (hεpos j) z - normalClipL2 μ K hK z‖ := by
      have htri := norm_add_le
        (smoothNormalClipL2 μ K (ε j) (hεpos j) (f j) - smoothNormalClipL2 μ K (ε j) (hεpos j) z)
        (smoothNormalClipL2 μ K (ε j) (hεpos j) z - normalClipL2 μ K hK z)
      simpa only [sub_add_sub_cancel] using htri
    _ ≤ ‖f j - z‖ + ‖smoothNormalClipL2 μ K (ε j) (hεpos j) z - normalClipL2 μ K hK z‖ := by
      apply add_le_add _ le_rfl
      simpa only [smoothNormalClipL2, NNReal.coe_one, one_mul] using
        (smoothNormalClip_lipschitz K (hεpos j)).norm_compLp_sub_le
          (smoothNormalClip_zero K (hεpos j)) (f j) z

open L18Aux
variable {n : ℕ} {M : ComplexManifold n}

/-- The smooth clip remains an actual compactly supported smooth function. -/
def smoothNormalClipDomain (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (K ε : ℝ) (hε : 0 < ε)
    (f : ScalarEnergyDomain g μ hμ) : ScalarEnergyDomain g μ hμ :=
  ⟨fun x => smoothNormalClip K ε (f x),
    smoothFn_scalar_comp f.2.1 _ (smoothNormalClip_contDiff K hε),
    f.2.2.comp_left (smoothNormalClip_zero K hε)⟩

theorem smoothNormalClipDomain_L2 (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (K ε : ℝ) (hε : 0 < ε)
    (f : ScalarEnergyDomain g μ hμ) :
    scalarEnergyDomainL2 g μ hμ (smoothNormalClipDomain g μ hμ K ε hε f) =
      smoothNormalClipL2 μ K ε hε (scalarEnergyDomainL2 g μ hμ f) := by
  apply Lp.ext
  filter_upwards [scalarEnergyDomainL2_coe g μ hμ (smoothNormalClipDomain g μ hμ K ε hε f),
    smoothNormalClipL2_coe μ K ε hε (scalarEnergyDomainL2 g μ hμ f),
    scalarEnergyDomainL2_coe g μ hμ f] with x hleft hright hf
  rw [hleft, hright, hf]
  rfl

theorem smoothNormalClipDomain_energy_le (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (K ε : ℝ) (hε : 0 < ε)
    (f : ScalarEnergyDomain g μ hμ) :
    scalarEnergyPair g μ (smoothNormalClipDomain g μ hμ K ε hε f)
      (smoothNormalClipDomain g μ hμ K ε hε f) ≤ scalarEnergyPair g μ f f := by
  unfold scalarEnergyPair
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply integral_mono
    (scalarGradientPair_integrable g μ hμ
      (smoothNormalClipDomain g μ hμ K ε hε f).2.1
      (smoothNormalClipDomain g μ hμ K ε hε f).2.1
      (smoothNormalClipDomain g μ hμ K ε hε f).2.2)
    (scalarGradientPair_integrable g μ hμ f.2.1 f.2.1 f.2.2)
  intro x
  change scalarGradientPair g.form (fun y => smoothNormalClip K ε (f y))
    (fun y => smoothNormalClip K ε (f y)) x ≤ scalarGradientPair g.form f f x
  rw [scalarGradientPair_scalar_comp_self g.form f.2.1 _ x
    (smoothNormalClip_hasDerivAt K hε (f x)).differentiableAt]
  have hd := smoothNormalClip_deriv_abs_le K hε (f x)
  have hd' : deriv (smoothNormalClip K ε) (f x) ^ 2 ≤ 1 := by
    simpa only [sq_abs, one_pow] using (sq_le_sq₀ (abs_nonneg _) zero_le_one).2 hd
  exact mul_le_of_le_one_left (scalarGradientPair_self_nonneg g.form f x) hd'

theorem scalarEnergyDomain_norm_sq (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (f : ScalarEnergyDomain g μ hμ) :
    ‖f‖ ^ 2 = ‖scalarEnergyDomainL2 g μ hμ f‖ ^ 2 + scalarEnergyPair g μ f f := by
  rw [← real_inner_self_eq_norm_sq f, scalarEnergyDomain_inner,
    ← real_inner_self_eq_norm_sq (scalarEnergyDomainL2 g μ hμ f), scalarEnergyDomainL2_inner]
  rfl

theorem smoothNormalClipDomain_norm_le (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (K ε : ℝ) (hε : 0 < ε)
    (f : ScalarEnergyDomain g μ hμ) :
    ‖smoothNormalClipDomain g μ hμ K ε hε f‖ ≤ ‖f‖ := by
  have hL2 : ‖scalarEnergyDomainL2 g μ hμ (smoothNormalClipDomain g μ hμ K ε hε f)‖ ≤
      ‖scalarEnergyDomainL2 g μ hμ f‖ := by
    rw [smoothNormalClipDomain_L2]
    simpa only [smoothNormalClipL2, NNReal.coe_one, one_mul] using
      (smoothNormalClip_lipschitz K hε).norm_compLp_le
        (smoothNormalClip_zero K hε) (scalarEnergyDomainL2 g μ hμ f)
  have hE := smoothNormalClipDomain_energy_le g μ hμ K ε hε f
  have hnorm := scalarEnergyDomain_norm_sq g μ hμ f
  have hnorm' := scalarEnergyDomain_norm_sq g μ hμ (smoothNormalClipDomain g μ hμ K ε hε f)
  nlinarith [norm_nonneg f, norm_nonneg (smoothNormalClipDomain g μ hμ K ε hε f),
    norm_nonneg (scalarEnergyDomainL2 g μ hμ f),
    norm_nonneg (scalarEnergyDomainL2 g μ hμ (smoothNormalClipDomain g μ hμ K ε hε f))]

/-- The true normal interval projection belongs to the image of the actual
energy completion, and its physical energy cannot increase. -/
theorem scalarEnergy_normalClip_L2 (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (u : ScalarEnergySpace g μ hμ)
    (K : ℝ) (hK : 0 ≤ K) :
    ∃ v : ScalarEnergySpace g μ hμ,
      scalarEnergyL2 g μ hμ v = normalClipL2 μ K hK (scalarEnergyL2 g μ hμ u) ∧
      ‖v‖ ^ 2 - ‖scalarEnergyL2 g μ hμ v‖ ^ 2 ≤
        ‖u‖ ^ 2 - ‖scalarEnergyL2 g μ hμ u‖ ^ 2 := by
  classical
  let H := ScalarEnergySpace g μ hμ
  let J := scalarEnergyL2 g μ hμ
  obtain ⟨q, hqmem, hq⟩ := mem_closure_iff_seq_limit.1
    ((UniformSpace.Completion.denseRange_coe (α := ScalarEnergyDomain g μ hμ)) u)
  choose f hf using hqmem
  have hcore : Tendsto (fun j => (f j : H)) atTop (𝓝 u) := by
    simpa only [hf] using hq
  let ε : ℕ → ℝ := fun j => 1 / ((j : ℝ) + 1)
  have hεpos (j : ℕ) : 0 < ε j := by dsimp [ε]; positivity
  have hε : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let w₀ : ℕ → ScalarEnergyDomain g μ hμ :=
    fun j => smoothNormalClipDomain g μ hμ K (ε j) (hεpos j) (f j)
  let w : ℕ → H := fun j => (w₀ j : H)
  let z := normalClipL2 μ K hK (J u)
  have hJcore : Tendsto (fun j => scalarEnergyDomainL2 g μ hμ (f j)) atTop (𝓝 (J u)) := by
    simpa only [Function.comp_def, J, scalarEnergyL2_coe] using J.continuous.continuousAt.tendsto.comp hcore
  have hstrong : Tendsto (fun j => J (w j)) atTop (𝓝 z) := by
    have ht := smoothNormalClipL2_tendsto_moving μ K hK _ (J u) hJcore ε hεpos hε
    simpa only [J, w, w₀, scalarEnergyL2_coe, smoothNormalClipDomain_L2, z] using ht
  have hbound : ∀ᶠ j in atTop, ‖w j‖ ≤ ‖u‖ + 1 := by
    have hb := hcore.norm.eventually (gt_mem_nhds (lt_add_one ‖u‖))
    filter_upwards [hb] with j hj
    rw [UniformSpace.Completion.norm_coe] at hj
    have hw := smoothNormalClipDomain_norm_le g μ hμ K (ε j) (hεpos j) (f j)
    change ‖(w₀ j : ScalarEnergySpace g μ hμ)‖ ≤ ‖u‖ + 1
    rw [UniformSpace.Completion.norm_coe]
    exact hw.trans hj.le
  let a : ℕ → ℝ := fun j => ‖(f j : H)‖ ^ 2 -
    ‖scalarEnergyDomainL2 g μ hμ (f j)‖ ^ 2 + ‖J (w j)‖ ^ 2
  have hupper : ∀ᶠ j in atTop, ‖w j‖ ^ 2 ≤ a j := by
    apply Eventually.of_forall
    intro j
    have hE := smoothNormalClipDomain_energy_le g μ hμ K (ε j) (hεpos j) (f j)
    have hw := scalarEnergyDomain_norm_sq g μ hμ (w₀ j)
    have hf' := scalarEnergyDomain_norm_sq g μ hμ (f j)
    dsimp only [a, w]
    rw [UniformSpace.Completion.norm_coe, UniformSpace.Completion.norm_coe, scalarEnergyL2_coe]
    change ‖w₀ j‖ ^ 2 ≤ ‖f j‖ ^ 2 - ‖scalarEnergyDomainL2 g μ hμ (f j)‖ ^ 2 +
      ‖scalarEnergyDomainL2 g μ hμ (w₀ j)‖ ^ 2
    linarith
  have ha : Tendsto a atTop
      (𝓝 (‖u‖ ^ 2 - ‖J u‖ ^ 2 + ‖z‖ ^ 2)) :=
    ((hcore.norm.pow 2).sub (hJcore.norm.pow 2)).add (hstrong.norm.pow 2)
  obtain ⟨v, hvJ, hv⟩ := hilbert_strong_image_limit J w z a _ (‖u‖ + 1)
    hbound hstrong hupper ha
  refine ⟨v, hvJ, ?_⟩
  change ‖v‖ ^ 2 - ‖J v‖ ^ 2 ≤ ‖u‖ ^ 2 - ‖J u‖ ^ 2
  rw [hvJ]
  linarith

theorem scalarEnergy_normalClip (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (u : ScalarEnergySpace g μ hμ)
    (K : ℝ) (hK : 0 < K) :
    ∃ v : ScalarEnergySpace g μ hμ,
      (scalarEnergyL2 g μ hμ v : M.Carrier → ℝ) =ᵐ[μ]
        (fun x => normalClip K ((scalarEnergyL2 g μ hμ u) x)) ∧
      ‖v‖ ^ 2 - ‖scalarEnergyL2 g μ hμ v‖ ^ 2 ≤
        ‖u‖ ^ 2 - ‖scalarEnergyL2 g μ hμ u‖ ^ 2 := by
  obtain ⟨v, hv, hE⟩ := scalarEnergy_normalClip_L2 g μ hμ u K hK.le
  exact ⟨v, hv ▸ normalClipL2_coe μ K hK.le (scalarEnergyL2 g μ hμ u), hE⟩

end Yau.LeafProofs.L19Aux
