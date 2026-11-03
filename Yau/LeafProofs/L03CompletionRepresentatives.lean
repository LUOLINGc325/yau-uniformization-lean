import Yau.LeafProofs.L03CompletionFastAE

open MeasureTheory Filter
open scoped Topology InnerProductSpace

noncomputable section

namespace Yau.LeafProofs.L03

variable {n k : ℕ} {M : ComplexManifold n}

theorem lintegral_formNormSq_le_liminf_of_ae_fiber_limit
    (g : SmoothMetric M) (μ : Measure M.Carrier) (u : ℕ → L2FormSpace g μ k)
    (A : RealForm M k)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun j => (u j).toSection x) atTop (𝓝 (A x))) :
    (∫⁻ x, ENNReal.ofReal (formNormSq g.form A x) ∂μ) ≤
      liminf (fun j => ENNReal.ofReal (‖realizeL2Form g μ (u j)‖ ^ 2)) atTop := by
  let f := fun j x => ENNReal.ofReal (formNormSq g.form (u j).toSection x)
  have hm (j : ℕ) : AEMeasurable (f j) μ := ENNReal.measurable_ofReal.comp_aemeasurable
    (formNormSq_aestronglyMeasurable g μ _ (u j).toSection_l2).aemeasurable
  have he : (fun x => ENNReal.ofReal (formNormSq g.form A x)) =ᵐ[μ]
      (fun x => liminf (fun j => f j x) atTop) := by
    filter_upwards [hlim] with x hx
    exact ((ENNReal.continuous_ofReal.tendsto _).comp
      (formNormSq_tendsto_of_fiber_tendsto g.form _ A x hx)).liminf_eq.symm
  have hi (j : ℕ) : (∫⁻ x, f j x ∂μ) = ENNReal.ofReal (‖realizeL2Form g μ (u j)‖ ^ 2) := by
    rw [realizeL2Form_norm_sq]
    exact (ofReal_integral_eq_lintegral_ofReal (formNormSq_integrable g μ _ (u j).toSection_l2)
      (Eventually.of_forall fun x => formNormSq_nonneg g.form _ x)).symm
  calc
    _ = ∫⁻ x, liminf (fun j => f j x) atTop ∂μ := lintegral_congr_ae he
    _ ≤ liminf (fun j => ∫⁻ x, f j x ∂μ) atTop := lintegral_liminf_le' hm
    _ = _ := by simp only [hi]

/-- Fixed-chart coefficient measurability and Fatou construct an actual
L² representative for an AE fibre limit of a Hilbert-convergent section
sequence. This does not assume surjectivity of realization. -/
theorem realize_eq_of_ae_fiber_limit
    (g : SmoothMetric M) (μ : Measure M.Carrier) (u : ℕ → L2FormSpace g μ k)
    (v : L2FormHilbert g μ k)
    (hv : Tendsto (fun j => realizeL2Form g μ (u j)) atTop (𝓝 v))
    (A : RealForm M k)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun j => (u j).toSection x) atTop (𝓝 (A x))) :
    ∃ hA : L2RealForm g.form μ A, realizeL2Form g μ (L2FormSpace.ofSection A hA) = v := by
  have hcoeff : ∀ (b : M.Carrier) (I : Fin k → RIdx n), AEStronglyMeasurable
      (fun y => A y (fun r => chartVec b y (realVec (I r))))
        (μ.restrict (chartAt (ComplexVector n) b).source) := by
    intro b I
    apply aestronglyMeasurable_of_tendsto_ae atTop (fun j => (u j).toSection_l2.1 b I)
    filter_upwards [ae_restrict_of_ae hlim] with y hy
    letI : ContinuousSMul ℝ (TangentVector M y) := IsScalarTower.continuousSMul ℂ
    exact ((ContinuousAlternatingMap.apply ℝ (TangentVector M y) ℝ
      (fun r => chartVec b y (realVec (I r)))).continuous.tendsto (A y)).comp hy
  have hnorm : Tendsto (fun j => ENNReal.ofReal (‖realizeL2Form g μ (u j)‖ ^ 2)) atTop
      (𝓝 (ENNReal.ofReal (‖v‖ ^ 2))) :=
    (ENNReal.continuous_ofReal.tendsto _).comp (hv.norm.pow 2)
  have hfatou := lintegral_formNormSq_le_liminf_of_ae_fiber_limit g μ u A hlim
  rw [hnorm.liminf_eq] at hfatou
  have hA : L2RealForm g.form μ A := ⟨hcoeff, hfatou.trans_lt ENNReal.ofReal_lt_top⟩
  refine ⟨hA, ?_⟩
  have hb (j : ℕ) : formL2DistanceSq g.form μ (u j).toSection A ≤
      ENNReal.ofReal (‖realizeL2Form g μ (u j) - v‖ ^ 2) := by
    let w := fun m => u j - u m
    have hwlim : ∀ᵐ x ∂μ, Tendsto (fun m => (w m).toSection x) atTop
        (𝓝 ((u j).toSection x - A x)) := by
      filter_upwards [hlim] with x hx
      exact tendsto_const_nhds.sub hx
    have hf := lintegral_formNormSq_le_liminf_of_ae_fiber_limit g μ w ((u j).toSection - A) hwlim
    have hwt : Tendsto (fun m => ENNReal.ofReal (‖realizeL2Form g μ (w m)‖ ^ 2)) atTop
        (𝓝 (ENNReal.ofReal (‖realizeL2Form g μ (u j) - v‖ ^ 2))) := by
      simp only [w, realizeL2Form_sub]
      exact (ENNReal.continuous_ofReal.tendsto _).comp ((tendsto_const_nhds.sub hv).norm.pow 2)
    rw [hwt.liminf_eq] at hf
    exact hf
  have hzero : Tendsto (fun j => ENNReal.ofReal (‖realizeL2Form g μ (u j) - v‖ ^ 2)) atTop (𝓝 0) := by
    have hp : Tendsto (fun j => ‖realizeL2Form g μ (u j) - v‖ ^ 2) atTop (𝓝 (0 : ℝ)) := by
      simpa only [zero_pow (by decide : 2 ≠ 0)] using (tendsto_iff_norm_sub_tendsto_zero.mp hv).pow 2
    simpa only [Function.comp_def, ENNReal.ofReal_zero] using (ENNReal.continuous_ofReal.tendsto 0).comp hp
  have hd : Tendsto (fun j => formL2DistanceSq g.form μ (u j).toSection A) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hzero (fun _ => bot_le) hb
  exact tendsto_nhds_unique ((tendsto_realizeL2Form_iff g μ u (L2FormSpace.ofSection A hA)).mpr hd) hv

theorem exists_fast_realizeL2Form_seq (g : SmoothMetric M) (μ : Measure M.Carrier)
    (v : L2FormHilbert g μ k) : ∃ u : ℕ → L2FormSpace g μ k,
      Tendsto (fun j => realizeL2Form g μ (u j)) atTop (𝓝 v) ∧
      ∀ j, ‖realizeL2Form g μ (u (j + 1)) - realizeL2Form g μ (u j)‖ ≤ (1 / 4 : ℝ) ^ j := by
  have hex (j : ℕ) := (realizeL2Form_denseRange g μ k).exists_dist_lt v
    (show 0 < (1 / 4 : ℝ) ^ (j + 1) by positivity)
  choose u hu using hex
  have hgeom : Tendsto (fun j : ℕ => (1 / 4 : ℝ) ^ (j + 1)) atTop (𝓝 0) := by
    simpa only [pow_succ, zero_mul] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (show 0 ≤ (1 / 4 : ℝ) by norm_num)
        (show (1 / 4 : ℝ) < 1 by norm_num)).mul_const (1 / 4 : ℝ)
  refine ⟨u, ?_, ?_⟩
  · apply tendsto_iff_norm_sub_tendsto_zero.mpr
    apply squeeze_zero (fun j => norm_nonneg _) _ hgeom
    intro j
    rw [← dist_eq_norm, dist_comm]
    exact (hu j).le
  · intro j
    rw [← dist_eq_norm]
    calc
      _ ≤ dist (realizeL2Form g μ (u (j + 1))) v + dist v (realizeL2Form g μ (u j)) := dist_triangle _ _ _
      _ ≤ (1 / 4 : ℝ) ^ (j + 2) + (1 / 4 : ℝ) ^ (j + 1) := add_le_add
        (by rw [dist_comm]; exact (hu (j + 1)).le) (hu j).le
      _ ≤ (1 / 4 : ℝ) ^ j := by
        simp only [pow_succ]
        nlinarith [pow_nonneg (show 0 ≤ (1 / 4 : ℝ) by norm_num) j]

/-- Every vector of the genuine Hilbert completion has an actual
measurable L² alternating-section representative, for every measure.
This is surjectivity, proved from a fast intrinsic Cauchy sequence,
actual fibre reconstruction, chart coefficient measurability and Fatou. -/
theorem l2FormHilbert_exists_section (g : SmoothMetric M) (μ : Measure M.Carrier)
    (v : L2FormHilbert g μ k) : ∃ A : RealForm M k, ∃ hA : L2RealForm g.form μ A,
      realizeL2Form g μ (L2FormSpace.ofSection A hA) = v := by
  obtain ⟨u, hv, hstep⟩ := exists_fast_realizeL2Form_seq g μ v
  obtain ⟨A, hlim⟩ := exists_ae_fiber_limit_of_fast_realize g μ u hstep
  obtain ⟨hA, he⟩ := realize_eq_of_ae_fiber_limit g μ u v hv A hlim
  exact ⟨A, hA, he⟩

theorem realizeL2Form_surjective (g : SmoothMetric M) (μ : Measure M.Carrier) (k : ℕ) :
    Function.Surjective (realizeL2Form (k := k) g μ) := by
  intro v
  obtain ⟨A, hA, he⟩ := l2FormHilbert_exists_section g μ v
  exact ⟨L2FormSpace.ofSection A hA, he⟩

end Yau.LeafProofs.L03
