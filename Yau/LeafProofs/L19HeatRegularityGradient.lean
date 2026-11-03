import Yau.LeafProofs.L19HeatRegularityChart

/-! Actual chart derivatives on the scalar energy completion. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff Manifold InnerProductSpace
namespace Yau.LeafProofs.L19Aux
open L18Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- Coordinate differential evaluation is bounded by the actual dual
quadratic form and the corresponding covariant metric diagonal. -/
theorem scalarChart_derivative_sq_le (g : HermitianField M) (x : M.Carrier)
    {z : ComplexVector n} (hz : z ∈ chartTarget x) (f : ComplexVector n → ℝ) (i : RIdx n) :
    (rDeriv f z i)^2 ≤ realMetricFn g x z i i * chartGradientPair g x f f z := by
  classical
  let Q := realMetricFn g x z
  let v := fun j => rDeriv f z j
  let e : RIdx n → ℝ := Pi.single i 1
  let w := Q.mulVec e
  have hQ : Q.PosDef := L12Aux.realMetricFn_posDef g x z hz
  have hd : IsUnit Q.det := (Matrix.isUnit_iff_isUnit_det _).mp hQ.isUnit
  have hw : Q⁻¹.mulVec w = e := by
    dsimp only [w]
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul Q hd, Matrix.one_mulVec]
  have hwi : w i = Q i i := by simp only [w, e, Matrix.mulVec_single_one, Matrix.col_apply]
  have hh := hQ.inv.star_dotProduct_mulVec_mul_le v w
  simp only [star_trivial, hw, e, dotProduct_single_one] at hh
  simpa only [v, Q, pow_two, hwi, mul_comm, chartGradientPair,
    Matrix.toBilin'_apply', star_trivial] using hh

/-- The needed chart derivative constant is obtained from the actual
metric and density on a compact set; it is uniform over all scalars. -/
theorem scalarChart_derivative_density_bound (g : SmoothMetric M) (x : M.Carrier)
    {K : Set (ComplexVector n)} (hK : IsCompact K) (hKt : K ⊆ chartTarget x)
    (i : RIdx n) : ∃ C : ℝ, 0 < C ∧ ∀ z ∈ K,
      realMetricFn g.form x z i i ≤ C * Real.sqrt (realMetricFn g.form x z).det := by
  let ρ := fun z => Real.sqrt (realMetricFn g.form x z).det
  have hρpos (z) (hz : z ∈ K) : 0 < ρ z := L12Aux.volumeDensity_pos g.form x z (hKt hz)
  have hc : ContinuousOn (fun z => realMetricFn g.form x z i i / ρ z) K :=
    ((metricSmooth_of_smoothMetric g x i i).continuousOn.mono hKt).div
      ((volumeDensity_contDiffOn g x).continuousOn.mono hKt)
      (fun z hz => ne_of_gt (hρpos z hz))
  obtain ⟨c, hc⟩ := hK.bddAbove_image hc
  refine ⟨max c 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro z hz
  exact (div_le_iff₀ (hρpos z hz)).mp ((hc ⟨z, hz, rfl⟩).trans (le_max_left _ _))

/-- Local Euclidean integrability of every true core derivative follows
from the global energy integral and the computed metric comparison. -/
theorem scalarChartDerivative_memLp (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (x : M.Carrier)
    {O : Set (ComplexVector n)} (hO : MeasurableSet O) (hOt : O ⊆ chartTarget x)
    (i : RIdx n) {C : ℝ} (_hC : 0 ≤ C)
    (hbound : ∀ z ∈ O, realMetricFn g.form x z i i ≤
      C * Real.sqrt (realMetricFn g.form x z).det)
    (f : ScalarEnergyDomain g μ hμ) :
    MemLp (fun z => rDeriv (inChart x f) z i) 2 (volume.restrict O) := by
  let P := fun z => Real.sqrt (realMetricFn g.form x z).det *
    scalarGradientPair g.form f f (chartInv x z)
  have hP : Integrable P (volume.restrict O) := by
    have hh := integrableOn_chart_volume_smul g μ hμ x
      (scalarGradientPair_integrable g μ hμ f.2.1 f.2.1 f.2.2).integrableOn
    rw [lebesgueC_eq_volume] at hh
    change Integrable P (volume.restrict (chartTarget x)) at hh
    exact hh.mono_measure (Measure.restrict_mono hOt le_rfl)
  have hm : AEStronglyMeasurable (fun z => rDeriv (inChart x f) z i) (volume.restrict O) :=
    ((rDeriv_contDiffOn (isOpen_extChartAt_target (I := ComplexModel n) x)
      (f.2.1 x) i).continuousOn.mono hOt).aestronglyMeasurable hO
  apply (memLp_two_iff_integrable_sq hm).mpr
  apply (hP.const_mul C).mono_nonneg (hm.pow 2)
    (ae_of_all _ fun _ => sq_nonneg _)
  filter_upwards [ae_restrict_mem hO] with z hz
  have hp := scalarChart_derivative_sq_le g.form x (hOt hz) (inChart x f) i
  have heq := scalarGradientPair_eq_chart g.form f.2.1 f.2.1 x (hOt hz)
  have hnonneg := chartGradientPair_self_nonneg g.form x (hOt hz) (inChart x f)
  calc
    _ ≤ _ := hp
    _ ≤ (C * Real.sqrt (realMetricFn g.form x z).det) *
        chartGradientPair g.form x (inChart x f) (inChart x f) z :=
      mul_le_mul_of_nonneg_right (hbound z hz) hnonneg
    _ = C * P z := by dsimp only [P]; rw [heq]; ring

/-- The genuine core chart derivative as a Euclidean L² equivalence class. -/
def scalarChartDerivative (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (x : M.Carrier)
    {O : Set (ComplexVector n)} (hO : MeasurableSet O) (hOt : O ⊆ chartTarget x)
    (i : RIdx n) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ z ∈ O, realMetricFn g.form x z i i ≤
      C * Real.sqrt (realMetricFn g.form x z).det)
    (f : ScalarEnergyDomain g μ hμ) : Lp ℝ 2 (volume.restrict O) :=
  (scalarChartDerivative_memLp g μ hμ x hO hOt i hC hbound f).toLp _

theorem scalarChartDerivative_coe (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (x : M.Carrier)
    {O : Set (ComplexVector n)} (hO : MeasurableSet O) (hOt : O ⊆ chartTarget x)
    (i : RIdx n) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ z ∈ O, realMetricFn g.form x z i i ≤
      C * Real.sqrt (realMetricFn g.form x z).det)
    (f : ScalarEnergyDomain g μ hμ) :
    scalarChartDerivative g μ hμ x hO hOt i hC hbound f =ᵐ[volume.restrict O]
      (fun z => rDeriv (inChart x f) z i) :=
  (scalarChartDerivative_memLp g μ hμ x hO hOt i hC hbound f).coeFn_toLp

/-- The core derivative is bounded in the actual H¹ norm. -/
theorem scalarChartDerivative_norm_le (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (x : M.Carrier)
    {O : Set (ComplexVector n)} (hO : MeasurableSet O) (hOt : O ⊆ chartTarget x)
    (i : RIdx n) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ z ∈ O, realMetricFn g.form x z i i ≤
      C * Real.sqrt (realMetricFn g.form x z).det)
    (f : ScalarEnergyDomain g μ hμ) :
    ‖scalarChartDerivative g μ hμ x hO hOt i hC hbound f‖ ≤ Real.sqrt (2 * C) * ‖f‖ := by
  let D := scalarChartDerivative g μ hμ x hO hOt i hC hbound f
  let P := fun z => Real.sqrt (realMetricFn g.form x z).det *
    scalarGradientPair g.form f f (chartInv x z)
  have hPg := scalarGradientPair_integrable g μ hμ f.2.1 f.2.1 f.2.2
  have hPt : Integrable P (volume.restrict (chartTarget x)) := by
    have hh := integrableOn_chart_volume_smul g μ hμ x hPg.integrableOn
    rw [lebesgueC_eq_volume] at hh
    exact hh
  have hP := hPt.mono_measure (Measure.restrict_mono hOt le_rfl)
  have hD := scalarChartDerivative_memLp g μ hμ x hO hOt i hC hbound f
  have hDsq := (memLp_two_iff_integrable_sq hD.aestronglyMeasurable).mp hD
  have hn : ‖D‖^2 = ∫ z in O, (rDeriv (inChart x f) z i)^2 := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [scalarChartDerivative_coe g μ hμ x hO hOt i hC hbound f] with z hz
    simp only [D] at *
    rw [hz]
    simp only [RCLike.inner_apply, conj_trivial, pow_two]
  have hdom : ∀ z ∈ O, (rDeriv (inChart x f) z i)^2 ≤ C * P z := by
    intro z hz
    have hp := scalarChart_derivative_sq_le g.form x (hOt hz) (inChart x f) i
    have heq := scalarGradientPair_eq_chart g.form f.2.1 f.2.1 x (hOt hz)
    calc
      _ ≤ _ := hp
      _ ≤ (C * Real.sqrt (realMetricFn g.form x z).det) *
          chartGradientPair g.form x (inChart x f) (inChart x f) z :=
        mul_le_mul_of_nonneg_right (hbound z hz)
          (chartGradientPair_self_nonneg g.form x (hOt hz) (inChart x f))
      _ = C * P z := by dsimp only [P]; rw [heq]; ring
  have hle : ‖D‖^2 ≤ C * ∫ y, scalarGradientPair g.form f f y ∂μ := by
    rw [hn]
    calc
      _ ≤ ∫ z in O, C * P z := integral_mono_ae hDsq (hP.const_mul C)
        (ae_restrict_of_forall_mem hO hdom)
      _ = C * ∫ z in O, P z := integral_const_mul C _
      _ ≤ C * ∫ z in chartTarget x, P z := mul_le_mul_of_nonneg_left
        (integral_mono_measure (Measure.restrict_mono hOt le_rfl)
          (ae_of_all _ fun z => mul_nonneg (Real.sqrt_nonneg _)
            (scalarGradientPair_self_nonneg g.form f (chartInv x z))) hPt) hC
      _ = C * ∫ y in (extChartAt (ComplexModel n) x).source,
          scalarGradientPair g.form f f y ∂μ := by
        congr 1
        have hh := integral_chart_volume_ae g μ hμ x hPg.aestronglyMeasurable.restrict
        rw [lebesgueC_eq_volume] at hh
        exact hh.symm
      _ ≤ C * ∫ y, scalarGradientPair g.form f f y ∂μ := mul_le_mul_of_nonneg_left
        (setIntegral_le_integral hPg (ae_of_all _ (scalarGradientPair_self_nonneg g.form f))) hC
  have hH1 := real_inner_self_eq_norm_sq f
  rw [scalarEnergyDomain_inner] at hH1
  unfold scalarSobolevPair scalarEnergyPair at hH1
  have hnonneg : 0 ≤ ∫ y, f y * f y ∂μ := integral_nonneg fun _ => mul_self_nonneg _
  have hglobal : (∫ y, scalarGradientPair g.form f f y ∂μ) ≤ 2 * ‖f‖^2 := by linarith
  have hsq : ‖D‖^2 ≤ (Real.sqrt (2 * C) * ‖f‖)^2 := by
    rw [mul_pow, Real.sq_sqrt (mul_nonneg (by norm_num) hC)]
    nlinarith [mul_le_mul_of_nonneg_left hglobal hC]
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp hsq

/-- The derivative map is linear on the genuine smooth compact domain. -/
def scalarChartDerivativeLinear (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (x : M.Carrier)
    {O : Set (ComplexVector n)} (hO : MeasurableSet O) (hOt : O ⊆ chartTarget x)
    (i : RIdx n) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ z ∈ O, realMetricFn g.form x z i i ≤
      C * Real.sqrt (realMetricFn g.form x z).det) :
    ScalarEnergyDomain g μ hμ →ₗ[ℝ] Lp ℝ 2 (volume.restrict O) where
  toFun := scalarChartDerivative g μ hμ x hO hOt i hC hbound
  map_add' f k := by
    apply Lp.ext
    filter_upwards [scalarChartDerivative_coe g μ hμ x hO hOt i hC hbound (f + k),
      scalarChartDerivative_coe g μ hμ x hO hOt i hC hbound f,
      scalarChartDerivative_coe g μ hμ x hO hOt i hC hbound k,
      Lp.coeFn_add (scalarChartDerivative g μ hμ x hO hOt i hC hbound f)
        (scalarChartDerivative g μ hμ x hO hOt i hC hbound k), ae_restrict_mem hO]
      with z hsum hf hk hLp hz
    rw [hsum, hLp, Pi.add_apply, hf, hk]
    change rDeriv (inChart x f + inChart x k) z i = _
    unfold rDeriv
    rw [fderiv_add ((contDiffAt_inChart f.2.1 x (hOt hz)).differentiableAt (by simp))
      ((contDiffAt_inChart k.2.1 x (hOt hz)).differentiableAt (by simp))]
    rfl
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [scalarChartDerivative_coe g μ hμ x hO hOt i hC hbound (c • f),
      scalarChartDerivative_coe g μ hμ x hO hOt i hC hbound f,
      Lp.coeFn_smul c (scalarChartDerivative g μ hμ x hO hOt i hC hbound f), ae_restrict_mem hO]
      with z hsmul hf hLp hz
    simp only [RingHom.id_apply]
    rw [hsmul, hLp, Pi.smul_apply, hf]
    change rDeriv (fun w => c * f (chartInv x w)) z i = c * _
    exact rDeriv_const_mul ((contDiffAt_inChart f.2.1 x (hOt hz)).differentiableAt (by simp)) c i

/-- Bounded core derivative with its genuine energy norm. -/
def scalarChartDerivativeCLM (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (x : M.Carrier)
    {O : Set (ComplexVector n)} (hO : MeasurableSet O) (hOt : O ⊆ chartTarget x)
    (i : RIdx n) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ z ∈ O, realMetricFn g.form x z i i ≤
      C * Real.sqrt (realMetricFn g.form x z).det) :
    ScalarEnergyDomain g μ hμ →L[ℝ] Lp ℝ 2 (volume.restrict O) :=
  (scalarChartDerivativeLinear g μ hμ x hO hOt i hC hbound).mkContinuous
    (Real.sqrt (2 * C)) (scalarChartDerivative_norm_le g μ hμ x hO hOt i hC hbound)

/-- The true chart derivative extends to the actual scalar energy completion. -/
def scalarEnergy_chartDerivativeCLM (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (x : M.Carrier)
    {O : Set (ComplexVector n)} (hO : IsOpen O) (hOc : IsCompact (closure O))
    (hOt : closure O ⊆ chartTarget x) (i : RIdx n) :
    ScalarEnergySpace g μ hμ →L[ℝ] Lp ℝ 2 (volume.restrict O) :=
  let hC := (scalarChart_derivative_density_bound g x hOc hOt i).choose_spec
  (scalarChartDerivativeCLM g μ hμ x hO.measurableSet (subset_closure.trans hOt) i
    hC.1.le (fun z hz => hC.2 z (subset_closure hz))).extend UniformSpace.Completion.toComplL

/-- The completed derivative recovers every true smooth core derivative. -/
theorem scalarEnergy_chartDerivativeCLM_coe (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (x : M.Carrier)
    {O : Set (ComplexVector n)} (hO : IsOpen O) (hOc : IsCompact (closure O))
    (hOt : closure O ⊆ chartTarget x) (i : RIdx n) (f : ScalarEnergyDomain g μ hμ) :
    scalarEnergy_chartDerivativeCLM g μ hμ x hO hOc hOt i (f : ScalarEnergySpace g μ hμ)
      =ᵐ[volume.restrict O] (fun z => rDeriv (inChart x f) z i) := by
  let hC := (scalarChart_derivative_density_bound g x hOc hOt i).choose_spec
  have heq : scalarEnergy_chartDerivativeCLM g μ hμ x hO hOc hOt i
      (f : ScalarEnergySpace g μ hμ) =
      scalarChartDerivative g μ hμ x hO.measurableSet (subset_closure.trans hOt) i
        hC.1.le (fun z hz => hC.2 z (subset_closure hz)) f := by
    exact ContinuousLinearMap.extend_eq
      (scalarChartDerivativeCLM g μ hμ x hO.measurableSet (subset_closure.trans hOt) i
        hC.1.le (fun z hz => hC.2 z (subset_closure hz)))
      UniformSpace.Completion.denseRange_coe (UniformSpace.Completion.isUniformInducing_coe _) f
  rw [heq]
  exact scalarChartDerivative_coe g μ hμ x hO.measurableSet (subset_closure.trans hOt) i
    (scalarChart_derivative_density_bound g x hOc hOt i).choose_spec.1.le
    (fun z hz => (scalarChart_derivative_density_bound g x hOc hOt i).choose_spec.2 z
      (subset_closure hz)) f

end Yau.LeafProofs.L19Aux
