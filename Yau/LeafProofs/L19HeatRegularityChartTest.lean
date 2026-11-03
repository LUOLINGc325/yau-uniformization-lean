import Yau.LeafProofs.L19HeatRegularityWeakGradient
import Yau.LeafProofs.L19ScalarResolvent

/-! Computed density-weighted chart test functions and their energy pairings. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff Manifold InnerProductSpace
namespace Yau.LeafProofs.L19Aux
open L18Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- The actual global compact smooth test obtained by zero-pushing a true
compact smooth chart test. -/
def scalarEnergy_chartTest (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (x : M.Carrier)
    {η : ComplexVector n → ℝ} (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η)
    (hηt : tsupport η ⊆ chartTarget x) : ScalarEnergyDomain g μ hμ :=
  ⟨chartPushforwardZero x η, smoothFn_chartPushforwardZero x hη hcη hηt,
    (chartPushforwardZero_properties x hη hcη hηt).1⟩

/-- One computed chart flux coefficient, with the project factor one half. -/
def scalarChartTestFluxEntry (g : SmoothMetric M) (x : M.Carrier)
    (η : ComplexVector n → ℝ) (i j : RIdx n) (z : ComplexVector n) : ℝ :=
  rDeriv η z i * ((1 / 2 : ℝ) * Real.sqrt (realMetricFn g.form x z).det *
    (realMetricFn g.form x z)⁻¹ i j)

/-- A genuine compact chart test yields actual L² flux coefficients. -/
theorem scalarChartTestFluxEntry_memLp (g : SmoothMetric M) (x : M.Carrier)
    {η : ComplexVector n → ℝ} (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η)
    (hηt : tsupport η ⊆ chartTarget x) (i j : RIdx n) :
    MemLp (scalarChartTestFluxEntry g x η i j) 2 volume := by
  have hd : Continuous (fun z => rDeriv η z i) :=
    ((hη.of_le (by simp) : ContDiff ℝ 1 η).continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hcd : HasCompactSupport (fun z => rDeriv η z i) := hcη.fderiv_apply ℝ (realVec i)
  have hc : ContinuousOn (fun z => (1 / 2 : ℝ) * Real.sqrt (realMetricFn g.form x z).det *
      (realMetricFn g.form x z)⁻¹ i j) (chartTarget x) :=
    (continuousOn_const.mul (volumeDensity_contDiffOn g x).continuousOn).mul
      (realMetricFn_inverse_contDiffOn g x i j).continuousOn
  exact (continuous_mul_of_continuousAt_tsupport hd (fun z hz =>
    hc.continuousAt ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds
      (hηt ((tsupport_fderiv_apply_subset ℝ (realVec i)) hz))))).memLp_of_hasCompactSupport
        hcd.mul_right

/-- The actual global core energy is exactly its computed local
coordinate integral; support and chart transport are proved inside. -/
theorem scalarEnergy_core_chartTest (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (x : M.Carrier)
    {O : Set (ComplexVector n)} (_hO : IsOpen O) (hOt : O ⊆ chartTarget x)
    (f : ScalarEnergyDomain g μ hμ)
    {η : ComplexVector n → ℝ} (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η)
    (hηO : tsupport η ⊆ O) :
    scalarEnergyPair g μ f (scalarEnergy_chartTest g μ hμ x hη hcη (hηO.trans hOt)) =
      ∫ z in O, ∑ i, ∑ j, rDeriv (inChart x f) z j * scalarChartTestFluxEntry g x η i j z := by
  let k := scalarEnergy_chartTest g μ hμ x hη hcη (hηO.trans hOt)
  have hks : tsupport (k : M.Carrier → ℝ) ⊆ (extChartAt (ComplexModel n) x).source :=
    (chartPushforwardZero_properties x hη hcη (hηO.trans hOt)).2.2
  have hdiff {z : ComplexVector n} (hz : z ∈ chartTarget x) :
      fderiv ℝ (inChart x k) z = fderiv ℝ η z := by
    apply Filter.EventuallyEq.fderiv_eq
    filter_upwards [(isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz] with w hw
    exact chartPushforwardZero_chartInv x η hw
  have hsource : (∫ y, scalarGradientPair g.form k f y ∂μ) =
      ∫ y in (extChartAt (ComplexModel n) x).source, scalarGradientPair g.form k f y ∂μ := by
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro y hy
    exact scalarGradientPair_zero_of_notMem_tsupport g.form k f (fun hh => hy (hks hh))
  have htransport := integral_chart_volume_ae g μ hμ x
    (scalarGradientPair_integrable g μ hμ k.2.1 f.2.1 k.2.2).aestronglyMeasurable.restrict
  rw [lebesgueC_eq_volume] at htransport
  have hpoint {z : ComplexVector n} (hz : z ∈ chartTarget x) :
      (1 / 2 : ℝ) * (Real.sqrt (realMetricFn g.form x z).det *
        scalarGradientPair g.form k f (chartInv x z)) =
      ∑ i, ∑ j, rDeriv (inChart x f) z j * scalarChartTestFluxEntry g x η i j z := by
    rw [scalarGradientPair_eq_chart g.form k.2.1 f.2.1 x hz, chartGradientPair_eq_sum]
    simp only [scalarChartTestFluxEntry, rDeriv, hdiff hz, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [scalarEnergyPair_symm g μ f k]
  unfold scalarEnergyPair
  rw [hsource, htransport, ← integral_const_mul]
  have hrestrict : (∫ z in O, ∑ i, ∑ j,
      rDeriv (inChart x f) z j * scalarChartTestFluxEntry g x η i j z) =
      ∫ z in chartTarget x, ∑ i, ∑ j,
        rDeriv (inChart x f) z j * scalarChartTestFluxEntry g x η i j z := by
    symm
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
      (isOpen_extChartAt_target (I := ComplexModel n) x).measurableSet hOt
    intro z hz
    have hηD (i : RIdx n) : rDeriv η z i = 0 :=
      image_eq_zero_of_notMem_tsupport (f := fun w => rDeriv η w i) (fun hh => hz.2
        (hηO ((tsupport_fderiv_apply_subset ℝ (realVec i)) hh)))
    simp only [scalarChartTestFluxEntry, hηD, zero_mul, mul_zero, Finset.sum_const_zero]
  rw [hrestrict]
  apply setIntegral_congr_fun (isOpen_extChartAt_target (I := ComplexModel n) x).measurableSet
  intro z hz
  exact hpoint hz

/-- The computed flux entry, as an actual local scalar L² element. -/
def scalarChartTestFluxEntryLp (g : SmoothMetric M) (x : M.Carrier)
    (O : Set (ComplexVector n)) {η : ComplexVector n → ℝ}
    (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η)
    (hηt : tsupport η ⊆ chartTarget x) (i j : RIdx n) : Lp ℝ 2 (volume.restrict O) :=
  ((scalarChartTestFluxEntry_memLp g x hη hcη hηt i j).mono_measure
    Measure.restrict_le_self).toLp _

theorem scalarChartTestFluxEntryLp_coe (g : SmoothMetric M) (x : M.Carrier)
    (O : Set (ComplexVector n)) {η : ComplexVector n → ℝ}
    (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η)
    (hηt : tsupport η ⊆ chartTarget x) (i j : RIdx n) :
    scalarChartTestFluxEntryLp g x O hη hcη hηt i j =ᵐ[volume.restrict O]
      scalarChartTestFluxEntry g x η i j :=
  ((scalarChartTestFluxEntry_memLp g x hη hcη hηt i j).mono_measure
    Measure.restrict_le_self).coeFn_toLp

/-- The finite chart flux pairing is a continuous L² pairing, with all
product integrability justified by the actual L² classes. -/
theorem scalarEnergy_chartFlux_integral (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (x : M.Carrier)
    {O : Set (ComplexVector n)} (hO : IsOpen O) (hOc : IsCompact (closure O))
    (hOt : closure O ⊆ chartTarget x) (v : ScalarEnergySpace g μ hμ)
    {η : ComplexVector n → ℝ} (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η)
    (hηt : tsupport η ⊆ chartTarget x) :
    (∑ i, ∑ j, inner ℝ (scalarEnergy_chartDerivativeCLM g μ hμ x hO hOc hOt j v)
      (scalarChartTestFluxEntryLp g x O hη hcη hηt i j)) =
      ∫ z in O, ∑ i, ∑ j, scalarEnergy_chartDerivativeCLM g μ hμ x hO hOc hOt j v z *
        scalarChartTestFluxEntry g x η i j z := by
  let D := fun j => scalarEnergy_chartDerivativeCLM g μ hμ x hO hOc hOt j v
  have hi (i j : RIdx n) : Integrable (fun z => D j z * scalarChartTestFluxEntry g x η i j z)
      (volume.restrict O) :=
    (Lp.memLp (D j)).integrable_mul
      ((scalarChartTestFluxEntry_memLp g x hη hcη hηt i j).mono_measure Measure.restrict_le_self)
  have hp (i j : RIdx n) : inner ℝ (D j) (scalarChartTestFluxEntryLp g x O hη hcη hηt i j) =
      ∫ z in O, D j z * scalarChartTestFluxEntry g x η i j z := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [scalarChartTestFluxEntryLp_coe g x O hη hcη hηt i j] with z hz
    rw [hz]
    simp only [RCLike.inner_apply, conj_trivial, mul_comm]
  change (∑ i, ∑ j, inner ℝ (D j) _) = _
  simp_rw [hp]
  rw [integral_finsetSum Finset.univ (fun i _ =>
    integrable_finsetSum Finset.univ (fun j _ => hi i j))]
  apply Finset.sum_congr rfl
  intro i _
  exact (integral_finsetSum Finset.univ (fun j _ => hi i j)).symm

/-- The genuine closed scalar energy evaluated against a genuine chart
pushforward test is its density-weighted chart gradient pairing. -/
theorem scalarClosedEnergy_chartTest (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (x : M.Carrier)
    {O : Set (ComplexVector n)} (hO : IsOpen O) (hOc : IsCompact (closure O))
    (hOt : closure O ⊆ chartTarget x) (v : ScalarEnergySpace g μ hμ)
    {η : ComplexVector n → ℝ} (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η)
    (hηO : tsupport η ⊆ O) :
    scalarClosedEnergy g μ hμ v
      (scalarEnergy_chartTest g μ hμ x hη hcη (hηO.trans (subset_closure.trans hOt)) :
        ScalarEnergySpace g μ hμ) =
      ∫ z in O, Real.sqrt (realMetricFn g.form x z).det *
        ∑ i, ∑ j, ((1 / 2 : ℝ) * (realMetricFn g.form x z)⁻¹ i j) *
          scalarEnergy_chartDerivativeCLM g μ hμ x hO hOc hOt j v z * rDeriv η z i := by
  let k := scalarEnergy_chartTest g μ hμ x hη hcη (hηO.trans (subset_closure.trans hOt))
  let D := fun j => scalarEnergy_chartDerivativeCLM g μ hμ x hO hOc hOt j
  let F := fun i j => scalarChartTestFluxEntryLp g x O hη hcη
    (hηO.trans (subset_closure.trans hOt)) i j
  have hpair : ∀ w : ScalarEnergySpace g μ hμ,
      scalarClosedEnergy g μ hμ w (k : ScalarEnergySpace g μ hμ) =
        ∑ i, ∑ j, inner ℝ (D j w) (F i j) := by
    intro w
    refine UniformSpace.Completion.induction_on w (p := fun w : ScalarEnergySpace g μ hμ =>
      scalarClosedEnergy g μ hμ w (k : ScalarEnergySpace g μ hμ) =
        ∑ i, ∑ j, inner ℝ (D j w) (F i j)) ?_ ?_
    · apply isClosed_eq
      · exact (continuous_id.inner continuous_const).sub
          ((scalarEnergyL2 g μ hμ).continuous.inner continuous_const)
      · exact continuous_finsetSum Finset.univ (fun i _ =>
          continuous_finsetSum Finset.univ (fun j _ => (D j).continuous.inner continuous_const))
    · intro f
      rw [scalarClosedEnergy_coe]
      rw [scalarEnergy_chartFlux_integral g μ hμ x hO hOc hOt _ hη hcη
        (hηO.trans (subset_closure.trans hOt))]
      rw [scalarEnergy_core_chartTest g μ hμ x hO (subset_closure.trans hOt) f hη hcη hηO]
      apply integral_congr_ae
      have ha : ∀ᵐ z ∂volume.restrict O, ∀ j : RIdx n,
          D j (f : ScalarEnergySpace g μ hμ) z = rDeriv (inChart x f) z j :=
        ae_all_iff.mpr (fun j => scalarEnergy_chartDerivativeCLM_coe g μ hμ x hO hOc hOt j f)
      filter_upwards [ha] with z hz
      simp only [D] at *
      simp_rw [hz]
  rw [hpair v, scalarEnergy_chartFlux_integral g μ hμ x hO hOc hOt v hη hcη
    (hηO.trans (subset_closure.trans hOt))]
  apply integral_congr_ae
  apply ae_of_all
  intro z
  simp only [scalarChartTestFluxEntry, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

end Yau.LeafProofs.L19Aux
