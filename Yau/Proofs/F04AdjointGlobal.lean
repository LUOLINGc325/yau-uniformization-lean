import Yau.Proofs.F04AdjointLocal

/-!
Global compact-test Green identity for an arbitrary smooth Kähler field.
The initial complete metric is used only to select a compact cutoff; the
metric in the Laplacian and volume has no completeness premise.
-/

open scoped Manifold Topology ContDiff Matrix ComplexOrder
open MeasureTheory Filter

noncomputable section
set_option maxHeartbeats 1000000

namespace Yau.F04Proof.Adjoint

open Yau.LeafProofs.L18Aux

variable {n : ℕ} {M : ComplexManifold n}

theorem volumeDensity_continuousOn (g : HermitianField M) (hg : MetricSmooth g)
    (x : M.Carrier) :
    ContinuousOn (fun z => Real.sqrt (realMetricFn g x z).det) (chartTarget x) :=
  (volumeDensity_contDiffOn g hg x).continuousOn

theorem riemannianVolume_locallyFinite {n : ℕ} {M : ComplexManifold n}
    (g : HermitianField M) (hg : MetricSmooth g) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g μ) : IsLocallyFiniteMeasure μ := by
  constructor
  intro x
  let d : ComplexVector n → ℝ := fun z => Real.sqrt (realMetricFn g x z).det
  let z₀ : ComplexVector n := chartPt x x
  let B : ℝ := d z₀ + 1
  have hz₀ : z₀ ∈ chartTarget x := mem_extChartAt_target x
  have htarget : chartTarget x ∈ 𝓝 z₀ :=
    (isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz₀
  have hd : ContinuousAt d z₀ :=
    (volumeDensity_continuousOn g hg x).continuousAt htarget
  have hB : {z | d z < B} ∈ 𝓝 z₀ :=
    hd.preimage_mem_nhds (Iio_mem_nhds (by dsimp [B]; linarith))
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (inter_mem htarget hB)
  let s : Set M.Carrier := (extChartAt (ComplexModel n) x).source ∩
    chartPt x ⁻¹' Metric.ball z₀ ε
  have hs : IsOpen s :=
    isOpen_extChartAt_preimage' (I := ComplexModel n) x Metric.isOpen_ball
  have hxs : x ∈ s := ⟨mem_extChartAt_source x, Metric.mem_ball_self hε⟩
  refine ⟨s, hs.mem_nhds hxs, ?_⟩
  have hsource : s ⊆ (chartAt (ComplexVector n) x).source := by
    intro y hy
    simpa only [extChartAt_source] using hy.1
  rw [hμ x s hs.measurableSet hsource]
  have himage : chartPt x '' s ⊆ Metric.ball z₀ ε := by
    rintro z ⟨y, hy, rfl⟩
    exact hy.2
  have hmass : lebesgueC n (Metric.closedBall z₀ ε) < ⊤ := by
    rw [LeafProofs.lebesgueC_eq_volume]
    exact (isCompact_closedBall z₀ ε).measure_lt_top
  calc
    ∫⁻ z in chartPt x '' s, ENNReal.ofReal (d z) ∂lebesgueC n
        ≤ ∫⁻ z in chartPt x '' s, ENNReal.ofReal B ∂lebesgueC n :=
      setLIntegral_mono measurable_const fun z hz =>
        ENNReal.ofReal_le_ofReal (hball (himage hz)).2.le
    _ = ENNReal.ofReal B * lebesgueC n (chartPt x '' s) := by simp
    _ ≤ ENNReal.ofReal B * lebesgueC n (Metric.closedBall z₀ ε) :=
      mul_le_mul_right (measure_mono
        (himage.trans Metric.ball_subset_closedBall)) (ENNReal.ofReal B)
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hmass

theorem integral_chart_volume (g : HermitianField M) (hg : MetricSmooth g) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g μ) (a : M.Carrier)
    (f : M.Carrier → ℝ) (hf : Measurable f) :
    ∫ y in (extChartAt (ComplexModel n) a).source, f y ∂μ =
      ∫ z in chartTarget a, Real.sqrt (realMetricFn g a z).det *
        f (chartInv a z) ∂lebesgueC n := by
  have ht : MeasurableSet (chartTarget a) :=
    (isOpen_extChartAt_target (I := ComplexModel n) a).measurableSet
  have hd : AEMeasurable (fun z => ENNReal.ofReal (Real.sqrt (realMetricFn g a z).det))
      ((lebesgueC n).restrict (chartTarget a)) :=
    ENNReal.measurable_ofReal.comp_aemeasurable ((volumeDensity_continuousOn g hg a).aemeasurable ht)
  rw [riemannianVolume_restrict_eq_map g μ hμ a,
    integral_map (chartInvExtension_measurable a).aemeasurable hf.aestronglyMeasurable,
    integral_withDensity_eq_integral_toReal_smul₀ hd
      (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  apply setIntegral_congr_fun ht
  intro z hz
  simp only [chartInvExtension, ite_eq_left hz, ENNReal.toReal_ofReal (Real.sqrt_nonneg _), smul_eq_mul]

theorem smoothFn_laplacian {n : ℕ} {M : ComplexManifold n}
    (g : HermitianField M) (hg : MetricSmooth g) {u : M.Carrier → ℝ} (hu : SmoothFn u) :
    SmoothFn (laplacian g u) := by
  intro x
  have hO := isOpen_extChartAt_target (I := ComplexModel n) x
  have hdu : ContDiffOn ℝ ∞ (fderiv ℝ (inChart x u)) (chartTarget x) :=
    (hu x).fderiv_of_isOpen hO (by simp)
  have hddu : ContDiffOn ℝ ∞ (fderiv ℝ (fderiv ℝ (inChart x u))) (chartTarget x) :=
    hdu.fderiv_of_isOpen hO (by simp)
  have hp : ContDiffOn ℝ ∞ (fun z => (1 / 2 : ℝ) * ∑ a, ∑ b,
      (realMetricFn g x z)⁻¹ a b *
        fderiv ℝ (fderiv ℝ (inChart x u)) z (realVec a) (realVec b)) (chartTarget x) := by
    apply contDiffOn_const.mul
    apply ContDiffOn.sum
    intro a _
    apply ContDiffOn.sum
    intro b _
    exact (realMetricFn_inverse_contDiffOn g hg x a b).mul
      ((hddu.clm_apply contDiffOn_const).clm_apply contDiffOn_const)
  apply hp.congr
  intro z hz
  symm
  have hf : ContDiffAt ℝ 2 (inChart x u) z :=
    ((hu x).contDiffAt (hO.mem_nhds hz)).of_le (by simp)
  change (1 / 2 : ℝ) * (∑ a, ∑ b, (realMetricFn g x z)⁻¹ a b *
    fderiv ℝ (fderiv ℝ (inChart x u)) z (realVec a) (realVec b)) = laplacian g u (chartInv x z)
  rw [principal_realLaplacian_eq_twice_traceWith g x hz hf,
    traceWith_inChart_eq_laplacian g hu x hz]
  ring

theorem smoothFn_scalarGradientPair {n : ℕ} {M : ComplexManifold n}
    (g : HermitianField M) (hg : MetricSmooth g) {u v : M.Carrier → ℝ} (hu : SmoothFn u) (hv : SmoothFn v) :
    SmoothFn (scalarGradientPair g u v) := by
  have hp := smoothFn_sub
    (smoothFn_sub (smoothFn_laplacian g hg (smoothFn_mul hu hv))
      (smoothFn_mul hu (smoothFn_laplacian g hg hv)))
    (smoothFn_mul hv (smoothFn_laplacian g hg hu))
  have heq : scalarGradientPair g u v =
      (fun y => laplacian g (fun x => u x * v x) y -
        u y * laplacian g v y - v y * laplacian g u y) :=
    funext (scalarGradientPair_laplacian_identity g hu hv)
  rw [heq]
  exact hp

theorem smoothFn_integrable_compact {n : ℕ} {M : ComplexManifold n}
    (g : HermitianField M) (hg : MetricSmooth g) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g μ)
    {u : M.Carrier → ℝ} (hu : SmoothFn u) (hcu : HasCompactSupport u) : Integrable u μ := by
  let _ : IsLocallyFiniteMeasure μ := riemannianVolume_locallyFinite g hg μ hμ
  exact (continuous_of_smoothFn hu).integrable_of_hasCompactSupport hcu

theorem scalarGradientPair_integrable {n : ℕ} {M : ComplexManifold n}
    (g : HermitianField M) (hg : MetricSmooth g) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g μ)
    {u v : M.Carrier → ℝ} (hu : SmoothFn u) (hv : SmoothFn v) (hcu : HasCompactSupport u) :
    Integrable (scalarGradientPair g u v) μ :=
  smoothFn_integrable_compact g hg μ hμ (smoothFn_scalarGradientPair g hg hu hv)
    (scalarGradientPair_hasCompactSupport g u v hcu)

theorem integral_chart_volume_of_tsupport {n : ℕ} {M : ComplexManifold n}
    (g : HermitianField M) (hg : MetricSmooth g) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g μ)
    (x : M.Carrier) (f : M.Carrier → ℝ) (hf : Measurable f)
    (hfs : tsupport f ⊆ (extChartAt (ComplexModel n) x).source) :
    (∫ y, f y ∂μ) = ∫ z, Real.sqrt (realMetricFn g x z).det * chartPullbackZero x f z ∂lebesgueC n := by
  have hs : (∫ y in (extChartAt (ComplexModel n) x).source, f y ∂μ) = ∫ y, f y ∂μ :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy =>
      image_eq_zero_of_notMem_tsupport (fun h => hy (hfs h))
  calc
    (∫ y, f y ∂μ) = ∫ y in (extChartAt (ComplexModel n) x).source, f y ∂μ := hs.symm
    _ = ∫ z in chartTarget x, Real.sqrt (realMetricFn g x z).det * f (chartInv x z) ∂lebesgueC n :=
      integral_chart_volume g hg μ hμ x f hf
    _ = ∫ z in chartTarget x, Real.sqrt (realMetricFn g x z).det * chartPullbackZero x f z ∂lebesgueC n := by
      apply setIntegral_congr_fun (isOpen_extChartAt_target (I := ComplexModel n) x).measurableSet
      intro z hz
      have hzt : z ∈ chartTarget x := hz
      simp only [chartPullbackZero, ite_eq_left hzt]
    _ = ∫ z, Real.sqrt (realMetricFn g x z).det * chartPullbackZero x f z ∂lebesgueC n := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro z hz
      simp only [chartPullbackZero, ite_eq_right hz, mul_zero]

theorem integral_scalar_green_in_chart {n : ℕ} {M : ComplexManifold n}
    (g : HermitianField M) (hg : MetricSmooth g) (hK : KahlerClosed g) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g μ) {u ψ : M.Carrier → ℝ}
    (hu : SmoothFn u) (hψ : SmoothFn ψ) (hcψ : HasCompactSupport ψ)
    (x : M.Carrier) (hψs : tsupport ψ ⊆ (extChartAt (ComplexModel n) x).source) :
    Integrable (fun y => ψ y * laplacian g u y) μ ∧
      Integrable (scalarGradientPair g ψ u) μ ∧
        (∫ y, ψ y * laplacian g u y ∂μ) =
          -(1 / 2 : ℝ) * ∫ y, scalarGradientPair g ψ u y ∂μ := by
  let Φ := chartPullbackZero x ψ
  let ρ : ComplexVector n → ℝ := fun z => Real.sqrt (realMetricFn g x z).det
  have hΦ : HasCompactSupport Φ ∧ ContDiff ℝ ∞ Φ ∧ tsupport Φ ⊆ chartTarget x :=
    chartPullbackZero_smoothFn x hψ hcψ hψs
  have hcI : HasCompactSupport (fun y => ψ y * laplacian g u y) := hcψ.mul_right
  have hIint : Integrable (fun y => ψ y * laplacian g u y) μ :=
    smoothFn_integrable_compact g hg μ hμ (smoothFn_mul hψ (smoothFn_laplacian g hg hu)) hcI
  have hEint : Integrable (scalarGradientPair g ψ u) μ :=
    scalarGradientPair_integrable g hg μ hμ hψ hu hcψ
  have hI : (∫ y, ψ y * laplacian g u y ∂μ) =
      ∫ z, ρ z * Φ z * laplacian g u (chartInv x z) ∂lebesgueC n := by
    calc
      _ = ∫ z, ρ z * chartPullbackZero x (fun y => ψ y * laplacian g u y) z ∂lebesgueC n :=
        integral_chart_volume_of_tsupport g hg μ hμ x _
          (continuous_of_smoothFn (smoothFn_mul hψ (smoothFn_laplacian g hg hu))).measurable
          (tsupport_mul_subset_left.trans hψs)
      _ = _ := by
        apply integral_congr_ae
        exact ae_of_all _ (fun z => by
          change ρ z * chartPullbackZero x (fun y => ψ y * laplacian g u y) z =
            ρ z * Φ z * laplacian g u (chartInv x z)
          rw [chartPullbackZero_mul x ψ (laplacian g u) z]
          change ρ z * (Φ z * laplacian g u (chartInv x z)) =
            ρ z * Φ z * laplacian g u (chartInv x z)
          ring)
  have hE : (∫ y, scalarGradientPair g ψ u y ∂μ) =
      ∫ z, ρ z * chartGradientPair g x Φ (inChart x u) z ∂lebesgueC n := by
    calc
      _ = ∫ z, ρ z * chartPullbackZero x (scalarGradientPair g ψ u) z ∂lebesgueC n :=
        integral_chart_volume_of_tsupport g hg μ hμ x _
          (continuous_of_smoothFn (smoothFn_scalarGradientPair g hg hψ hu)).measurable
          ((scalarGradientPair_tsupport_subset_left g ψ u).trans hψs)
      _ = _ := by
        apply integral_congr_ae
        apply ae_of_all
        intro z
        change ρ z * chartPullbackZero x (scalarGradientPair g ψ u) z =
          ρ z * chartGradientPair g x Φ (inChart x u) z
        by_cases hz : z ∈ chartTarget x
        · have heval : chartPullbackZero x (scalarGradientPair g ψ u) z =
              scalarGradientPair g ψ u (chartInv x z) := by
            simp only [chartPullbackZero, ite_eq_left hz]
          rw [heval, scalarGradientPair_eq_chart g hψ hu x hz,
            chartGradientPair_pullbackZero g x ψ (inChart x u) hz]
        · have heval : chartPullbackZero x (scalarGradientPair g ψ u) z = 0 := by
            simp only [chartPullbackZero, ite_eq_right hz]
          have hnot : z ∉ tsupport Φ := fun h => hz (hΦ.2.2 h)
          have hzero := chartGradientPair_zero_of_notMem_tsupport g x Φ (inChart x u) hnot
          rw [heval, hzero]
  have hG := integral_kahler_laplacian g hg hK hu x (hΦ.2.1.of_le (by simp)) hΦ.1 hΦ.2.2
  have hLeft : (∫ z, Φ z * (2 * ρ z * laplacian g u (chartInv x z)) ∂lebesgueC n) =
      2 * ∫ y, ψ y * laplacian g u y ∂μ := by
    calc
      _ = ∫ z, 2 * (ρ z * Φ z * laplacian g u (chartInv x z)) ∂lebesgueC n := by
        apply integral_congr_ae
        exact ae_of_all _ (fun _ => by ring)
      _ = 2 * ∫ z, ρ z * Φ z * laplacian g u (chartInv x z) ∂lebesgueC n := integral_const_mul _ _
      _ = _ := congrArg (fun q => 2 * q) hI.symm
  have hRight : (∫ z, ∑ a, rDeriv Φ z a * scalarMetricFlux g x u a z ∂lebesgueC n) =
      ∫ y, scalarGradientPair g ψ u y ∂μ := by
    calc
      _ = ∫ z, ρ z * chartGradientPair g x Φ (inChart x u) z ∂lebesgueC n := by
        apply integral_congr_ae
        exact ae_of_all _ (fun z => scalarMetricFlux_pairing g x u Φ z)
      _ = _ := hE.symm
  change (∫ z, Φ z * (2 * ρ z * laplacian g u (chartInv x z)) ∂lebesgueC n) =
    -(∫ z, ∑ a, rDeriv Φ z a * scalarMetricFlux g x u a z ∂lebesgueC n) at hG
  rw [hLeft, hRight] at hG
  exact ⟨hIint, hEint, by linarith⟩

theorem integral_scalar_green {n : ℕ} {M : ComplexManifold n}
    (g : HermitianField M) (hg : MetricSmooth g) (hK : KahlerClosed g) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g μ) {u ψ : M.Carrier → ℝ}
    (hu : SmoothFn u) (hψ : SmoothFn ψ) (hcψ : HasCompactSupport ψ) :
    Integrable (fun y => ψ y * laplacian g u y) μ ∧
      Integrable (scalarGradientPair g ψ u) μ ∧
        (∫ y, ψ y * laplacian g u y ∂μ) =
          -(1 / 2 : ℝ) * ∫ y, scalarGradientPair g ψ u y ∂μ := by
  classical
  obtain ⟨s, p, hp, _, hps, hsum⟩ :=
    exists_finite_smooth_partition (show IsCompact (tsupport ψ) from hcψ)
  let η : s → M.Carrier → ℝ := fun i y => p i y * ψ y
  have hη (i : s) : SmoothFn (η i) := smoothFn_mul (hp i) hψ
  have hcη (i : s) : HasCompactSupport (η i) := hcψ.mul_left
  have hηs (i : s) : tsupport (η i) ⊆ (extChartAt (ComplexModel n) (i : M.Carrier)).source :=
    tsupport_mul_subset_left.trans (hps i)
  have hloc (i : s) := integral_scalar_green_in_chart g hg hK μ hμ hu (hη i) (hcη i)
    (i : M.Carrier) (hηs i)
  have hsumFn : (fun y => ∑ i, η i y) = ψ := by
    funext y
    change (∑ i, p i y * ψ y) = ψ y
    rw [← Finset.sum_mul]
    by_cases hzero : ψ y = 0
    · simp only [hzero, mul_zero]
    · rw [hsum y (subset_closure hzero), one_mul]
  have hpieces (i : s) : Integrable (fun y => p i y • (ψ y * laplacian g u y)) μ := by
    convert (hloc i).1 using 1
    funext y
    simp only [smul_eq_mul, η]
    ring
  have hsumI : ∀ y ∈ Function.support (fun y => ψ y * laplacian g u y), ∑ i, p i y = 1 := by
    intro y hy
    have hψnz : ψ y ≠ 0 := by
      intro hzero
      apply hy
      simp only [hzero, zero_mul]
    exact hsum y (subset_closure hψnz)
  have hIformal := integral_finite_partition μ p (fun y => ψ y * laplacian g u y) hpieces hsumI
  have hIeq : (∫ y, ψ y * laplacian g u y ∂μ) =
      ∑ i, ∫ y, η i y * laplacian g u y ∂μ := by
    calc
      _ = ∑ i, ∫ y, p i y • (ψ y * laplacian g u y) ∂μ := hIformal.2
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i _
        apply integral_congr_ae
        exact ae_of_all _ (fun y => by simp only [smul_eq_mul, η]; ring)
  have hsumE : (fun y => ∑ i, scalarGradientPair g (η i) u y) = scalarGradientPair g ψ u := by
    funext y
    rw [← scalarGradientPair_sum_left g η hη u y]
    exact congrArg (fun q : M.Carrier → ℝ => scalarGradientPair g q u y) hsumFn
  have hEeq : (∫ y, scalarGradientPair g ψ u y ∂μ) =
      ∑ i, ∫ y, scalarGradientPair g (η i) u y ∂μ := by
    calc
      _ = ∫ y, ∑ i, scalarGradientPair g (η i) u y ∂μ :=
        congrArg (fun q : M.Carrier → ℝ => ∫ y, q y ∂μ) hsumE.symm
      _ = _ := integral_finsetSum Finset.univ (fun i _ => (hloc i).2.1)
  refine ⟨hIformal.1, scalarGradientPair_integrable g hg μ hμ hψ hu hcψ, ?_⟩
  calc
    _ = ∑ i, ∫ y, η i y * laplacian g u y ∂μ := hIeq
    _ = ∑ i, (-(1 / 2 : ℝ)) * ∫ y, scalarGradientPair g (η i) u y ∂μ := by
      apply Finset.sum_congr rfl
      intro i _
      exact (hloc i).2.2
    _ = (-(1 / 2 : ℝ)) * ∑ i, ∫ y, scalarGradientPair g (η i) u y ∂μ :=
      (Finset.mul_sum _ _ _).symm
    _ = _ := congrArg (fun q => (-(1 / 2 : ℝ)) * q) hEeq.symm

end Yau.F04Proof.Adjoint
