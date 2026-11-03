import Yau.LeafProofs.L18Moser
import Yau.LeafProofs.L18MeanValueAssembly
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! The actual ball Poincaré inequality and its scalar Sobolev consequence. -/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold ENNReal ComplexOrder

namespace Yau.LeafProofs.L18Aux

/-- The uniform L¹ Poincaré estimate on actual concentric distance balls,
with the original metric energy and the given Riemannian volume measure. -/
def BallScalarPoincareEstimate (n : ℕ) (C : ℝ) : Prop :=
  ∀ (M : ComplexManifold n) (g : SmoothMetric M),
    IsComplete g → IsKahler g → (∀ x, (ricci g.form x).PosSemidef) →
    ∀ (μ : Measure M.Carrier), IsRiemannianVolume g.form μ →
    ∀ (v : M.Carrier → ℝ), SmoothFn v → ∀ (x : M.Carrier) (r : ℝ), 0 < r →
      (∫ y in distBall g.form x r,
        |v y - (μ.real (distBall g.form x r))⁻¹ *
          ∫ z in distBall g.form x r, v z ∂μ| ∂μ) ≤
        C * r * ∫ y in distBall g.form x (3 * r),
          Real.sqrt (scalarGradientPair g.form v v y) ∂μ

private theorem ball_real_pos {n : ℕ} {M : ComplexManifold n}
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (x : M.Carrier) {r : ℝ} (hr : 0 < r) : 0 < μ.real (distBall g.form x r) :=
  ENNReal.toReal_pos (riemannianVolume_distBall_pos g μ hμ x hr).ne'
    (riemannianVolume_distBall_lt_top g μ hμ x hr).ne

private theorem ball_real_comparison {n : ℕ} {M : ComplexManifold n}
    (g : SmoothMetric M) (hc : IsComplete g) (hK : IsKahler g)
    (hRic : ∀ x, (ricci g.form x).PosSemidef)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (x : M.Carrier) {r R : ℝ} (hr : 0 < r) (hrR : r ≤ R) :
    μ.real (distBall g.form x R) ≤ (R / r) ^ (2 * n) *
      μ.real (distBall g.form x r) := by
  have hb := Yau.LeafProofs.L12 n M g hc hK hRic μ hμ x r R hr hrR
  have ht : ENNReal.ofReal ((R / r) ^ (2 * n)) * μ (distBall g.form x r) ≠ ⊤ :=
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (riemannianVolume_distBall_lt_top g μ hμ x hr)).ne
  have hb' := ENNReal.toReal_mono ht hb
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal
    (pow_nonneg (div_nonneg (hr.trans_le hrR).le hr.le) _), Measure.real_def] using hb'

private theorem centered_ball_subset {n : ℕ} {M : ComplexManifold n}
    (g : SmoothMetric M) (o y : M.Carrier) {R : ℝ} (hR : 0 < R)
    (hy : y ∈ distBall g.form o R) :
    distBall g.form o R ⊆ distBall g.form y (3 * R) := by
  intro z hz
  apply (L12Aux.mem_distBall_iff g y z (by positivity)).mpr
  have hyo : inducedDistance g.form y o < R := by
    rw [g.induced_distance_symm]
    exact (L12Aux.mem_distBall_iff g o y hR).mp hy
  have hzo := (L12Aux.mem_distBall_iff g o z hR).mp hz
  linarith [g.induced_distance_triangle y o z]

private theorem gradient_norm_integrable {n : ℕ} {M : ComplexManifold n}
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    {v : M.Carrier → ℝ} (hv : SmoothFn v) (hcv : HasCompactSupport v) :
    Integrable (fun y => Real.sqrt (scalarGradientPair g.form v v y)) μ := by
  let : IsLocallyFiniteMeasure μ := riemannianVolume_locallyFinite g μ hμ
  apply (Real.continuous_sqrt.comp
    (continuous_of_smoothFn (smoothFn_scalarGradientPair g hv hv))).integrable_of_hasCompactSupport
  exact (scalarGradientPair_hasCompactSupport g.form v v hcv).comp_left (by simp)

private theorem sqrt_integral_ball_le {n : ℕ} {M : ComplexManifold n}
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    {v : M.Carrier → ℝ} (hv : SmoothFn v) (hcv : HasCompactSupport v)
    (x : M.Carrier) (r : ℝ) :
    (∫ y in distBall g.form x r, Real.sqrt (scalarGradientPair g.form v v y) ∂μ) ≤
      ∫ y, Real.sqrt (scalarGradientPair g.form v v y) ∂μ :=
  setIntegral_le_integral (gradient_norm_integrable g μ hμ hv hcv)
    (Eventually.of_forall (fun y => Real.sqrt_nonneg _))

private theorem half_pow_cancel (k : ℕ) :
    (2 : ℝ) ^ k * (1 / 2 : ℝ) ^ k = 1 := by rw [← mul_pow]; norm_num

/-- The potential bound at a point whose local gradient averages are all
bounded. The only analytic input is the displayed original-ball Poincaré
estimate; convergence of the genuine averages removes the terminal value. -/
private theorem normalized_poincare_potential {n : ℕ} {C θ : ℝ}
    (hC : 0 ≤ C) (hPI : BallScalarPoincareEstimate n C)
    (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hgain : (1 / 2 : ℝ) * ((2 : ℝ) ^ (2 * n)) ^ (1 - θ) < 1)
    {M : ComplexManifold n} (g : SmoothMetric M)
    (hc : IsComplete g) (hK : IsKahler g) (hRic : ∀ x, (ricci g.form x).PosSemidef)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    {v : M.Carrier → ℝ} (hv : SmoothFn v) (hcv : HasCompactSupport v)
    (hv0 : ∀ z, 0 ≤ v z) (o y : M.Carrier) {R t : ℝ} (hR : 0 < R) (ht : 0 < t)
    (hy : y ∈ distBall g.form o R)
    (hI : (∫ z, v z ∂μ) ≤ μ.real (distBall g.form o R))
    (hJ : (∫ z, Real.sqrt (scalarGradientPair g.form v v z) ∂μ) ≤
      μ.real (distBall g.form o R) / R)
    (hlocal : ∀ ρ : ℝ, 0 < ρ → ρ ≤ 3 * R →
      (∫ z in distBall g.form y ρ, Real.sqrt (scalarGradientPair g.form v v z) ∂μ) ≤
        t * μ.real (distBall g.form y ρ)) :
    v y ≤ (3 : ℝ) ^ (2 * n) +
      (C * (6 : ℝ) ^ (2 * n) /
        (1 - (1 / 2 : ℝ) * ((2 : ℝ) ^ (2 * n)) ^ (1 - θ))) * (R * t) ^ θ := by
  let r : ℕ → ℝ := fun k => R * (1 / 2 : ℝ) ^ k
  let s : ℕ → ℝ := fun k => (μ.real (distBall g.form y (r k)))⁻¹ *
    ∫ z in distBall g.form y (r k), v z ∂μ
  let b : ℕ → ℝ := fun k => (μ.real (distBall g.form y (3 * r k)))⁻¹ *
    ∫ z in distBall g.form y (3 * r k), Real.sqrt (scalarGradientPair g.form v v z) ∂μ
  let V := μ.real (distBall g.form o R)
  have hV : 0 < V := ball_real_pos g μ hμ o hR
  have hr (k : ℕ) : 0 < r k := by dsimp [r]; positivity
  have hrle (k : ℕ) : r k ≤ R := by
    dsimp [r]
    exact mul_le_of_le_one_right hR.le (pow_le_one₀ (by norm_num) (by norm_num))
  have hstep (k : ℕ) : r (k + 1) = r k / 2 := by dsimp [r]; rw [pow_succ]; ring
  have hW (k : ℕ) : 0 < μ.real (distBall g.form y (3 * r k)) :=
    ball_real_pos g μ hμ y (by positivity)
  have hb0 (k : ℕ) : 0 ≤ b k := by dsimp [b]; positivity
  have hbM (k : ℕ) : b k ≤ t := by
    have h := hlocal (3 * r k) (by positivity) (by nlinarith [hrle k])
    dsimp only [b]
    calc
      _ ≤ (μ.real (distBall g.form y (3 * r k)))⁻¹ *
          (t * μ.real (distBall g.form y (3 * r k))) :=
        mul_le_mul_of_nonneg_left h (inv_nonneg.mpr (hW k).le)
      _ = t := by field_simp [(hW k).ne']
  have hbaseVolume : V ≤ μ.real (distBall g.form y (3 * R)) :=
    measureReal_mono (centered_ball_subset g o y hR hy)
      (riemannianVolume_distBall_lt_top g μ hμ y (by positivity)).ne
  have hbA (k : ℕ) : b k ≤ (1 / R) * ((2 : ℝ) ^ (2 * n)) ^ k := by
    have hratio : (3 * R) / (3 * r k) = (2 : ℝ) ^ k := by
      apply (div_eq_iff (by positivity : 3 * r k ≠ 0)).mpr
      symm
      dsimp [r]
      calc
        _ = 3 * R * ((2 : ℝ) ^ k * (1 / 2 : ℝ) ^ k) := by ring
        _ = 3 * R := by rw [half_pow_cancel, mul_one]
    have hvol := ball_real_comparison g hc hK hRic μ hμ y (R := 3 * R)
      (by positivity : 0 < 3 * r k) (by nlinarith [hrle k])
    rw [hratio, pow_right_comm] at hvol
    have hvol' : V ≤ ((2 : ℝ) ^ (2 * n)) ^ k *
        μ.real (distBall g.form y (3 * r k)) := hbaseVolume.trans hvol
    have hInt := (sqrt_integral_ball_le g μ hμ hv hcv y (3 * r k)).trans hJ
    dsimp only [b]
    rw [← div_eq_inv_mul]
    apply (div_le_iff₀ (hW k)).mpr
    calc
      _ ≤ V / R := hInt
      _ ≤ (((2 : ℝ) ^ (2 * n)) ^ k * μ.real (distBall g.form y (3 * r k))) / R :=
        div_le_div_of_nonneg_right hvol' hR.le
      _ = _ := by ring
  have hdiff (k : ℕ) : |s (k + 1) - s k| ≤
      (C * (6 : ℝ) ^ (2 * n) * R) * (1 / 2 : ℝ) ^ k * b k := by
    have hp := abs_distBall_nested_averages_le_oscillation g μ hμ hv y (R := r k)
      (hr (k + 1)) (by rw [hstep]; linarith [hr k])
    have hP := hPI M g hc hK hRic μ hμ v hv y (r k) (hr k)
    have hwpos := ball_real_pos g μ hμ y (hr (k + 1))
    have hratio : (3 * r k) / r (k + 1) = 6 := by
      rw [hstep]
      field_simp [(hr k).ne']
      norm_num
    have hw := ball_real_comparison g hc hK hRic μ hμ y (R := 3 * r k)
      (hr (k + 1)) (by rw [hstep]; linarith [hr k])
    rw [hratio] at hw
    have hw' : μ.real (distBall g.form y (3 * r k)) /
        μ.real (distBall g.form y (r (k + 1))) ≤ (6 : ℝ) ^ (2 * n) :=
      (div_le_iff₀ hwpos).mpr hw
    have hbId : (∫ z in distBall g.form y (3 * r k),
        Real.sqrt (scalarGradientPair g.form v v z) ∂μ) =
        μ.real (distBall g.form y (3 * r k)) * b k := by
      dsimp [b]
      field_simp [(hW k).ne']
    calc
      _ ≤ (μ.real (distBall g.form y (r (k + 1))))⁻¹ *
          (C * r k * ∫ z in distBall g.form y (3 * r k),
            Real.sqrt (scalarGradientPair g.form v v z) ∂μ) :=
        hp.trans (mul_le_mul_of_nonneg_left hP (inv_nonneg.mpr hwpos.le))
      _ = C * r k * (μ.real (distBall g.form y (3 * r k)) /
          μ.real (distBall g.form y (r (k + 1)))) * b k := by rw [hbId]; ring
      _ ≤ C * r k * (6 : ℝ) ^ (2 * n) * b k := by gcongr
      _ = _ := by dsimp [r]; ring
  have hlim : Tendsto s atTop (𝓝 (v y)) := by
    apply distBall_average_tendsto g μ hμ hv y hr
    simpa only [r, mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1)).const_mul R
  have hpot := interpolated_geometric_telescoping_bound (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by positivity : (0 : ℝ) ≤ 2 ^ (2 * n)) hθ0.le hθ1.le hgain
    (by positivity : 0 ≤ C * (6 : ℝ) ^ (2 * n) * R) ht.le
    (by positivity : 0 ≤ 1 / R) s b hb0 hbM hbA hdiff hlim
  have hS0 : s 0 ≤ (3 : ℝ) ^ (2 * n) := by
    have hvInt := (setIntegral_le_integral (smoothFn_integrable_compact g μ hμ hv hcv)
      (ae_of_all _ hv0) (s := distBall g.form y R)).trans hI
    have hvol := ball_real_comparison g hc hK hRic μ hμ y hR
      (by linarith : R ≤ 3 * R)
    have hrat : (3 * R) / R = (3 : ℝ) := by field_simp
    rw [hrat] at hvol
    have hvol' := hbaseVolume.trans hvol
    have hW0 := ball_real_pos g μ hμ y hR
    dsimp only [s, r]
    simp only [pow_zero, mul_one]
    rw [← div_eq_inv_mul]
    apply (div_le_iff₀ hW0).mpr
    exact hvInt.trans hvol'
  have hden : 0 < 1 - (1 / 2 : ℝ) * ((2 : ℝ) ^ (2 * n)) ^ (1 - θ) :=
    sub_pos.mpr hgain
  have hpower : R * t ^ θ * (1 / R) ^ (1 - θ) = (R * t) ^ θ := by
    rw [Real.div_rpow zero_le_one hR.le, Real.one_rpow,
      Real.rpow_sub hR, Real.rpow_one, Real.mul_rpow hR.le ht.le]
    field_simp
  have hpot' : |v y - s 0| ≤
      (C * (6 : ℝ) ^ (2 * n) /
        (1 - (1 / 2 : ℝ) * ((2 : ℝ) ^ (2 * n)) ^ (1 - θ))) * (R * t) ^ θ := by
    convert hpot using 1
    rw [← hpower]
    ring
  linarith [le_abs_self (v y - s 0)]

/-- A polynomial distribution bound gives every strictly smaller moment.
Only the scalar itself is measurable; no maximal function is introduced. -/
private theorem exists_moment_bound_of_polynomial_tails {p q K : ℝ}
    (hq : 1 < q) (hqp : q < p) (hK : 0 ≤ K) :
    ∃ L : ℝ, 0 < L ∧ ∀ {X : Type*} [MeasurableSpace X]
      (μ : Measure X) [IsFiniteMeasure μ] (f : X → ℝ),
      (∀ x, 0 ≤ f x) → Measurable f →
      (∀ t : ℝ, 1 ≤ t → μ {x | t < f x} ≤
        ENNReal.ofReal (K * t ^ (-p)) * μ univ) →
      (∫⁻ x, ENNReal.ofReal (f x ^ q) ∂μ) ≤ ENNReal.ofReal L * μ univ := by
  let H : ℝ := ∫ t : ℝ in Ioi 1, t ^ (q - p - 1)
  have hH : 0 ≤ H := setIntegral_nonneg measurableSet_Ioi
    (fun t ht => Real.rpow_nonneg (zero_lt_one.trans ht).le _)
  refine ⟨q * (1 + K * H), by positivity, ?_⟩
  intro X _ μ _ f hf0 hfm htail
  have hHfinite : IntegrableOn (fun t : ℝ => t ^ (q - p - 1)) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one
  have hHigh : (∫⁻ t : ℝ in Ioi 1, μ {x | t < f x} *
      ENNReal.ofReal (t ^ (q - 1))) ≤
      ENNReal.ofReal (K * H) * μ univ := by
    calc
      _ ≤ ∫⁻ t : ℝ in Ioi 1,
          ENNReal.ofReal (K * t ^ (q - p - 1)) * μ univ := by
        apply setLIntegral_mono' measurableSet_Ioi
        intro t ht
        calc
          _ ≤ (ENNReal.ofReal (K * t ^ (-p)) * μ univ) *
              ENNReal.ofReal (t ^ (q - 1)) := mul_le_mul' (htail t ht.le) le_rfl
          _ = _ := by
            rw [mul_right_comm, ← ENNReal.ofReal_mul
              (mul_nonneg hK (Real.rpow_nonneg (zero_lt_one.trans ht).le _))]
            congr 2
            rw [mul_assoc, ← Real.rpow_add (zero_lt_one.trans ht)]
            congr 1
            ring
      _ = ENNReal.ofReal (K * H) * μ univ := by
        rw [lintegral_mul_const' _ _ (measure_ne_top μ univ)]
        rw [← ofReal_integral_eq_lintegral_ofReal (hHfinite.const_mul K)
          (ae_restrict_of_forall_mem measurableSet_Ioi
            (fun t ht => mul_nonneg hK (Real.rpow_nonneg (zero_lt_one.trans ht).le _)))]
        rw [integral_const_mul]
  have hLow : (∫⁻ t : ℝ in Ioc 0 1, μ {x | t < f x} *
      ENNReal.ofReal (t ^ (q - 1))) ≤ μ univ := by
    calc
      _ ≤ ∫⁻ _t : ℝ in Ioc 0 1, μ univ := by
        apply setLIntegral_mono' measurableSet_Ioc
        intro t ht
        have hp : t ^ (q - 1) ≤ 1 :=
          Real.rpow_le_one ht.1.le ht.2 (by linarith)
        calc
          _ ≤ μ univ * 1 := mul_le_mul' (measure_mono (subset_univ _))
            (by simpa using ENNReal.ofReal_le_ofReal hp)
          _ = _ := mul_one _
      _ = μ univ := by simp
  rw [lintegral_rpow_eq_lintegral_meas_lt_mul μ (ae_of_all _ hf0) hfm.aemeasurable
    (zero_lt_one.trans hq)]
  have hsplit : Ioi (0 : ℝ) = Ioc 0 1 ∪ Ioi 1 := by ext t; simp
  rw [hsplit, lintegral_union measurableSet_Ioi (by exact disjoint_left.mpr (by grind))]
  calc
    _ ≤ ENNReal.ofReal q * (μ univ + ENNReal.ofReal (K * H) * μ univ) := by gcongr
    _ = ENNReal.ofReal (q * (1 + K * H)) * μ univ := by
      rw [ENNReal.ofReal_mul (by linarith : 0 ≤ q), ENNReal.ofReal_add zero_le_one
        (mul_nonneg hK hH), ENNReal.ofReal_one]
      ring

/-- Uniform subcritical moments for a normalized compactly supported scalar.
Both normalizations are real integrals of the original geometric data. -/
private theorem exists_normalized_poincare_moment_bound (n : ℕ) {C : ℝ}
    (hC : 0 < C) (hPI : BallScalarPoincareEstimate n C) :
    ∃ q : ℝ, 1 < q ∧ ∃ W : ℝ, 0 < W ∧
      ∀ (M : ComplexManifold n) (g : SmoothMetric M), IsComplete g → IsKahler g →
      (∀ x, (ricci g.form x).PosSemidef) → ∀ (μ : Measure M.Carrier),
      IsRiemannianVolume g.form μ → ∀ (v : M.Carrier → ℝ), SmoothFn v →
      HasCompactSupport v → (∀ z, 0 ≤ v z) → ∀ (o : M.Carrier) (R : ℝ), 0 < R →
      (∫ z, v z ∂μ) ≤ μ.real (distBall g.form o R) →
      (∫ z, Real.sqrt (scalarGradientPair g.form v v z) ∂μ) ≤
        μ.real (distBall g.form o R) / R →
      (∫ z in distBall g.form o R, v z ^ q ∂μ) ≤ W * μ.real (distBall g.form o R) := by
  obtain ⟨θ, hθ0, hθ1, _, hgain⟩ := exists_subcritical_interpolation_exponent
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
    (by positivity : (0 : ℝ) < 2 ^ (2 * n))
  let p := θ⁻¹
  have hp : 1 < p := (one_lt_inv₀ hθ0).mpr hθ1
  let q := (1 + p) / 2
  have hq : 1 < q := by dsimp [q]; linarith
  have hqp : q < p := by dsimp [q]; linarith
  obtain ⟨L, hL, hMoment⟩ := exists_moment_bound_of_polynomial_tails hq hqp
    (by positivity : (0 : ℝ) ≤ 5 ^ (2 * n))
  let B0 := C * (6 : ℝ) ^ (2 * n) /
    (1 - (1 / 2 : ℝ) * ((2 : ℝ) ^ (2 * n)) ^ (1 - θ))
  let B := (3 : ℝ) ^ (2 * n) + B0 + 1
  have hB0 : 0 ≤ B0 := by dsimp [B0]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨q, hq, L * B ^ q, by positivity, ?_⟩
  intro M g hc hK hRic μ hμ v hv hcv hv0 o R hR hI hJ
  let T := distBall g.form o R
  let V := μ.real T
  let G : M.Carrier → ℝ := fun z => Real.sqrt (scalarGradientPair g.form v v z)
  let w : M.Carrier → ℝ := fun z => v z / B
  have hV : 0 < V := ball_real_pos g μ hμ o hR
  have hTf : μ T < ⊤ := riemannianVolume_distBall_lt_top g μ hμ o hR
  letI : IsFiniteMeasure (μ.restrict T) := ⟨by simpa using hTf⟩
  letI metric := L12Aux.inducedMetricSpace g
  letI : SecondCountableTopology M.Carrier := M.secondCountable
  letI sep : TopologicalSpace.SeparableSpace M.Carrier :=
    TopologicalSpace.SecondCountableTopology.to_separableSpace
  have hopens : @OpensMeasurableSpace M.Carrier
      metric.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace (borel M.Carrier) :=
    ⟨le_rfl⟩
  have hG : Integrable G μ := gradient_norm_integrable g μ hμ hv hcv
  have hG0 : ∀ z, 0 ≤ G z := fun z => Real.sqrt_nonneg _
  have hw0 : ∀ z, 0 ≤ w z := fun z => div_nonneg (hv0 z) hB.le
  have hwm : Measurable w := ((continuous_of_smoothFn hv).div_const B).measurable
  have htail (t : ℝ) (ht : 1 ≤ t) : (μ.restrict T) {z | t < w z} ≤
      ENNReal.ofReal ((5 : ℝ) ^ (2 * n) * t ^ (-p)) * (μ.restrict T) univ := by
    have ht0 : 0 < t := zero_lt_one.trans_le ht
    let τ := t ^ p / R
    have hτ : 0 < τ := by dsimp [τ]; positivity
    let E : Set M.Carrier := {z | ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 3 * R ∧
      ENNReal.ofReal τ * μ (Metric.ball z ρ) <
        ∫⁻ z' in Metric.ball z ρ, ENNReal.ofReal (G z') ∂μ}
    have hsub : {z | t < w z} ∩ T ⊆ E := by
      intro y hy
      by_contra hnot
      have hlocal (ρ : ℝ) (hρ : 0 < ρ) (hρR : ρ ≤ 3 * R) :
          (∫ z in distBall g.form y ρ, G z ∂μ) ≤ τ * μ.real (distBall g.form y ρ) := by
        have hbad : ¬ (ENNReal.ofReal τ * μ (Metric.ball y ρ) <
            ∫⁻ z in Metric.ball y ρ, ENNReal.ofReal (G z) ∂μ) := by
          intro hlt
          exact hnot ⟨ρ, hρ, hρR, hlt⟩
        have hreal := ENNReal.toReal_mono
          (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
            (by rw [← L12Aux.distBall_eq_metric_ball g y hρ]
                exact riemannianVolume_distBall_lt_top g μ hμ y hρ)).ne
          (le_of_not_gt hbad)
        rw [← L12Aux.distBall_eq_metric_ball g y hρ] at hreal
        rw [← ofReal_integral_eq_lintegral_ofReal hG.integrableOn
          (ae_of_all _ hG0), ENNReal.toReal_ofReal (integral_nonneg hG0),
          ENNReal.toReal_mul, ENNReal.toReal_ofReal hτ.le] at hreal
        exact hreal
      have hpot := normalized_poincare_potential hC.le hPI hθ0 hθ1 hgain
        g hc hK hRic μ hμ hv hcv hv0 o y hR hτ hy.2 hI hJ hlocal
      have hpow : (R * τ) ^ θ = t := by
        dsimp only [τ, p]
        rw [mul_div_cancel₀ _ hR.ne', ← Real.rpow_mul ht0.le,
          inv_mul_cancel₀ hθ0.ne', Real.rpow_one]
      rw [hpow] at hpot
      have hy' : B * t < v y := by
        have hh : t < v y / B := hy.1
        simpa only [mul_comm] using (lt_div_iff₀ hB).mp hh
      have hsmall : (3 : ℝ) ^ (2 * n) + B0 * t ≤ B * t := by
        dsimp [B]
        nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 3) (2 * n)]
      exact (not_lt_of_ge (hpot.trans hsmall)) hy'
    have hweak := @weak_local_average_superlevel_measure M.Carrier metric.toPseudoMetricSpace
      sep (borel M.Carrier) hopens μ (3 * R)
      (fun z => ENNReal.ofReal (G z)) (ENNReal.ofReal τ)
      (ENNReal.ofReal ((5 : ℝ) ^ (2 * n))) (by
        intro z ρ hρ _hρR
        have hb := Yau.LeafProofs.L12 n M g hc hK hRic μ hμ z ρ (5 * ρ) hρ
          (by linarith)
        have heq : (5 * ρ) / ρ = (5 : ℝ) := by field_simp
        rw [heq, L12Aux.distBall_eq_metric_ball g z hρ,
          L12Aux.distBall_eq_metric_ball g z (by positivity)] at hb
        exact hb)
    have hweak' : ENNReal.ofReal τ * μ E ≤
        ENNReal.ofReal ((5 : ℝ) ^ (2 * n) * (V / R)) := by
      calc
        _ ≤ ENNReal.ofReal ((5 : ℝ) ^ (2 * n)) *
            ∫⁻ z, ENNReal.ofReal (G z) ∂μ := hweak
        _ ≤ ENNReal.ofReal ((5 : ℝ) ^ (2 * n)) * ENNReal.ofReal (V / R) := by
          rw [← ofReal_integral_eq_lintegral_ofReal hG (ae_of_all _ hG0)]
          gcongr
        _ = _ := (ENNReal.ofReal_mul (by positivity)).symm
    have hmeasure : μ E ≤ ENNReal.ofReal
        (((5 : ℝ) ^ (2 * n) * (V / R)) / τ) := by
      rw [ENNReal.ofReal_div_of_pos hτ]
      apply (ENNReal.le_div_iff_mul_le
        (Or.inl (ENNReal.ofReal_pos.mpr hτ).ne') (Or.inl ENNReal.ofReal_ne_top)).mpr
      simpa only [mul_comm] using hweak'
    have halgebra : (((5 : ℝ) ^ (2 * n) * (V / R)) / τ) =
        ((5 : ℝ) ^ (2 * n) * t ^ (-p)) * V := by
      dsimp only [τ]
      rw [Real.rpow_neg ht0.le]
      field_simp
    calc
      _ = μ ({z | t < w z} ∩ T) := Measure.restrict_apply (measurableSet_lt measurable_const hwm)
      _ ≤ μ E := measure_mono hsub
      _ ≤ _ := hmeasure.trans_eq (by
        rw [halgebra, ENNReal.ofReal_mul (by positivity), Measure.restrict_apply_univ]
        congr 1
        exact ENNReal.ofReal_toReal hTf.ne)
  have hMom := hMoment (μ.restrict T) w hw0 hwm htail
  have hi : IntegrableOn (fun z => v z ^ q) T μ :=
    continuous_integrableOn_distBall g μ hμ
      ((continuous_of_smoothFn hv).rpow_const (fun _ => Or.inr (by linarith))) o hR
  have hwq : (fun z => w z ^ q) = fun z => (B ^ q)⁻¹ * v z ^ q := by
    funext z
    dsimp [w]
    rw [Real.div_rpow (hv0 z) hB.le]
    ring
  have hiw : IntegrableOn (fun z => w z ^ q) T μ := by rw [hwq]; exact hi.const_mul _
  rw [← ofReal_integral_eq_lintegral_ofReal hiw
    (ae_of_all _ (fun z => Real.rpow_nonneg (hw0 z) _)),
    Measure.restrict_apply_univ, ← ENNReal.ofReal_toReal hTf.ne,
    ← ENNReal.ofReal_mul hL.le] at hMom
  have hMom' := (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hL.le hV.le)).mp hMom
  rw [hwq, integral_const_mul] at hMom'
  have hBq : 0 < B ^ q := Real.rpow_pos_of_pos hB _
  have hh := mul_le_mul_of_nonneg_left hMom' hBq.le
  calc
    _ ≤ B ^ q * (L * V) := by simpa only [← mul_assoc, mul_inv_cancel₀ hBq.ne', one_mul] using hh
    _ = _ := by ring

/-- The Poincaré input yields a genuine scalar Sobolev gain in every positive
complex dimension. The original L² term remains in the conclusion. -/
theorem exists_ballScalarSobolevEstimate_of_poincare (n : ℕ) (_hn : 0 < n)
    (hPI : ∃ C : ℝ, 0 < C ∧ BallScalarPoincareEstimate n C) :
    ∃ S : ℝ, 0 < S ∧ ∃ q : ℝ, 1 < q ∧ BallScalarSobolevEstimate n S q := by
  obtain ⟨C, hC, hPI⟩ := hPI
  obtain ⟨q, hq, W, hW, hMoment⟩ := exists_normalized_poincare_moment_bound n hC hPI
  refine ⟨W ^ q⁻¹, Real.rpow_pos_of_pos hW _, q, hq, ?_⟩
  intro M g hc hK hRic μ hμ o R hR f hf hcf hf0 hsupport
  let T := distBall g.form o R
  let V := μ.real T
  let I := ∫ y in T, f y ^ 2 ∂μ
  let E := ∫ y, scalarGradientPair g.form f f y ∂μ
  let H := R ^ 2 * E + I
  have hV : 0 < V := ball_real_pos g μ hμ o hR
  have hI : 0 ≤ I := integral_nonneg (fun y => sq_nonneg (f y))
  have hE : 0 ≤ E := integral_nonneg (scalarGradientPair_self_nonneg g.form f)
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hi2 : IntegrableOn (fun y => f y ^ 2) T μ :=
    smoothFn_integrableOn_distBall g μ hμ (smoothFn_pow hf 2) o hR
  have hcf2 : HasCompactSupport (fun y => f y ^ 2) := by
    apply HasCompactSupport.comp_left hcf (g := fun t : ℝ => t ^ 2)
    norm_num
  have hqpos : 0 < q := zero_lt_one.trans hq
  have hglobal : (∫ y, f y ^ 2 ∂μ) = I := by
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro y hy
    have hfy : f y = 0 := image_eq_zero_of_notMem_tsupport (fun hs => hy (hsupport hs))
    rw [hfy, zero_pow (by decide)]
  by_cases hHz : H = 0
  · have hIz : I = 0 := by dsimp [H] at hHz; nlinarith [mul_nonneg (sq_nonneg R) hE]
    have hfae := (integral_eq_zero_iff_of_nonneg
      (fun y => sq_nonneg (f y)) hi2).mp hIz
    have hzero : (∫ y in T, f y ^ (2 * q) ∂μ) = 0 := by
      apply integral_eq_zero_of_ae
      filter_upwards [hfae] with y hy
      change f y ^ (2 * q) = 0
      have hfy : f y = 0 := sq_eq_zero_iff.mp hy
      rw [hfy, Real.zero_rpow (by positivity : 2 * q ≠ 0)]
    rw [hzero, Real.zero_rpow (inv_ne_zero hqpos.ne')]
    change 0 ≤ W ^ q⁻¹ * V ^ (q⁻¹ - 1) * H
    positivity
  · have hHpos : 0 < H := lt_of_le_of_ne hH (Ne.symm hHz)
    let a := V / H
    have ha : 0 < a := div_pos hV hHpos
    let v : M.Carrier → ℝ := fun y => a * f y ^ 2
    have hv : SmoothFn v := smoothFn_mul (smoothFn_const a) (smoothFn_pow hf 2)
    have hcv : HasCompactSupport v := hcf2.mul_left
    have hv0 : ∀ y, 0 ≤ v y := fun y => mul_nonneg ha.le (sq_nonneg (f y))
    have hvI : (∫ y, v y ∂μ) ≤ V := by
      dsimp only [v]
      rw [integral_const_mul, hglobal]
      calc
        a * I ≤ a * H := mul_le_mul_of_nonneg_left (by dsimp [H]; nlinarith) ha.le
        _ = V := by dsimp [a]; field_simp
    have hgrad (y : M.Carrier) :
        Real.sqrt (scalarGradientPair g.form v v y) =
          2 * a * f y * Real.sqrt (scalarGradientPair g.form f f y) := by
      have hF : DifferentiableAt ℝ (fun t : ℝ => a * t ^ 2) (f y) := by fun_prop
      have hder : deriv (fun t : ℝ => a * t ^ 2) (f y) = 2 * a * f y := by
        simpa only [id_eq, Pi.pow_apply, Nat.cast_ofNat, Nat.reduceSub, pow_one, one_mul, mul_one, mul_assoc,
          mul_comm, mul_left_comm] using (((hasDerivAt_id (f y)).pow 2).const_mul a).deriv
      rw [show v = fun y => a * f y ^ 2 from rfl,
        scalarGradientPair_scalar_comp_self g.form hf (fun t : ℝ => a * t ^ 2) y hF,
        hder, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs,
        abs_of_nonneg (mul_nonneg (by positivity) (hf0 y))]
    have hvJ : (∫ y, Real.sqrt (scalarGradientPair g.form v v y) ∂μ) ≤ V / R := by
      have hbound (y : M.Carrier) :
          R * Real.sqrt (scalarGradientPair g.form v v y) ≤
            a * (f y ^ 2 + R ^ 2 * scalarGradientPair g.form f f y) := by
        rw [hgrad]
        have hs := Real.sq_sqrt (scalarGradientPair_self_nonneg g.form f y)
        calc
          _ = a * (2 * f y * (R * Real.sqrt (scalarGradientPair g.form f f y))) := by ring
          _ ≤ a * (f y ^ 2 + (R * Real.sqrt (scalarGradientPair g.form f f y)) ^ 2) :=
            mul_le_mul_of_nonneg_left (by
              nlinarith [sq_nonneg (f y - R * Real.sqrt (scalarGradientPair g.form f f y))]) ha.le
          _ = _ := by rw [mul_pow, hs]
      have hfi : Integrable (fun y => a *
          (f y ^ 2 + R ^ 2 * scalarGradientPair g.form f f y)) μ :=
        ((smoothFn_integrable_compact g μ hμ (smoothFn_pow hf 2) hcf2).add
          ((scalarGradientPair_integrable g μ hμ hf hf hcf).const_mul (R ^ 2))).const_mul a
      have hb := integral_mono
        ((gradient_norm_integrable g μ hμ hv hcv).const_mul R) hfi hbound
      rw [integral_const_mul, integral_const_mul,
        integral_add (smoothFn_integrable_compact g μ hμ (smoothFn_pow hf 2) hcf2)
          ((scalarGradientPair_integrable g μ hμ hf hf hcf).const_mul (R ^ 2)),
        integral_const_mul, hglobal] at hb
      have hright : a * (I + R ^ 2 * E) = V := by
        rw [show I + R ^ 2 * E = H by dsimp [H]; ring]
        exact div_mul_cancel₀ V hHz
      rw [hright] at hb
      exact (le_div_iff₀ hR).mpr (by simpa only [mul_comm] using hb)
    have hMom := hMoment M g hc hK hRic μ hμ v hv hcv hv0 o R hR hvI hvJ
    have hpower (y : M.Carrier) : v y ^ q = a ^ q * f y ^ (2 * q) := by
      dsimp only [v]
      rw [Real.mul_rpow ha.le (sq_nonneg _), ← Real.rpow_natCast_mul (hf0 y) 2 q]
      norm_num
    simp_rw [hpower] at hMom
    rw [integral_const_mul] at hMom
    have hHigh0 : 0 ≤ ∫ y in T, f y ^ (2 * q) ∂μ :=
      integral_nonneg (fun y => Real.rpow_nonneg (hf0 y) _)
    have hroot := Real.rpow_le_rpow (mul_nonneg (Real.rpow_nonneg ha.le _) hHigh0)
      hMom (inv_nonneg.mpr hqpos.le)
    rw [Real.mul_rpow (Real.rpow_nonneg ha.le _) hHigh0,
      ← Real.rpow_mul ha.le, mul_inv_cancel₀ hqpos.ne', Real.rpow_one,
      Real.mul_rpow hW.le hV.le] at hroot
    have hfinal : (∫ y in T, f y ^ (2 * q) ∂μ) ^ q⁻¹ ≤
        W ^ q⁻¹ * V ^ (q⁻¹ - 1) * H := by
      have hroot' : (∫ y in T, f y ^ (2 * q) ∂μ) ^ q⁻¹ ≤
          (W ^ q⁻¹ * V ^ q⁻¹) / a :=
        (le_div_iff₀ ha).mpr (by
          rw [mul_comm]
          exact hroot)
      convert hroot' using 1
      rw [Real.rpow_sub hV, Real.rpow_one]
      dsimp [a]
      field_simp
    exact hfinal

end Yau.LeafProofs.L18Aux
