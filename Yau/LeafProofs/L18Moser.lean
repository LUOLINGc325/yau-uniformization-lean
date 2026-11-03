import Yau.LeafProofs.L18
import Yau.LeafProofs.L12Complete
import Yau.LeafProofs.L18MeanValueAssembly

/-! The scalar Sobolev-to-Moser part of the Li--Schoen proof.
The Sobolev proposition below is an explicit intermediate gap, not an axiom.
Its constant and gain exponent are selected before every geometric input. -/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold ENNReal ComplexOrder

namespace Yau.LeafProofs.L18Aux

/-- The normalized local scalar Sobolev inequality needed by Moser iteration.
The zeroth-order term covers balls that contain a compact manifold. -/
def BallScalarSobolevEstimate (n : ℕ) (S q : ℝ) : Prop :=
  ∀ (M : ComplexManifold n) (g : SmoothMetric M),
    IsComplete g → IsKahler g → (∀ x, (ricci g.form x).PosSemidef) →
    ∀ (μ : Measure M.Carrier), IsRiemannianVolume g.form μ →
    ∀ (x : M.Carrier) (R : ℝ), 0 < R →
    ∀ (f : M.Carrier → ℝ), SmoothFn f → HasCompactSupport f →
      (∀ y, 0 ≤ f y) → tsupport f ⊆ distBall g.form x R →
      (∫ y in distBall g.form x R, f y ^ (2 * q) ∂μ) ^ q⁻¹ ≤
        S * (μ.real (distBall g.form x R)) ^ (q⁻¹ - 1) *
          (R ^ 2 * ∫ y, scalarGradientPair g.form f f y ∂μ +
            ∫ y in distBall g.form x R, f y ^ 2 ∂μ)

/-- Continuous scalar powers are genuinely integrable on every original
finite-radius ball, including powers of cutoffs which vanish. -/
theorem continuous_integrableOn_distBall {n : ℕ} {M : ComplexManifold n}
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    {f : M.Carrier → ℝ} (hf : Continuous f) (x : M.Carrier) {R : ℝ} (hR : 0 < R) :
    IntegrableOn f (distBall g.form x R) μ := by
  letI : IsLocallyFiniteMeasure μ := riemannianVolume_locallyFinite g μ hμ
  apply (hf.continuousOn.integrableOn_compact
    (L12Aux.isCompact_inducedDistance_sublevel g x R)).mono_set
  intro y hy
  exact ((L12Aux.mem_distBall_iff g x y hR).mp hy).le

/-- One genuine annular Moser step. The only conditional input is the
explicit scalar Sobolev inequality; its test function and energy cutoff
are constructed from the original smooth subharmonic function. -/
theorem exists_uniform_annular_moser_steps (n : ℕ) {S q : ℝ}
    (hS : 0 ≤ S) (hq : 1 < q) (hSob : BallScalarSobolevEstimate n S q) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : ComplexManifold n) (g : SmoothMetric M), IsComplete g →
      IsKahler g → (∀ x, (ricci g.form x).PosSemidef) →
      ∀ (μ : Measure M.Carrier), IsRiemannianVolume g.form μ →
      ∀ (u : M.Carrier → ℝ), SmoothFn u → (∀ y, 0 ≤ u y) →
      (∀ y, 0 ≤ laplacian g.form u y) →
      ∀ (x : M.Carrier) (r R ε p : ℝ), 0 < r → r < R → 0 < ε → 1 ≤ p →
      (∫ y in distBall g.form x r, (u y + ε) ^ (2 * p * q) ∂μ) ^ q⁻¹ ≤
        S * (μ.real (distBall g.form x R)) ^ (q⁻¹ - 1) *
          (C * R ^ 2 / (R - r) ^ 2 + 1) *
            ∫ y in distBall g.form x R, (u y + ε) ^ (2 * p) ∂μ := by
  obtain ⟨C, hC, hCut⟩ := exists_uniform_annular_moser_energy_cutoffs n
  refine ⟨C, hC, ?_⟩
  intro M g hc hK hRic μ hμ u hu h0 hsub x r R ε p hr hrR hε hp
  obtain ⟨η, _hηC, hη, hcη, hηrange, hηone, hsη, hE⟩ :=
    hCut M g hK μ hμ u hu h0 hsub x r R hr hrR ε p hε hp
  let w : M.Carrier → ℝ := fun y => u y + ε
  have hw : SmoothFn w := fun a => (hu a).add contDiffOn_const
  have hwpos : ∀ y, 0 < w y := fun y => add_pos_of_nonneg_of_pos (h0 y) hε
  let f : M.Carrier → ℝ := fun y => η y * w y ^ p
  have hf : SmoothFn f := smoothFn_mul hη (smoothFn_rpow hw (fun y => (hwpos y).ne') p)
  have hcf : HasCompactSupport f := hcη.mul_right
  have hf0 : ∀ y, 0 ≤ f y := fun y =>
    mul_nonneg (hηrange y).1 (Real.rpow_nonneg (hwpos y).le p)
  have hsf : tsupport f ⊆ distBall g.form x R :=
    tsupport_mul_subset_left.trans hsη
  have hR : 0 < R := hr.trans hrR
  have hiPow : IntegrableOn (fun y => w y ^ (2 * p)) (distBall g.form x R) μ :=
    smoothFn_integrableOn_distBall g μ hμ (smoothFn_rpow hw (fun y => (hwpos y).ne') _) x hR
  have hif2 : IntegrableOn (fun y => f y ^ 2) (distBall g.form x R) μ :=
    smoothFn_integrableOn_distBall g μ hμ (smoothFn_pow hf 2) x hR
  have hLow : (∫ y in distBall g.form x R, f y ^ 2 ∂μ) ≤
      ∫ y in distBall g.form x R, w y ^ (2 * p) ∂μ := by
    apply setIntegral_mono_on hif2 hiPow (L12Aux.measurableSet_distBall g x R)
    intro y _hy
    have hη2 : η y ^ 2 ≤ 1 := by nlinarith [(hηrange y).1, (hηrange y).2]
    have hpow : (w y ^ p) ^ 2 = w y ^ (2 * p) := by
      rw [← Real.rpow_mul_natCast (hwpos y).le p 2]
      congr 1
      ring
    change (η y * w y ^ p) ^ 2 ≤ _
    rw [mul_pow, hpow]
    exact (mul_le_mul_of_nonneg_right hη2 (Real.rpow_nonneg (hwpos y).le _)).trans_eq (one_mul _)
  have hiHigh : IntegrableOn (fun y => f y ^ (2 * q)) (distBall g.form x R) μ :=
    continuous_integrableOn_distBall g μ hμ
      ((continuous_of_smoothFn hf).rpow_const (fun _ => Or.inr (by linarith))) x hR
  have hsubBall : distBall g.form x r ⊆ distBall g.form x R := by
    intro y hy
    exact (L12Aux.mem_distBall_iff g x y hR).mpr
      (((L12Aux.mem_distBall_iff g x y hr).mp hy).trans hrR)
  have hHigh : (∫ y in distBall g.form x r, w y ^ (2 * p * q) ∂μ) ≤
      ∫ y in distBall g.form x R, f y ^ (2 * q) ∂μ := by
    calc
      _ = ∫ y in distBall g.form x r, f y ^ (2 * q) ∂μ := by
        apply setIntegral_congr_fun (L12Aux.measurableSet_distBall g x r)
        intro y hy
        have hηy : η y = 1 := hηone y ((L12Aux.mem_distBall_iff g x y hr).mp hy).le
        dsimp only [f]
        rw [hηy, one_mul, ← Real.rpow_mul (hwpos y).le]
        congr 1
        ring
      _ ≤ _ := setIntegral_mono_set hiHigh
        (ae_restrict_of_forall_mem (L12Aux.measurableSet_distBall g x R)
          (fun y _ => Real.rpow_nonneg (hf0 y) _))
        (Eventually.of_forall (fun y hy => hsubBall hy))
  have hSobf := hSob M g hc hK hRic μ hμ x R hR f hf hcf hf0 hsf
  have hM0 : 0 ≤ S * (μ.real (distBall g.form x R)) ^ (q⁻¹ - 1) :=
    mul_nonneg hS (Real.rpow_nonneg ENNReal.toReal_nonneg _)
  have hMoment0 : 0 ≤ ∫ y in distBall g.form x R, w y ^ (2 * p) ∂μ :=
    integral_nonneg (fun y => Real.rpow_nonneg (hwpos y).le _)
  calc
    _ ≤ (∫ y in distBall g.form x R, f y ^ (2 * q) ∂μ) ^ q⁻¹ :=
      Real.rpow_le_rpow (integral_nonneg (fun y => Real.rpow_nonneg (hwpos y).le _))
        hHigh (inv_nonneg.mpr (by linarith))
    _ ≤ _ := hSobf.trans ?_
  rw [mul_assoc (S * _) _ _]
  apply mul_le_mul_of_nonneg_left _ hM0
  calc
    _ ≤ R ^ 2 * (C / (R - r) ^ 2 * ∫ y in distBall g.form x R, w y ^ (2 * p) ∂μ) +
        ∫ y in distBall g.form x R, w y ^ (2 * p) ∂μ :=
      add_le_add (mul_le_mul_of_nonneg_left hE (sq_nonneg R)) hLow
    _ = _ := by ring

/-- The numerical Moser recurrence, expressed in normalized moments.
Taking the successive inverse powers turns the multiplicative factors
into the summable exponential recurrence already proved internally. -/
theorem normalized_moser_sequence_bound {q K b : ℝ}
    (hq : 1 < q) (hK : 1 ≤ K) (hb : 1 ≤ b)
    (a : ℕ → ℝ) (ha : ∀ j, 0 ≤ a j)
    (hrec : ∀ j, a (j + 1) ^ q⁻¹ ≤ K * b ^ j * a j) :
    ∀ j, a j ^ (q⁻¹ ^ j) ≤
      Real.exp (Real.log K / (1 - q⁻¹) +
        Real.log b * q⁻¹ / (1 - q⁻¹) ^ 2) * a 0 := by
  have hqpos : 0 < q := zero_lt_one.trans hq
  have hi0 : 0 ≤ q⁻¹ := (inv_pos.mpr hqpos).le
  have hi1 : q⁻¹ < 1 := (inv_lt_one₀ hqpos).mpr hq
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  have hbpos : 0 < b := zero_lt_one.trans_le hb
  let s : ℕ → ℝ := fun j => a j ^ (q⁻¹ ^ j)
  have hs0 : 0 ≤ s 0 := Real.rpow_nonneg (ha 0) _
  have hsrec (j : ℕ) :
      s (j + 1) ≤ Real.exp (q⁻¹ ^ j * (Real.log K + (j : ℝ) * Real.log b)) * s j := by
    have hpow : s (j + 1) = (a (j + 1) ^ q⁻¹) ^ (q⁻¹ ^ j) := by
      dsimp only [s]
      rw [← Real.rpow_mul (ha (j + 1)), pow_succ']
    rw [hpow]
    calc
      _ ≤ (K * b ^ j * a j) ^ (q⁻¹ ^ j) :=
        Real.rpow_le_rpow (Real.rpow_nonneg (ha (j + 1)) _) (hrec j) (pow_nonneg hi0 j)
      _ = (K * b ^ j) ^ (q⁻¹ ^ j) * s j := by
        rw [Real.mul_rpow (mul_nonneg hKpos.le (pow_nonneg hbpos.le j)) (ha j)]
      _ = _ := by
        congr 1
        rw [Real.rpow_def_of_pos (mul_pos hKpos (pow_pos hbpos j)),
          Real.log_mul hKpos.ne' (pow_pos hbpos j).ne', Real.log_pow]
        congr 1
        ring
  have hbnd := geometric_exponential_iteration_bound hi0 hi1
    (Real.log_nonneg hK) (Real.log_nonneg hb) s hs0 hsrec
  intro j
  simpa only [s, pow_zero, Real.rpow_one] using hbnd j

/-- Normalized Moser moments give an actual everywhere estimate.
The moment sets may vary; all their use is recorded in the displayed
upper bounds on the one fixed open set. -/
theorem moser_pointwise_of_normalized_moments {X : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] (μ : Measure X) [μ.IsOpenPosMeasure]
    {U : Set X} (hU : IsOpen U) (hUf : μ U < ⊤)
    {u : X → ℝ} (hu : Continuous u) (hu0 : ∀ x ∈ U, 0 ≤ u x)
    {q K b V : ℝ} (hq : 1 < q) (hK : 1 ≤ K) (hb : 1 ≤ b) (hV : 0 < V)
    (a : ℕ → ℝ) (ha : ∀ j, 0 ≤ a j) (ha0 : 0 < a 0)
    (hrec : ∀ j, a (j + 1) ^ q⁻¹ ≤ K * b ^ j * a j)
    (hMom : ∀ j, IntegrableOn (fun x => u x ^ (2 * q ^ j)) U μ ∧
      (∫ x in U, u x ^ (2 * q ^ j) ∂μ) ≤ V * a j) :
    ∀ x ∈ U, u x ^ 2 ≤
      Real.exp (Real.log K / (1 - q⁻¹) +
        Real.log b * q⁻¹ / (1 - q⁻¹) ^ 2) * a 0 := by
  let E := Real.exp (Real.log K / (1 - q⁻¹) +
    Real.log b * q⁻¹ / (1 - q⁻¹) ^ 2)
  let B := Real.sqrt (E * a 0)
  have hE : 0 < E := Real.exp_pos _
  have hB : 0 < B := Real.sqrt_pos.mpr (mul_pos hE ha0)
  have hB2 : B ^ 2 = E * a 0 := Real.sq_sqrt (mul_pos hE ha0).le
  have hbound := normalized_moser_sequence_bound hq hK hb a ha hrec
  have hpower (j : ℕ) : a j ≤ (E * a 0) ^ (q ^ j) := by
    have h := Real.rpow_le_rpow (Real.rpow_nonneg (ha j) _) (hbound j)
      (pow_nonneg (zero_lt_one.trans hq).le j)
    have he : (a j ^ (q⁻¹ ^ j)) ^ (q ^ j) = a j := by
      rw [← Real.rpow_mul (ha j), ← mul_pow, inv_mul_cancel₀ (zero_lt_one.trans hq).ne',
        one_pow, Real.rpow_one]
    simpa only [he] using h
  have hBpow (j : ℕ) : B ^ (2 * q ^ j) = (E * a 0) ^ (q ^ j) := by
    rw [Real.rpow_mul hB.le, Real.rpow_two, hB2]
  have hlim : Tendsto (fun j : ℕ => 2 * q ^ j) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt hq).const_mul_atTop (by norm_num)
  have hpoint : ∀ x ∈ U, u x ≤ B := by
    apply continuous_le_of_rpow_integral_bounds μ hU hUf hu hu0
      (fun j => mul_nonneg (by norm_num) (pow_nonneg (zero_lt_one.trans hq).le j)) hlim hB
    intro j
    refine ⟨(hMom j).1, ?_⟩
    rw [hBpow]
    exact (hMom j).2.trans (mul_le_mul_of_nonneg_left (hpower j) hV.le)
  intro x hx
  have hx0 := hu0 x hx
  have hxB := hpoint x hx
  dsimp only [E] at hB2 ⊢
  nlinarith

/-- A volume denominator can be replaced by a fixed outer-ball volume
using only the actual volume comparison and monotonicity. -/
theorem volume_rpow_sub_one_comparison {v V D s : ℝ}
    (hv : 0 < v) (hV : 0 < V) (hvV : v ≤ V) (hVDv : V ≤ D * v) (hs : 0 ≤ s) :
    v ^ (s - 1) ≤ D * V ^ (s - 1) := by
  rw [Real.rpow_sub_one hv.ne', Real.rpow_sub_one hV.ne']
  calc
    _ ≤ V ^ s / v := div_le_div_of_nonneg_right (Real.rpow_le_rpow hv.le hvV hs) hv.le
    _ ≤ (D * V ^ s) / V := by
      apply (div_le_div_iff₀ hv hV).mpr
      nlinarith [mul_le_mul_of_nonneg_left hVDv (Real.rpow_nonneg hV.le s)]
    _ = _ := by ring

/-- Normalizing every Moser moment by the same outer-ball volume makes
the exponent in the recurrence independent of the current ball. -/
theorem normalized_sobolev_step {I J v V S D k s : ℝ}
    (hI : 0 ≤ I) (hJ : 0 ≤ J) (hv : 0 < v) (hV : 0 < V)
    (hvV : v ≤ V) (hVDv : V ≤ D * v) (hS : 0 ≤ S) (hk : 0 ≤ k) (hs : 0 ≤ s)
    (hstep : I ^ s ≤ S * v ^ (s - 1) * k * J) :
    (I / V) ^ s ≤ S * D * k * (J / V) := by
  have hpow := volume_rpow_sub_one_comparison hv hV hvV hVDv hs
  rw [Real.div_rpow hI hV.le]
  calc
    _ ≤ (S * (D * V ^ (s - 1)) * k * J) / V ^ s := by
      apply div_le_div_of_nonneg_right _ (Real.rpow_nonneg hV.le _)
      exact hstep.trans (by gcongr)
    _ = _ := by
      rw [Real.rpow_sub_one hV.ne']
      field_simp

private def moserRadius (r R : ℝ) (j : ℕ) : ℝ :=
  (R + r) / 2 + (R - r) / 2 * (1 / 2 : ℝ) ^ j

private theorem moserRadius_bounds {r R : ℝ} (hr : 0 < r) (hrR : r < R) (j : ℕ) :
    r < moserRadius r R j ∧ moserRadius r R j ≤ R ∧ R / 2 ≤ moserRadius r R j := by
  have hp : 0 < (1 / 2 : ℝ) ^ j := by positivity
  have hp1 : (1 / 2 : ℝ) ^ j ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  dsimp [moserRadius]
  constructor
  · nlinarith
  constructor <;> nlinarith

private theorem moserRadius_succ {r R : ℝ} (hrR : r < R) (j : ℕ) :
    moserRadius r R (j + 1) < moserRadius r R j ∧
      moserRadius r R j - moserRadius r R (j + 1) =
        (R - r) / 4 * (1 / 2 : ℝ) ^ j := by
  have hp : 0 < (1 / 2 : ℝ) ^ j := by positivity
  have he : moserRadius r R j - moserRadius r R (j + 1) =
      (R - r) / 4 * (1 / 2 : ℝ) ^ j := by
    dsimp [moserRadius]
    rw [pow_succ]
    ring
  exact ⟨by rw [← sub_pos, he]; positivity, he⟩

private theorem moserRadius_volume_comparison {n : ℕ} {M : ComplexManifold n}
    (g : SmoothMetric M) (hc : IsComplete g) (hK : IsKahler g)
    (hRic : ∀ x, (ricci g.form x).PosSemidef)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (x : M.Carrier) {r R : ℝ} (hr : 0 < r) (hrR : r < R) (j : ℕ) :
    μ.real (distBall g.form x R) ≤
      (2 : ℝ) ^ (2 * n) * μ.real (distBall g.form x (moserRadius r R j)) := by
  have hρ := moserRadius_bounds hr hrR j
  have hρpos : 0 < moserRadius r R j := hr.trans hρ.1
  have hratio : R / moserRadius r R j ≤ 2 := by
    apply (div_le_iff₀ hρpos).mpr
    linarith [hρ.2.2]
  have hbg := Yau.LeafProofs.L12 n M g hc hK hRic μ hμ x
    (moserRadius r R j) R hρpos hρ.2.1
  have hpow : (R / moserRadius r R j) ^ (2 * n) ≤ (2 : ℝ) ^ (2 * n) :=
    pow_le_pow_left₀ (div_nonneg (hr.trans hrR).le hρpos.le) hratio _
  have hbg' : μ (distBall g.form x R) ≤
      ENNReal.ofReal ((2 : ℝ) ^ (2 * n)) * μ (distBall g.form x (moserRadius r R j)) :=
    hbg.trans (by gcongr)
  have ht : ENNReal.ofReal ((2 : ℝ) ^ (2 * n)) *
      μ (distBall g.form x (moserRadius r R j)) ≠ ⊤ :=
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (riemannianVolume_distBall_lt_top g μ hμ x hρpos)).ne
  have hreal := ENNReal.toReal_mono ht hbg'
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity :
    (0 : ℝ) ≤ 2 ^ (2 * n)), Measure.real_def] using hreal

private theorem moserRadius_energy_factor {C r R : ℝ} (hC : 0 ≤ C)
    (hr : 0 < r) (hrR : r < R) (j : ℕ) :
    C * (moserRadius r R j) ^ 2 /
        (moserRadius r R j - moserRadius r R (j + 1)) ^ 2 + 1 ≤
      (16 * C + 1) * (R / (R - r)) ^ 2 * (4 : ℝ) ^ j := by
  have hρ := moserRadius_bounds hr hrR j
  have hd := moserRadius_succ hrR j
  have hgap : 0 < moserRadius r R j - moserRadius r R (j + 1) := sub_pos.mpr hd.1
  have hprod : (4 * (R / (R - r)) * (2 : ℝ) ^ j) *
      (moserRadius r R j - moserRadius r R (j + 1)) = R := by
    rw [hd.2]
    have he : (2 : ℝ) ^ j * (1 / 2 : ℝ) ^ j = 1 := by rw [← mul_pow]; norm_num
    calc
      _ = R * ((2 : ℝ) ^ j * (1 / 2 : ℝ) ^ j) := by field_simp
      _ = R := by rw [he, mul_one]
  have hratio : moserRadius r R j /
      (moserRadius r R j - moserRadius r R (j + 1)) ≤
      4 * (R / (R - r)) * (2 : ℝ) ^ j := by
    exact (div_le_iff₀ hgap).mpr (hρ.2.1.trans_eq hprod.symm)
  have hsq := pow_le_pow_left₀
    (div_nonneg (hr.trans hρ.1).le hgap.le) hratio 2
  have htwo : ((2 : ℝ) ^ j) ^ 2 = (4 : ℝ) ^ j := by
    rw [← pow_mul, Nat.mul_comm j 2, pow_mul]
    norm_num
  have hlarge : 1 ≤ (R / (R - r)) ^ 2 * (4 : ℝ) ^ j := by
    have hdiv : 1 ≤ R / (R - r) := (one_le_div (sub_pos.mpr hrR)).mpr (by linarith)
    exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ hdiv) (one_le_pow₀ (by norm_num))
  calc
    _ = C * (moserRadius r R j /
        (moserRadius r R j - moserRadius r R (j + 1))) ^ 2 + 1 := by rw [div_pow]; ring
    _ ≤ C * (4 * (R / (R - r)) * (2 : ℝ) ^ j) ^ 2 +
        (R / (R - r)) ^ 2 * (4 : ℝ) ^ j :=
      add_le_add (mul_le_mul_of_nonneg_left hsq hC) hlarge
    _ = _ := by rw [mul_pow, mul_pow, htwo]; ring

private def normalizedMoserMoment {n : ℕ} {M : ComplexManifold n}
    (g : SmoothMetric M) (μ : Measure M.Carrier) (u : M.Carrier → ℝ)
    (ε q : ℝ) (x : M.Carrier) (r R : ℝ) (j : ℕ) : ℝ :=
  (∫ y in distBall g.form x (moserRadius r R j), (u y + ε) ^ (2 * q ^ j) ∂μ) /
    μ.real (distBall g.form x R)

private theorem moserRadius_zero (r R : ℝ) : moserRadius r R 0 = R := by
  simp only [moserRadius, pow_zero, mul_one]
  ring

/-- The actual shrinking-ball moments satisfy the numerical Moser
recurrence with one constant fixed before all geometric and analytic data. -/
theorem exists_uniform_normalized_moser_recurrences (n : ℕ) {S q : ℝ}
    (hS : 0 ≤ S) (hq : 1 < q) (hSob : BallScalarSobolevEstimate n S q) :
    ∃ K : ℝ, 1 ≤ K ∧
      ∀ (M : ComplexManifold n) (g : SmoothMetric M), IsComplete g →
      IsKahler g → (∀ x, (ricci g.form x).PosSemidef) →
      ∀ (μ : Measure M.Carrier), IsRiemannianVolume g.form μ →
      ∀ (u : M.Carrier → ℝ), SmoothFn u → (∀ y, 0 ≤ u y) →
      (∀ y, 0 ≤ laplacian g.form u y) →
      ∀ (x : M.Carrier) (r R ε : ℝ), 0 < r → r < R → 0 < ε →
      ∀ j : ℕ, (normalizedMoserMoment g μ u ε q x r R (j + 1)) ^ q⁻¹ ≤
        (K * (R / (R - r)) ^ 2) * (4 : ℝ) ^ j *
          normalizedMoserMoment g μ u ε q x r R j := by
  obtain ⟨C, hC, hStep⟩ := exists_uniform_annular_moser_steps n hS hq hSob
  let D : ℝ := 2 ^ (2 * n)
  let K : ℝ := max 1 (S * D * (16 * C + 1))
  refine ⟨K, le_max_left _ _, ?_⟩
  intro M g hc hK hRic μ hμ u hu h0 hsub x r R ε hr hrR hε j
  have hρ := moserRadius_bounds hr hrR j
  have hρ' := moserRadius_bounds hr hrR (j + 1)
  have hd := moserRadius_succ hrR j
  have hR : 0 < R := hr.trans hrR
  have hρpos : 0 < moserRadius r R j := hr.trans hρ.1
  have hρpos' : 0 < moserRadius r R (j + 1) := hr.trans hρ'.1
  have hV : 0 < μ.real (distBall g.form x R) :=
    ENNReal.toReal_pos (riemannianVolume_distBall_pos g μ hμ x hR).ne'
      (riemannianVolume_distBall_lt_top g μ hμ x hR).ne
  have hv : 0 < μ.real (distBall g.form x (moserRadius r R j)) :=
    ENNReal.toReal_pos (riemannianVolume_distBall_pos g μ hμ x hρpos).ne'
      (riemannianVolume_distBall_lt_top g μ hμ x hρpos).ne
  have hvV : μ.real (distBall g.form x (moserRadius r R j)) ≤
      μ.real (distBall g.form x R) := by
    apply ENNReal.toReal_mono (riemannianVolume_distBall_lt_top g μ hμ x hR).ne
    apply measure_mono
    intro y hy
    exact (L12Aux.mem_distBall_iff g x y hR).mpr
      (((L12Aux.mem_distBall_iff g x y hρpos).mp hy).trans_le hρ.2.1)
  have hVDv := moserRadius_volume_comparison g hc hK hRic μ hμ x hr hrR j
  have hqj : 1 ≤ q ^ j := one_le_pow₀ hq.le
  have hStep' := hStep M g hc hK hRic μ hμ u hu h0 hsub x
    (moserRadius r R (j + 1)) (moserRadius r R j) ε (q ^ j) hρpos' hd.1 hε hqj
  have hI0 : 0 ≤ ∫ y in distBall g.form x (moserRadius r R (j + 1)),
      (u y + ε) ^ (2 * q ^ j * q) ∂μ :=
    integral_nonneg (fun y => Real.rpow_nonneg (add_nonneg (h0 y) hε.le) _)
  have hJ0 : 0 ≤ ∫ y in distBall g.form x (moserRadius r R j),
      (u y + ε) ^ (2 * q ^ j) ∂μ :=
    integral_nonneg (fun y => Real.rpow_nonneg (add_nonneg (h0 y) hε.le) _)
  have hk0 : 0 ≤ C * (moserRadius r R j) ^ 2 /
      (moserRadius r R j - moserRadius r R (j + 1)) ^ 2 + 1 := by positivity
  have hn := normalized_sobolev_step hI0 hJ0 hv hV hvV hVDv hS hk0
    (inv_nonneg.mpr (zero_lt_one.trans hq).le) hStep'
  have ha0 : 0 ≤ normalizedMoserMoment g μ u ε q x r R j := div_nonneg hJ0 hV.le
  calc
    _ ≤ S * D * (C * (moserRadius r R j) ^ 2 /
        (moserRadius r R j - moserRadius r R (j + 1)) ^ 2 + 1) *
          normalizedMoserMoment g μ u ε q x r R j := by
      simpa only [normalizedMoserMoment, D, pow_succ, mul_assoc] using hn
    _ ≤ S * D * ((16 * C + 1) * (R / (R - r)) ^ 2 * (4 : ℝ) ^ j) *
        normalizedMoserMoment g μ u ε q x r R j := by
      gcongr
      exact moserRadius_energy_factor hC.le hr hrR j
    _ ≤ _ := by
      have hKdom : S * D * (16 * C + 1) ≤ K := le_max_right _ _
      calc
        _ = (S * D * (16 * C + 1)) * (R / (R - r)) ^ 2 * (4 : ℝ) ^ j *
            normalizedMoserMoment g μ u ε q x r R j := by ring
        _ ≤ _ := by gcongr

/-- The actual normalized Moser recurrence gives a local regularized
L² bound. No integrability, volume, measurability or pointwise-limit
premise is added to the original geometric and scalar input. -/
theorem exists_uniform_regularized_ball_l2_moser (n : ℕ) {S q : ℝ}
    (hS : 0 ≤ S) (hq : 1 < q) (hSob : BallScalarSobolevEstimate n S q) :
    ∃ K : ℝ, 1 ≤ K ∧
      ∀ (M : ComplexManifold n) (g : SmoothMetric M), IsComplete g →
      IsKahler g → (∀ x, (ricci g.form x).PosSemidef) →
      ∀ (μ : Measure M.Carrier), IsRiemannianVolume g.form μ →
      ∀ (u : M.Carrier → ℝ), SmoothFn u → (∀ y, 0 ≤ u y) →
      (∀ y, 0 ≤ laplacian g.form u y) →
      ∀ (x : M.Carrier) (r R ε : ℝ), 0 < r → r < R → 0 < ε →
      ∀ y ∈ distBall g.form x r, (u y + ε) ^ 2 ≤
        Real.exp (Real.log (K * (R / (R - r)) ^ 2) / (1 - q⁻¹) +
          Real.log 4 * q⁻¹ / (1 - q⁻¹) ^ 2) *
            ((∫ z in distBall g.form x R, (u z + ε) ^ 2 ∂μ) /
              μ.real (distBall g.form x R)) := by
  obtain ⟨K, hK, hRec⟩ := exists_uniform_normalized_moser_recurrences n hS hq hSob
  refine ⟨K, hK, ?_⟩
  intro M g hc hKg hRic μ hμ u hu h0 hsub x r R ε hr hrR hε
  let V := μ.real (distBall g.form x R)
  let w : M.Carrier → ℝ := fun y => u y + ε
  let a : ℕ → ℝ := normalizedMoserMoment g μ u ε q x r R
  have hw : SmoothFn w := fun z => (hu z).add contDiffOn_const
  have hwpos : ∀ z, 0 < w z := fun z => add_pos_of_nonneg_of_pos (h0 z) hε
  have hR : 0 < R := hr.trans hrR
  have hV : 0 < V := ENNReal.toReal_pos
    (riemannianVolume_distBall_pos g μ hμ x hR).ne'
    (riemannianVolume_distBall_lt_top g μ hμ x hR).ne
  have ha : ∀ j, 0 ≤ a j := fun j => div_nonneg
    (integral_nonneg (fun z => Real.rpow_nonneg (hwpos z).le _)) hV.le
  have haZero : a 0 = (∫ z in distBall g.form x R, w z ^ 2 ∂μ) / V := by
    simp only [a, normalizedMoserMoment, moserRadius_zero, pow_zero, mul_one,
      Real.rpow_two, w, V]
  letI : IsFiniteMeasure (μ.restrict (distBall g.form x R)) := ⟨by
    simpa only [Measure.restrict_apply_univ] using riemannianVolume_distBall_lt_top g μ hμ x hR⟩
  have hlow : V * ε ^ 2 ≤ ∫ z in distBall g.form x R, w z ^ 2 ∂μ := by
    calc
      _ = ∫ _z in distBall g.form x R, ε ^ 2 ∂μ := by
        rw [setIntegral_const]
        rfl
      _ ≤ _ := setIntegral_mono_on (integrable_const _)
        (smoothFn_integrableOn_distBall g μ hμ (smoothFn_pow hw 2) x hR)
        (L12Aux.measurableSet_distBall g x R) (fun z _hz => by
          dsimp only [w]
          nlinarith [h0 z])
  have ha0 : 0 < a 0 := by
    rw [haZero]
    exact div_pos ((mul_pos hV (sq_pos_of_pos hε)).trans_le hlow) hV
  have hratio : 1 ≤ R / (R - r) :=
    (one_le_div (sub_pos.mpr hrR)).mpr (by linarith)
  have hKratio : 1 ≤ K * (R / (R - r)) ^ 2 :=
    one_le_mul_of_one_le_of_one_le hK (one_le_pow₀ hratio)
  have hrec := hRec M g hc hKg hRic μ hμ u hu h0 hsub x r R ε hr hrR hε
  have hMom (j : ℕ) : IntegrableOn (fun z => w z ^ (2 * q ^ j)) (distBall g.form x r) μ ∧
      (∫ z in distBall g.form x r, w z ^ (2 * q ^ j) ∂μ) ≤ V * a j := by
    have hρ := moserRadius_bounds hr hrR j
    have hρpos : 0 < moserRadius r R j := hr.trans hρ.1
    have hi : IntegrableOn (fun z => w z ^ (2 * q ^ j))
        (distBall g.form x (moserRadius r R j)) μ :=
      smoothFn_integrableOn_distBall g μ hμ
        (smoothFn_rpow hw (fun z => (hwpos z).ne') _) x hρpos
    have hballs : distBall g.form x r ⊆ distBall g.form x (moserRadius r R j) := by
      intro z hz
      exact (L12Aux.mem_distBall_iff g x z hρpos).mpr
        (((L12Aux.mem_distBall_iff g x z hr).mp hz).trans hρ.1)
    refine ⟨hi.mono_set hballs, ?_⟩
    calc
      _ ≤ ∫ z in distBall g.form x (moserRadius r R j), w z ^ (2 * q ^ j) ∂μ :=
        setIntegral_mono_set hi
          (ae_restrict_of_forall_mem (L12Aux.measurableSet_distBall g x (moserRadius r R j))
            (fun z _hz => Real.rpow_nonneg (hwpos z).le _))
          (Eventually.of_forall (fun z hz => hballs hz))
      _ = V * a j := by
        change _ = V * (_ / V)
        field_simp [hV.ne']
        rfl
  letI : μ.IsOpenPosMeasure := riemannianVolume_isOpenPosMeasure g μ hμ
  have hpoint := moser_pointwise_of_normalized_moments μ
    (L12Aux.isOpen_distBall g x r) (riemannianVolume_distBall_lt_top g μ hμ x hr)
    (continuous_of_smoothFn hw) (fun z _hz => (hwpos z).le) hq hKratio (by norm_num)
    hV a ha ha0 hrec hMom
  simpa only [haZero, w, V] using hpoint

/-- The exponential Moser coefficient has a dimensional integer-power
majorant in the annular radius ratio. -/
theorem exists_moser_coefficient_power_bound {q K : ℝ} (hq : 1 < q) (hK : 1 ≤ K) :
    ∃ A : ℝ, 0 < A ∧ ∃ N : ℕ, ∀ t : ℝ, 1 ≤ t →
      Real.exp (Real.log (K * t ^ 2) / (1 - q⁻¹) +
        Real.log 4 * q⁻¹ / (1 - q⁻¹) ^ 2) ≤ A * t ^ N := by
  let A := Real.exp (Real.log K / (1 - q⁻¹) +
    Real.log 4 * q⁻¹ / (1 - q⁻¹) ^ 2)
  obtain ⟨N, hN⟩ := exists_nat_ge (2 / (1 - q⁻¹))
  refine ⟨A, Real.exp_pos _, N, ?_⟩
  intro t ht
  have htpos : 0 < t := zero_lt_one.trans_le ht
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  calc
    _ = A * t ^ (2 / (1 - q⁻¹)) := by
      rw [Real.log_mul hKpos.ne' (pow_pos htpos 2).ne', Real.log_pow,
        Real.rpow_def_of_pos htpos, ← Real.exp_add]
      congr 1
      ring
    _ ≤ A * t ^ (N : ℝ) := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le ht hN) (Real.exp_pos _).le
    _ = _ := by rw [Real.rpow_natCast]

/-- The regularized square integral is an actual finite polynomial in
the regularization parameter, for the exact original ball measure. -/
theorem integral_distBall_add_const_sq {n : ℕ} {M : ComplexManifold n}
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    {u : M.Carrier → ℝ} (hu : SmoothFn u) (x : M.Carrier) {R : ℝ} (hR : 0 < R) (ε : ℝ) :
    (∫ z in distBall g.form x R, (u z + ε) ^ 2 ∂μ) =
      (∫ z in distBall g.form x R, u z ^ 2 ∂μ) +
        2 * ε * (∫ z in distBall g.form x R, u z ∂μ) +
          ε ^ 2 * μ.real (distBall g.form x R) := by
  have hi := smoothFn_integrableOn_distBall g μ hμ hu x hR
  have hi2 := smoothFn_integrableOn_distBall g μ hμ (smoothFn_pow hu 2) x hR
  letI : IsFiniteMeasure (μ.restrict (distBall g.form x R)) := ⟨by
    simpa only [Measure.restrict_apply_univ] using riemannianVolume_distBall_lt_top g μ hμ x hR⟩
  calc
    _ = ∫ z in distBall g.form x R, (u z ^ 2 + 2 * ε * u z) + ε ^ 2 ∂μ := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun z => by ring)
    _ = _ := by
      have hsum₁ := integral_add (hi2.add (hi.const_mul (2 * ε))) (integrable_const (ε ^ 2))
      have hsum₂ := integral_add hi2 (hi.const_mul (2 * ε))
      simp only [Pi.add_apply] at hsum₁ hsum₂
      rw [hsum₁, hsum₂, integral_const_mul, setIntegral_const]
      simp only [smul_eq_mul]
      ring

/-- The explicit local scalar Sobolev estimate yields the actual ball
L² mean-value estimate. Every radius and every original nonnegative
smooth subharmonic function is retained. -/
theorem exists_ballL2MeanValueEstimate_of_sobolev (n : ℕ) {S q : ℝ}
    (hS : 0 ≤ S) (hq : 1 < q) (hSob : BallScalarSobolevEstimate n S q) :
    ∃ A : ℝ, 0 < A ∧ ∃ N : ℕ, BallL2MeanValueEstimate n A N := by
  obtain ⟨K, hK, hReg⟩ := exists_uniform_regularized_ball_l2_moser n hS hq hSob
  obtain ⟨A, hA, N, hCoeff⟩ := exists_moser_coefficient_power_bound hq hK
  refine ⟨A, hA, N, ?_⟩
  intro M g hc hKg hRic μ hμ u hu h0 hsub x r R hr hrR
  let V := μ.real (distBall g.form x R)
  let I₂ := ∫ z in distBall g.form x R, u z ^ 2 ∂μ
  let I₁ := ∫ z in distBall g.form x R, u z ∂μ
  let c := A * (R / (R - r)) ^ N / V
  let T := c * I₂
  have hR : 0 < R := hr.trans hrR
  have hV : 0 < V := ENNReal.toReal_pos
    (riemannianVolume_distBall_pos g μ hμ x hR).ne'
    (riemannianVolume_distBall_lt_top g μ hμ x hR).ne
  have hratio : 1 ≤ R / (R - r) :=
    (one_le_div (sub_pos.mpr hrR)).mpr (by linarith)
  have hT : 0 ≤ T := mul_nonneg (div_nonneg
    (mul_nonneg hA.le (pow_nonneg (zero_lt_one.trans_le hratio).le N)) hV.le)
      (integral_nonneg (fun z => sq_nonneg (u z)))
  have hpoint (y : M.Carrier) (hy : y ∈ distBall g.form x r) : u y ^ 2 ≤ T := by
    have hε (ε : ℝ) (hε : 0 < ε) :
        (u y + ε) ^ 2 ≤ c * (I₂ + 2 * ε * I₁ + ε ^ 2 * V) := by
      have h := hReg M g hc hKg hRic μ hμ u hu h0 hsub x r R ε hr hrR hε y hy
      calc
        _ ≤ A * (R / (R - r)) ^ N *
            ((∫ z in distBall g.form x R, (u z + ε) ^ 2 ∂μ) / V) :=
          h.trans (mul_le_mul_of_nonneg_right (hCoeff _ hratio)
            (div_nonneg (integral_nonneg (fun z => sq_nonneg (u z + ε))) hV.le))
        _ = _ := by
          rw [integral_distBall_add_const_sq g μ hμ hu x hR ε]
          dsimp only [c, I₂, I₁, V]
          ring
    have hL : ContinuousAt (fun ε : ℝ => (u y + ε) ^ 2) 0 := by fun_prop
    have hRlim : ContinuousAt (fun ε : ℝ => c * (I₂ + 2 * ε * I₁ + ε ^ 2 * V)) 0 := by fun_prop
    have hlim := le_of_tendsto_of_tendsto
      (hL.tendsto.mono_left nhdsWithin_le_nhds)
      (hRlim.tendsto.mono_left nhdsWithin_le_nhds)
      (show ∀ᶠ ε in 𝓝[>] (0 : ℝ), (u y + ε) ^ 2 ≤
        c * (I₂ + 2 * ε * I₁ + ε ^ 2 * V) from by
        filter_upwards [self_mem_nhdsWithin] with ε hεpos
        exact hε ε hεpos)
    simpa only [add_zero, mul_zero, zero_mul, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using hlim
  have hx : x ∈ distBall g.form x r := by
    apply (L12Aux.mem_distBall_iff g x x hr).mpr
    rw [g.induced_distance_eq_zero.mpr rfl]
    exact hr
  have hSup : sSup (u '' distBall g.form x r) ≤ Real.sqrt T := by
    apply csSup_le (show (u '' distBall g.form x r).Nonempty from ⟨u x, x, hx, rfl⟩)
    rintro z ⟨y, hy, rfl⟩
    have hpy := hpoint y hy
    have hsqrt := Real.sq_sqrt hT
    nlinarith [h0 y, Real.sqrt_nonneg T]
  obtain ⟨B, _hB, hbound⟩ := smoothFn_boundedOn_distBall g hu x hr
  have hbdd : BddAbove (u '' distBall g.form x r) := by
    refine ⟨B, ?_⟩
    rintro z ⟨y, hy, rfl⟩
    exact hbound y hy
  have hSup0 : 0 ≤ sSup (u '' distBall g.form x r) :=
    (h0 x).trans (le_csSup hbdd ⟨x, hx, rfl⟩)
  have hsqrt := Real.sq_sqrt hT
  change (sSup (u '' distBall g.form x r)) ^ 2 ≤ T
  nlinarith [Real.sqrt_nonneg T]

/-- The complete analytic route from a dimensional local scalar Sobolev
gain to the original ENNReal Li--Schoen statement. -/
theorem liSchoenMeanValue_of_ballScalarSobolev
    (h : ∀ n > 0, ∃ S : ℝ, 0 < S ∧ ∃ q : ℝ, 1 < q ∧ BallScalarSobolevEstimate n S q) :
    Yau.LeafObligations.L18 := by
  apply liSchoenMeanValue_of_ballL2Estimate
  intro n hn
  obtain ⟨S, hS, q, hq, hSob⟩ := h n hn
  exact exists_ballL2MeanValueEstimate_of_sobolev n hS.le hq hSob

end Yau.LeafProofs.L18Aux
