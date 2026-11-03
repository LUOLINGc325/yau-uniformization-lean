import Yau.Proofs.D04Truncation
import Yau.Proofs.D04FiniteL1

open MeasureTheory Filter Set
open scoped Topology ENNReal

noncomputable section

namespace Yau.Proofs.D04Aux

open Yau Yau.Blueprint

variable {n : ℕ}

/-- Simultaneous rotation of all complex coordinates, as a real isometry. -/
def scalarRotation (θ : ℝ) : ComplexVector n ≃ₗᵢ[ℝ] ComplexVector n where
  toLinearEquiv :=
    { toFun := fun v => Complex.exp (θ * Complex.I) • v
      invFun := fun v => (Complex.exp (θ * Complex.I))⁻¹ • v
      left_inv := fun v => by simp [smul_smul, Complex.exp_ne_zero]
      right_inv := fun v => by simp [smul_smul, Complex.exp_ne_zero]
      map_add' := fun v w => smul_add _ v w
      map_smul' := fun r v => smul_comm _ r v }
  norm_map' v := by simp [norm_smul]

@[simp] theorem scalarRotation_apply (θ : ℝ) (v : ComplexVector n) :
    scalarRotation θ v = Complex.exp (θ * Complex.I) • v := rfl

theorem integral_closedBall_rotate (F : ComplexVector n → ℝ)
    (x : ComplexVector n) (r θ : ℝ) :
    (∫ v in Metric.closedBall 0 r, F (x + Complex.exp (θ * Complex.I) • v)) =
      ∫ v in Metric.closedBall 0 r, F (x + v) := by
  let e : ComplexVector n ≃ₗᵢ[ℝ] ComplexVector n := scalarRotation θ
  have hpre : e ⁻¹' Metric.closedBall 0 r = Metric.closedBall 0 r := by
    ext v
    simp only [mem_preimage, Metric.mem_closedBall, dist_zero_right, e.norm_map]
  have h := e.measurePreserving.setIntegral_preimage_emb
    e.toHomeomorph.measurableEmbedding (fun v => F (x + v)) (Metric.closedBall 0 r)
  rw [hpre] at h
  exact h

theorem integral_closedBall_add (F : ComplexVector n → ℝ)
    (x : ComplexVector n) (r : ℝ) :
    (∫ v in Metric.closedBall 0 r, F (x + v)) = ∫ y in Metric.closedBall x r, F y := by
  have hpre : (fun v : ComplexVector n => x + v) ⁻¹' Metric.closedBall x r =
      Metric.closedBall 0 r := by
    ext v
    simp [Metric.mem_closedBall, dist_eq_norm]
  have h := (measurePreserving_add_left (volume : Measure (ComplexVector n)) x).setIntegral_preimage_emb
    (MeasurableEquiv.addLeft x).measurableEmbedding F
      (Metric.closedBall x r)
  rw [hpre] at h
  exact h

theorem integral_circleAverage_closedBall {F : ComplexVector n → ℝ}
    (hF : Continuous F) (x : ComplexVector n) (r : ℝ) :
    IntegrableOn (fun v => circleAverage (fun θ => F (x + Complex.exp (θ * Complex.I) • v)))
        (Metric.closedBall 0 r) volume ∧
      (∫ v in Metric.closedBall 0 r,
          circleAverage (fun θ => F (x + Complex.exp (θ * Complex.I) • v))) =
        ∫ y in Metric.closedBall x r, F y := by
  let K : Set (ComplexVector n) := Metric.closedBall 0 r
  have hprod : Integrable
      (fun p : ComplexVector n × ℝ => F (x + Complex.exp (p.2 * Complex.I) • p.1))
      ((volume.restrict K).prod (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi)))) := by
    rw [Measure.prod_restrict]
    have hc : Continuous
        (fun p : ComplexVector n × ℝ => F (x + Complex.exp (p.2 * Complex.I) • p.1)) := by
      fun_prop
    exact (hc.continuousOn.integrableOn_compact
      ((isCompact_closedBall 0 r).prod isCompact_Icc)).mono_set
        (Set.prod_mono Subset.rfl Ioc_subset_Icc_self)
  have hi : IntegrableOn
      (fun v => circleAverage (fun θ => F (x + Complex.exp (θ * Complex.I) • v))) K volume := by
    simpa only [IntegrableOn, circleAverage, intervalIntegral.integral_of_le
      (by positivity : (0 : ℝ) ≤ 2 * Real.pi)] using
        hprod.integral_prod_left.const_mul ((2 * Real.pi)⁻¹)
  refine ⟨hi, ?_⟩
  have hswap :
      (∫ v in K, circleAverage (fun θ => F (x + Complex.exp (θ * Complex.I) • v))) =
        circleAverage (fun θ => ∫ v in K, F (x + Complex.exp (θ * Complex.I) • v)) := by
    simp only [circleAverage, intervalIntegral.integral_of_le
      (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
    rw [integral_const_mul, integral_integral_swap hprod]
  rw [hswap]
  have heq (θ : ℝ) : (∫ v in K, F (x + Complex.exp (θ * Complex.I) • v)) =
      ∫ y in Metric.closedBall x r, F y :=
    (integral_closedBall_rotate F x r θ).trans (integral_closedBall_add F x r)
  simp_rw [heq]
  exact circleAverage_const _

/-- Averaging the complex-line submean over a rotation-invariant real ball
gives the genuine real-volume submean in every complex dimension. -/
theorem continuous_majorant_closedBall_submean
    {Ω : Set (ComplexVector n)} {u : ComplexVector n → EReal}
    (hu : IsPshOn u Ω) {x : ComplexVector n} {r q : ℝ}
    (hball : Metric.closedBall x r ⊆ Ω) (hq : (q : EReal) ≤ u x)
    {F : ComplexVector n → ℝ} (hF : Continuous F)
    (hmajor : ∀ y ∈ Metric.closedBall x r, u y ≤ (F y : EReal)) :
    q * volume.real (Metric.closedBall x r) ≤ ∫ y in Metric.closedBall x r, F y := by
  obtain ⟨hi, heq⟩ := integral_circleAverage_closedBall hF x r
  have hmean : ∀ v ∈ Metric.closedBall (0 : ComplexVector n) r,
      q ≤ circleAverage (fun θ => F (x + Complex.exp (θ * Complex.I) • v)) := by
    intro v hv
    have hvnorm : ‖v‖ ≤ r := by simpa only [Metric.mem_closedBall, dist_zero_right] using hv
    have hdisc (ζ : ℂ) (hζ : ‖ζ‖ ≤ 1) : x + ζ • v ∈ Metric.closedBall x r := by
      rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul]
      exact ((mul_le_mul_of_nonneg_right hζ (norm_nonneg v)).trans (by simpa using hvnorm))
    apply EReal.coe_le_coe_iff.mp
    apply hq.trans
    apply hu.2.2 x v (fun ζ hζ => hball (hdisc ζ hζ))
      (fun θ => F (x + Complex.exp (θ * Complex.I) • v))
      (by fun_prop)
    exact fun θ => hmajor _ (hdisc _ (by simp))
  calc
    q * volume.real (Metric.closedBall x r) = ∫ y in Metric.closedBall x r, q := by
      rw [setIntegral_const, smul_eq_mul, mul_comm]
    _ = ∫ v in Metric.closedBall (0 : ComplexVector n) r, q :=
      (integral_closedBall_add (fun _ => q) x r).symm
    _ ≤ ∫ v in Metric.closedBall (0 : ComplexVector n) r,
        circleAverage (fun θ => F (x + Complex.exp (θ * Complex.I) • v)) :=
      setIntegral_mono_on (integrableOn_const (isCompact_closedBall 0 r).measure_lt_top.ne)
        hi measurableSet_closedBall hmean
    _ = _ := heq

/-- The real-ball submean holds for finite lower truncations without an
integrability assumption on the original psh function. -/
theorem lowerTrunc_closedBall_submean
    {Ω : Set (ComplexVector n)} {u : ComplexVector n → EReal}
    (hu : IsPshOn u Ω) {x : ComplexVector n} {r q : ℝ} (hr : 0 ≤ r)
    (hball : Metric.closedBall x r ⊆ Ω) (hq : (q : EReal) ≤ u x) (k : ℕ) :
    q * volume.real (Metric.closedBall x r) ≤ ∫ y in Metric.closedBall x r, lowerTrunc u k y := by
  let K : Set (ComplexVector n) := Metric.closedBall x r
  have hK : IsCompact K := isCompact_closedBall x r
  have hx : x ∈ K := Metric.mem_closedBall_self hr
  obtain ⟨C, hC⟩ := compact_upper_bound hK (hu.2.1.mono hball)
    (fun y hy => hu.1 y (hball hy))
  let B : ℝ := max C 0
  have hB0 : 0 ≤ B := le_max_right _ _
  have hB : ∀ y ∈ K, u y ≤ (B : EReal) := fun y hy =>
    (hC y hy).trans (EReal.coe_le_coe_iff.mpr (le_max_left C 0))
  let v : ComplexVector n → EReal := fun y => (lowerTrunc u k y : EReal)
  have hv : IsPshOn v Ω := isPshOn_lowerTrunc hu k
  have hvB : ∀ y ∈ K, v y ≤ (B : EReal) := fun y hy =>
    EReal.coe_le_coe_iff.mpr (lowerTrunc_le k (hB y hy)
      ((neg_nonpos.mpr (Nat.cast_nonneg k)).trans hB0))
  have hfinite : ∀ᵐ y ∂volume.restrict K, v y ≠ ⊥ ∧ v y ≠ ⊤ :=
    Filter.Eventually.of_forall fun _ => ⟨(EReal.bot_lt_coe _).ne', (EReal.coe_lt_top _).ne⟩
  have hi : IntegrableOn (fun y => (v y).toReal) K volume := by
    simpa only [v, EReal.toReal_coe] using
      integrableOn_lowerTrunc volume hK.measurableSet hK.measure_lt_top
        (hu.2.1.mono hball) hB k
  have hconv := tendsto_integral_majorantEnvelope volume hK.measurableSet hK.measure_lt_top
    ⟨x, hx⟩ hB0 hvB (hv.2.1.mono hball) hfinite hi
  apply ge_of_tendsto (by simpa only [v, EReal.toReal_coe] using hconv)
  apply Filter.Eventually.of_forall
  intro j
  exact continuous_majorant_closedBall_submean hv hball
    (hq.trans (le_coe_lowerTrunc k (hu.1 x (hball hx))))
    (majorantEnvelope_lipschitz ⟨x, hx⟩ hB0 hvB j).continuous
    (fun y hy => le_coe_majorantEnvelope hB0 hvB j hy)

/-- The lower anchor gives a uniform bound for the truncated negative parts
on a genuine real ball. The bound is independent of the truncation level. -/
theorem lowerTrunc_closedBall_deficit_bound
    {Ω : Set (ComplexVector n)} {u : ComplexVector n → EReal}
    (hu : IsPshOn u Ω) {x : ComplexVector n} {r q B : ℝ} (hr : 0 ≤ r)
    (hball : Metric.closedBall x r ⊆ Ω) (hq : (q : EReal) ≤ u x)
    (hB0 : 0 ≤ B) (hB : ∀ y ∈ Metric.closedBall x r, u y ≤ (B : EReal)) (k : ℕ) :
    (∫⁻ y in Metric.closedBall x r, ENNReal.ofReal (B - lowerTrunc u k y)) ≤
      ENNReal.ofReal ((B - q) * volume.real (Metric.closedBall x r)) := by
  have hK : IsCompact (Metric.closedBall x r) := isCompact_closedBall x r
  have hi := integrableOn_lowerTrunc volume hK.measurableSet hK.measure_lt_top
    (hu.2.1.mono hball) hB k
  have hconst : IntegrableOn (fun _ : ComplexVector n => B) (Metric.closedBall x r) volume :=
    integrableOn_const hK.measure_lt_top.ne
  have hnn : ∀ᵐ y ∂volume.restrict (Metric.closedBall x r), 0 ≤ B - lowerTrunc u k y := by
    filter_upwards [ae_restrict_mem hK.measurableSet] with y hy
    exact sub_nonneg.mpr (lowerTrunc_le k (hB y hy)
      ((neg_nonpos.mpr (Nat.cast_nonneg k)).trans hB0))
  have heq : ENNReal.ofReal (∫ y in Metric.closedBall x r, B - lowerTrunc u k y) =
      ∫⁻ y in Metric.closedBall x r, ENNReal.ofReal (B - lowerTrunc u k y) :=
    ofReal_integral_eq_lintegral_ofReal (hconst.sub hi) hnn
  have hid : (∫ y in Metric.closedBall x r, B - lowerTrunc u k y) =
      volume.real (Metric.closedBall x r) * B - ∫ y in Metric.closedBall x r, lowerTrunc u k y := by
    calc
      _ = (∫ _ in Metric.closedBall x r, B) -
          ∫ y in Metric.closedBall x r, lowerTrunc u k y := integral_sub hconst hi
      _ = _ := by rw [setIntegral_const, smul_eq_mul]
  rw [← heq, hid]
  apply ENNReal.ofReal_le_ofReal
  have hmean := lowerTrunc_closedBall_submean hu hr hball hq k
  nlinarith

/-- A finite point anchor produces actual finite-a.e. local L¹ data on every
closed ball about it lying in the psh domain, in arbitrary complex dimension. -/
theorem finiteL1_on_closedBall_of_anchor
    {Ω : Set (ComplexVector n)} {u : ComplexVector n → EReal}
    (hu : IsPshOn u Ω) {x : ComplexVector n} {r q : ℝ} (hr : 0 ≤ r)
    (hball : Metric.closedBall x r ⊆ Ω) (hq : (q : EReal) ≤ u x) :
    (∀ᵐ y ∂volume.restrict (Metric.closedBall x r), u y ≠ ⊥ ∧ u y ≠ ⊤) ∧
      IntegrableOn (fun y => (u y).toReal) (Metric.closedBall x r) volume := by
  have hK : IsCompact (Metric.closedBall x r) := isCompact_closedBall x r
  obtain ⟨C, hC⟩ := compact_upper_bound hK (hu.2.1.mono hball)
    (fun y hy => hu.1 y (hball hy))
  let B : ℝ := max C 0
  have hB0 : 0 ≤ B := le_max_right _ _
  have hB : ∀ y ∈ Metric.closedBall x r, u y ≤ (B : EReal) := fun y hy =>
    (hC y hy).trans (EReal.coe_le_coe_iff.mpr (le_max_left C 0))
  exact finiteL1_of_truncation_deficit_bound volume hK.measurableSet hK.measure_lt_top
    (hu.2.1.mono hball) hB ENNReal.ofReal_ne_top
    (lowerTrunc_closedBall_deficit_bound hu hr hball hq hB0 hB)

end Yau.Proofs.D04Aux
