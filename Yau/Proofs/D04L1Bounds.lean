import Yau.Proofs.D04BallMean

open MeasureTheory Filter Set
open scoped Topology ENNReal

noncomputable section

namespace Yau.Proofs.D04Aux

open Yau Yau.Blueprint

variable {n : ℕ}

theorem volumeReal_closedBall_eq (x : ComplexVector n) (r : ℝ) :
    volume.real (Metric.closedBall x r) = volume.real (Metric.closedBall (0 : ComplexVector n) r) := by
  have h := integral_closedBall_add (fun _ : ComplexVector n => (1 : ℝ)) x r
  simpa only [setIntegral_const, smul_eq_mul, mul_one] using h.symm

/-- The original potential satisfies the real-volume ball submean, after
finite-a.e. local integrability has been produced from the anchor. -/
theorem closedBall_submean
    {Ω : Set (ComplexVector n)} {u : ComplexVector n → EReal}
    (hu : IsPshOn u Ω) {x : ComplexVector n} {r q : ℝ} (hr : 0 ≤ r)
    (hball : Metric.closedBall x r ⊆ Ω) (hq : (q : EReal) ≤ u x) :
    q * volume.real (Metric.closedBall x r) ≤ ∫ y in Metric.closedBall x r, (u y).toReal := by
  have hK : IsCompact (Metric.closedBall x r) := isCompact_closedBall x r
  obtain ⟨C, hC⟩ := compact_upper_bound hK (hu.2.1.mono hball)
    (fun y hy => hu.1 y (hball hy))
  let B : ℝ := max C 0
  have hB0 : 0 ≤ B := le_max_right _ _
  have hB : ∀ y ∈ Metric.closedBall x r, u y ≤ (B : EReal) := fun y hy =>
    (hC y hy).trans (EReal.coe_le_coe_iff.mpr (le_max_left C 0))
  obtain ⟨hfinite, hi⟩ := finiteL1_on_closedBall_of_anchor hu hr hball hq
  have hx : x ∈ Metric.closedBall x r := Metric.mem_closedBall_self hr
  have hconv := tendsto_integral_majorantEnvelope volume hK.measurableSet hK.measure_lt_top
    ⟨x, hx⟩ hB0 hB (hu.2.1.mono hball) hfinite hi
  apply ge_of_tendsto hconv
  exact Filter.Eventually.of_forall fun j => continuous_majorant_closedBall_submean hu hball hq
    (majorantEnvelope_lipschitz ⟨x, hx⟩ hB0 hB j).continuous
    (fun y hy => le_coe_majorantEnvelope hB0 hB j hy)

/-- A common upper bound and a real point anchor give a quantitative local
L¹ bound for the same original potential, with no truncation dependence. -/
theorem L1_bound_on_closedBall_of_anchor
    {Ω : Set (ComplexVector n)} {u : ComplexVector n → EReal}
    (hu : IsPshOn u Ω) {x : ComplexVector n} {r q B : ℝ} (hr : 0 ≤ r)
    (hball : Metric.closedBall x r ⊆ Ω) (hq : (q : EReal) ≤ u x)
    (hB0 : 0 ≤ B) (hB : ∀ y ∈ Metric.closedBall x r, u y ≤ (B : EReal)) :
    (∫ y in Metric.closedBall x r, |(u y).toReal|) ≤
      (2 * B - q) * volume.real (Metric.closedBall x r) := by
  have hK : IsCompact (Metric.closedBall x r) := isCompact_closedBall x r
  obtain ⟨hfinite, hi⟩ := finiteL1_on_closedBall_of_anchor hu hr hball hq
  have hconst : IntegrableOn (fun _ : ComplexVector n => 2 * B) (Metric.closedBall x r) volume :=
    integrableOn_const hK.measure_lt_top.ne
  have hpoint : ∀ᵐ y ∂volume.restrict (Metric.closedBall x r),
      |(u y).toReal| ≤ 2 * B - (u y).toReal := by
    filter_upwards [hfinite, ae_restrict_mem hK.measurableSet] with y hy hyK
    have hyB : (u y).toReal ≤ B := by
      apply EReal.coe_le_coe_iff.mp
      rw [EReal.coe_toReal hy.2 hy.1]
      exact hB y hyK
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hupper : (∫ y in Metric.closedBall x r, |(u y).toReal|) ≤
      ∫ y in Metric.closedBall x r, 2 * B - (u y).toReal := by
    exact integral_mono_ae hi.norm (hconst.sub hi) hpoint
  calc
    _ ≤ ∫ y in Metric.closedBall x r, 2 * B - (u y).toReal := hupper
    _ = volume.real (Metric.closedBall x r) * (2 * B) -
        ∫ y in Metric.closedBall x r, (u y).toReal := by
      calc
        _ = (∫ _ in Metric.closedBall x r, 2 * B) -
            ∫ y in Metric.closedBall x r, (u y).toReal := integral_sub hconst hi
        _ = _ := by rw [setIntegral_const, smul_eq_mul]
    _ ≤ _ := by
      have hm := closedBall_submean hu hr hball hq
      nlinarith

/-- Lower anchors moving in an inner ball produce uniform finite-a.e. L¹
control on that fixed ball. All balls remain in the actual varying domains. -/
theorem uniform_L1_bound_of_moving_anchor
    {Ωs : ℕ → Set (ComplexVector n)} {us : ℕ → ComplexVector n → EReal}
    (hu : ∀ j, IsPshOn (us j) (Ωs j))
    {c : ComplexVector n} {ρ q B : ℝ} (hρ : 0 ≤ ρ)
    (hlarge : ∀ j, Metric.closedBall c (3 * ρ) ⊆ Ωs j)
    (hB0 : 0 ≤ B) (hB : ∀ j y, y ∈ Metric.closedBall c (3 * ρ) → us j y ≤ (B : EReal))
    {z : ℕ → ComplexVector n}
    (hz : ∀ j, z j ∈ Metric.closedBall c ρ ∧ (q : EReal) ≤ us j (z j)) :
    ∀ j,
      (∀ᵐ y ∂volume.restrict (Metric.closedBall c ρ), us j y ≠ ⊥ ∧ us j y ≠ ⊤) ∧
      IntegrableOn (fun y => (us j y).toReal) (Metric.closedBall c ρ) volume ∧
      (∫ y in Metric.closedBall c ρ, |(us j y).toReal|) ≤
        (2 * B - q) * volume.real (Metric.closedBall (0 : ComplexVector n) (2 * ρ)) := by
  intro j
  have hsmall : Metric.closedBall c ρ ⊆ Metric.closedBall (z j) (2 * ρ) := by
    apply Metric.closedBall_subset_closedBall'
    have hzdist := Metric.mem_closedBall.mp (hz j).1
    rw [dist_comm] at hzdist
    linarith
  have hbig : Metric.closedBall (z j) (2 * ρ) ⊆ Metric.closedBall c (3 * ρ) := by
    apply Metric.closedBall_subset_closedBall'
    have hzdist := Metric.mem_closedBall.mp (hz j).1
    linarith
  obtain ⟨hfinite, hi⟩ := finiteL1_on_closedBall_of_anchor (hu j) (by linarith : 0 ≤ 2 * ρ)
    (hbig.trans (hlarge j)) (hz j).2
  refine ⟨ae_restrict_of_ae_restrict_of_subset hsmall hfinite, hi.mono_set hsmall, ?_⟩
  have hmono : (∫ y in Metric.closedBall c ρ, |(us j y).toReal|) ≤
      ∫ y in Metric.closedBall (z j) (2 * ρ), |(us j y).toReal| :=
    setIntegral_mono_set hi.norm (Filter.Eventually.of_forall fun y => abs_nonneg _)
      (Filter.Eventually.of_forall hsmall)
  have hbound := L1_bound_on_closedBall_of_anchor (hu j) (by linarith : 0 ≤ 2 * ρ)
    (hbig.trans (hlarge j)) (hz j).2 hB0 (fun y hy => hB j y (hbig hy))
  exact hmono.trans (by simpa only [volumeReal_closedBall_eq] using hbound)

end Yau.Proofs.D04Aux
