import Yau.Proofs.P06ComplexOperator
import Yau.Proofs.P06PositiveResolvent
import Yau.LeafProofs.L19HeatFamilyDerivative

noncomputable section
open Filter
open scoped Topology InnerProductSpace ContinuousFunctionalCalculus
namespace Yau.NodeProofs.P06Aux.Spectral
open Yau.LeafProofs.L19Aux
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

def complexResolvent (R : H →L[ℝ] H) (_hs : R.IsSymmetric)
    (_hp : ∀ x, 0 ≤ inner ℝ (R x) x) (_hb : ∀ x, ‖R x‖ ≤ ‖x‖) (_hi : Function.Injective R) :
    ComplexHilbert H →L[ℂ] ComplexHilbert H := ComplexHilbert.complexify R

theorem complexResolvent_positive (R : H →L[ℝ] H) (hs : R.IsSymmetric)
    (hp : ∀ x, 0 ≤ inner ℝ (R x) x) (hb : ∀ x, ‖R x‖ ≤ ‖x‖) (hi : Function.Injective R) :
    (complexResolvent R hs hp hb hi).IsPositive := ComplexHilbert.complexify_positive R hs hp

theorem complexResolvent_selfAdjoint (R : H →L[ℝ] H) (hs : R.IsSymmetric)
    (hp : ∀ x, 0 ≤ inner ℝ (R x) x) (hb : ∀ x, ‖R x‖ ≤ ‖x‖) (hi : Function.Injective R) :
    IsSelfAdjoint (complexResolvent R hs hp hb hi) := ComplexHilbert.complexify_selfAdjoint R hs

theorem complexResolvent_norm_le (R : H →L[ℝ] H) (hs : R.IsSymmetric)
    (hp : ∀ x, 0 ≤ inner ℝ (R x) x) (hb : ∀ x, ‖R x‖ ≤ ‖x‖) (hi : Function.Injective R)
    (x : ComplexHilbert H) : ‖complexResolvent R hs hp hb hi x‖ ≤ ‖x‖ :=
  ComplexHilbert.complexify_norm_le R hb x

theorem complexResolvent_opNorm_le (R : H →L[ℝ] H) (hs : R.IsSymmetric)
    (hp : ∀ x, 0 ≤ inner ℝ (R x) x) (hb : ∀ x, ‖R x‖ ≤ ‖x‖) (hi : Function.Injective R) :
    ‖complexResolvent R hs hp hb hi‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simpa only [one_mul] using complexResolvent_norm_le R hs hp hb hi x

theorem complexResolvent_denseRange (R : H →L[ℝ] H) (hs : R.IsSymmetric)
    (hp : ∀ x, 0 ≤ inner ℝ (R x) x) (hb : ∀ x, ‖R x‖ ≤ ‖x‖) (hi : Function.Injective R) :
    DenseRange (complexResolvent R hs hp hb hi) := ComplexHilbert.complexify_denseRange R hs hi

theorem complexResolvent_spectrum (R : H →L[ℝ] H) (hs : R.IsSymmetric)
    (hp : ∀ x, 0 ≤ inner ℝ (R x) x) (hb : ∀ x, ‖R x‖ ≤ ‖x‖) (hi : Function.Injective R) :
    spectrum ℝ (complexResolvent R hs hp hb hi) ⊆ Set.Icc 0 1 := by
  intro s hspectral
  have hpos : 0 ≤ complexResolvent R hs hp hb hi :=
    ContinuousLinearMap.nonneg_iff_isPositive.mpr (complexResolvent_positive R hs hp hb hi)
  refine ⟨spectrum_nonneg_of_nonneg hpos hspectral, ?_⟩
  have hn := spectrum.norm_le_norm_mul_of_mem hspectral
  have hI : ‖(1 : ComplexHilbert H →L[ℂ] ComplexHilbert H)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  have hop := complexResolvent_opNorm_le R hs hp hb hi
  have hmul := mul_le_mul hop hI (norm_nonneg _) zero_le_one
  exact (le_abs_self s).trans (hn.trans (by simpa using hmul))

/-- Positive times use the bounded continuous functional calculus of the fixed
variational resolvent. At zero the operator is the identity. -/
def complexHeat (R : H →L[ℝ] H) (hRs : R.IsSymmetric)
    (hRp : ∀ x, 0 ≤ inner ℝ (R x) x) (hRb : ∀ x, ‖R x‖ ≤ ‖x‖) (hRi : Function.Injective R) (t : ℝ) : ComplexHilbert H →L[ℂ] ComplexHilbert H :=
  if 0 < t then cfc (scalarHeatMultiplier t) (complexResolvent R hRs hRp hRb hRi) else 1

@[simp] theorem complexHeat_zero (R : H →L[ℝ] H) (hRs : R.IsSymmetric)
    (hRp : ∀ x, 0 ≤ inner ℝ (R x) x) (hRb : ∀ x, ‖R x‖ ≤ ‖x‖) (hRi : Function.Injective R) : complexHeat R hRs hRp hRb hRi 0 = 1 := by
  simp [complexHeat]

theorem complexHeat_of_pos (R : H →L[ℝ] H) (hRs : R.IsSymmetric)
    (hRp : ∀ x, 0 ≤ inner ℝ (R x) x) (hRb : ∀ x, ‖R x‖ ≤ ‖x‖) (hRi : Function.Injective R) {t : ℝ} (ht : 0 < t) :
    complexHeat R hRs hRp hRb hRi t = cfc (scalarHeatMultiplier t) (complexResolvent R hRs hRp hRb hRi) := by
  simp [complexHeat, ht]

theorem complexHeat_selfAdjoint (R : H →L[ℝ] H) (hRs : R.IsSymmetric)
    (hRp : ∀ x, 0 ≤ inner ℝ (R x) x) (hRb : ∀ x, ‖R x‖ ≤ ‖x‖) (hRi : Function.Injective R) (t : ℝ) : IsSelfAdjoint (complexHeat R hRs hRp hRb hRi t) := by
  unfold complexHeat
  split_ifs
  · exact IsSelfAdjoint.cfc
  · exact IsSelfAdjoint.one _

theorem complexHeat_opNorm_le (R : H →L[ℝ] H) (hRs : R.IsSymmetric)
    (hRp : ∀ x, 0 ≤ inner ℝ (R x) x) (hRb : ∀ x, ‖R x‖ ≤ ‖x‖) (hRi : Function.Injective R) (t : ℝ) : ‖complexHeat R hRs hRp hRb hRi t‖ ≤ 1 := by
  unfold complexHeat
  split_ifs with ht
  · apply norm_cfc_le zero_le_one
    intro s hs
    rw [Real.norm_eq_abs, abs_of_nonneg (scalarHeatMultiplier_nonneg t s)]
    exact scalarHeatMultiplier_le_one ht.le (complexResolvent_spectrum R hRs hRp hRb hRi hs).2
  · exact ContinuousLinearMap.norm_id_le

theorem complexHeat_norm_le (R : H →L[ℝ] H) (hRs : R.IsSymmetric)
    (hRp : ∀ x, 0 ≤ inner ℝ (R x) x) (hRb : ∀ x, ‖R x‖ ≤ ‖x‖) (hRi : Function.Injective R) (t : ℝ) (f : ComplexHilbert H) :
    ‖complexHeat R hRs hRp hRb hRi t f‖ ≤ ‖f‖ := by
  calc
    _ ≤ ‖complexHeat R hRs hRp hRb hRi t‖ * ‖f‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ 1 * ‖f‖ := mul_le_mul_of_nonneg_right (complexHeat_opNorm_le R hRs hRp hRb hRi t) (norm_nonneg f)
    _ = _ := one_mul _

theorem complexHeat_add (R : H →L[ℝ] H) (hRs : R.IsSymmetric)
    (hRp : ∀ x, 0 ≤ inner ℝ (R x) x) (hRb : ∀ x, ‖R x‖ ≤ ‖x‖) (hRi : Function.Injective R) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    complexHeat R hRs hRp hRb hRi (s + t) = complexHeat R hRs hRp hRb hRi s * complexHeat R hRs hRp hRb hRi t := by
  rcases hs.eq_or_lt with rfl | hs
  · simp
  rcases ht.eq_or_lt with rfl | ht
  · simp
  rw [complexHeat_of_pos R hRs hRp hRb hRi (add_pos hs ht),
    complexHeat_of_pos R hRs hRp hRb hRi hs, complexHeat_of_pos R hRs hRp hRb hRi ht,
    ← cfc_mul _ _ _ (scalarHeatMultiplier_continuous hs).continuousOn
      (scalarHeatMultiplier_continuous ht).continuousOn]
  apply cfc_congr
  intro x _
  exact scalarHeatMultiplier_add s t x

/-- Uniform weighted initial estimate. It holds despite the multiplier's
failure to converge uniformly to one at spectral zero. -/
theorem complexHeat_initial_opNorm (R : H →L[ℝ] H) (hRs : R.IsSymmetric)
    (hRp : ∀ x, 0 ≤ inner ℝ (R x) x) (hRb : ∀ x, ‖R x‖ ≤ ‖x‖) (hRi : Function.Injective R) {t : ℝ} (ht : 0 ≤ t) :
    ‖(complexHeat R hRs hRp hRb hRi t - 1) * complexResolvent R hRs hRp hRb hRi‖ ≤ t := by
  rcases ht.eq_or_lt with rfl | ht
  · simp
  rw [complexHeat_of_pos R hRs hRp hRb hRi ht]
  have hc := scalarHeatMultiplier_continuous ht
  have hB := complexResolvent_selfAdjoint R hRs hRp hRb hRi
  have heq : (cfc (scalarHeatMultiplier t) (complexResolvent R hRs hRp hRb hRi) - 1) *
      complexResolvent R hRs hRp hRb hRi =
      cfc (fun s => (scalarHeatMultiplier t s - 1) * s) (complexResolvent R hRs hRp hRb hRi) := by
    rw [cfc_mul (fun s : ℝ => scalarHeatMultiplier t s - 1) (fun s : ℝ => s)
      (complexResolvent R hRs hRp hRb hRi) (hc.sub continuous_const).continuousOn continuous_id.continuousOn,
      cfc_sub (f := scalarHeatMultiplier t) (g := fun _ : ℝ => 1) (a := complexResolvent R hRs hRp hRb hRi)
        hc.continuousOn continuous_const.continuousOn,
      cfc_id' ℝ _ hB, cfc_const 1 _ hB, map_one]
  rw [heq]
  apply norm_cfc_le ht.le
  intro s hs
  exact scalarHeatMultiplier_initial_bound ht.le (complexResolvent_spectrum R hRs hRp hRb hRi hs)

/-- Strong initial continuity on the dense resolvent range has an explicit
rate controlled by the preimage norm. -/
theorem complexHeat_initial_range_bound (R : H →L[ℝ] H) (hRs : R.IsSymmetric)
    (hRp : ∀ x, 0 ≤ inner ℝ (R x) x) (hRb : ∀ x, ‖R x‖ ≤ ‖x‖) (hRi : Function.Injective R) {t : ℝ} (ht : 0 ≤ t) (f : ComplexHilbert H) :
    ‖complexHeat R hRs hRp hRb hRi t (complexResolvent R hRs hRp hRb hRi f) -
      complexResolvent R hRs hRp hRb hRi f‖ ≤ t * ‖f‖ := by
  have h := (ContinuousLinearMap.le_opNorm
    ((complexHeat R hRs hRp hRb hRi t - 1) * complexResolvent R hRs hRp hRb hRi) f).trans
    (mul_le_mul_of_nonneg_right (complexHeat_initial_opNorm R hRs hRp hRb hRi ht) (norm_nonneg f))
  simpa only [mul_apply_eq_comp, sub_apply,
    one_apply_eq_self] using h

/-- The fixed CFC family tends strongly to the identity on the full original
complex L² space, by the proved dense range and its contraction bound. -/
theorem complexHeat_tendsto_zero (R : H →L[ℝ] H) (hRs : R.IsSymmetric)
    (hRp : ∀ x, 0 ≤ inner ℝ (R x) x) (hRb : ∀ x, ‖R x‖ ≤ ‖x‖) (hRi : Function.Injective R) (f : ComplexHilbert H) :
    Tendsto (fun t : ℝ => complexHeat R hRs hRp hRb hRi t f) (𝓝[≥] (0 : ℝ)) (𝓝 f) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨v, hv⟩ := (complexResolvent_denseRange R hRs hRp hRb hRi).exists_dist_lt f
    (show 0 < ε / 4 by positivity)
  rw [dist_eq_norm] at hv
  let δ := ε / (2 * (‖v‖ + 1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hevent : ∀ᶠ t : ℝ in 𝓝[≥] (0 : ℝ), t < δ :=
    (eventually_lt_nhds hδ).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hevent] with t ht htδ
  have ht₀ : 0 ≤ t := ht
  have hsmall : t * ‖v‖ < ε / 2 := by
    calc
      t * ‖v‖ ≤ t * (‖v‖ + 1) := mul_le_mul_of_nonneg_left (by linarith) ht₀
      _ < δ * (‖v‖ + 1) := mul_lt_mul_of_pos_right htδ (by positivity)
      _ = ε / 2 := by dsimp [δ]; field_simp
  rw [dist_eq_norm]
  have heq : complexHeat R hRs hRp hRb hRi t f - f =
      complexHeat R hRs hRp hRb hRi t (f - complexResolvent R hRs hRp hRb hRi v) +
        (complexHeat R hRs hRp hRb hRi t (complexResolvent R hRs hRp hRb hRi v) -
          complexResolvent R hRs hRp hRb hRi v) + (complexResolvent R hRs hRp hRb hRi v - f) := by
    simp only [map_sub]
    abel
  rw [heq]
  calc
    _ ≤ ‖complexHeat R hRs hRp hRb hRi t (f - complexResolvent R hRs hRp hRb hRi v)‖ +
        ‖complexHeat R hRs hRp hRb hRi t (complexResolvent R hRs hRp hRb hRi v) -
          complexResolvent R hRs hRp hRb hRi v‖ + ‖complexResolvent R hRs hRp hRb hRi v - f‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) (le_refl _))
    _ ≤ ‖f - complexResolvent R hRs hRp hRb hRi v‖ + t * ‖v‖ +
        ‖complexResolvent R hRs hRp hRb hRi v - f‖ := by
      gcongr
      · exact complexHeat_norm_le R hRs hRp hRb hRi t _
      · exact complexHeat_initial_range_bound R hRs hRp hRb hRi ht₀ v
    _ < ε := by rw [norm_sub_rev (complexResolvent R hRs hRp hRb hRi v) f]; linarith

/-- This is an actual bounded operator defined by the fixed continuous
functional calculus, with no chosen heat-family premise. -/
def complexHeatInverse (R : H →L[ℝ] H) (hRs : R.IsSymmetric)
    (hRp : ∀ x, 0 ≤ inner ℝ (R x) x) (hRb : ∀ x, ‖R x‖ ≤ ‖x‖) (hRi : Function.Injective R) (t : ℝ) : ComplexHilbert H →L[ℂ] ComplexHilbert H :=
  cfc (scalarHeatInverseMultiplier t) (complexResolvent R hRs hRp hRb hRi)

theorem complexHeat_factor (R : H →L[ℝ] H) (hRs : R.IsSymmetric)
    (hRp : ∀ x, 0 ≤ inner ℝ (R x) x) (hRb : ∀ x, ‖R x‖ ≤ ‖x‖) (hRi : Function.Injective R) {t : ℝ} (ht : 0 < t) :
    complexHeat R hRs hRp hRb hRi t = complexResolvent R hRs hRp hRb hRi * complexHeatInverse R hRs hRp hRb hRi t := by
  rw [complexHeat_of_pos R hRs hRp hRb hRi ht, complexHeatInverse]
  calc
    _ = cfc (fun s => s * scalarHeatInverseMultiplier t s) (complexResolvent R hRs hRp hRb hRi) := by
      apply cfc_congr
      intro s _
      exact (scalarHeatInverseMultiplier_mul t s).symm
    _ = cfc (fun s : ℝ => s) (complexResolvent R hRs hRp hRb hRi) *
        cfc (scalarHeatInverseMultiplier t) (complexResolvent R hRs hRp hRb hRi) :=
      cfc_mul _ _ _ continuous_id.continuousOn (scalarHeatInverseMultiplier_continuous ht).continuousOn
    _ = _ := by rw [cfc_id' ℝ _ (complexResolvent_selfAdjoint R hRs hRp hRb hRi)]

/-- Logarithmic time keeps the multiplier inside the positive-time region. -/
def heatLogContinuous (R : H →L[ℝ] H) (hRs : R.IsSymmetric)
    (hRp : ∀ x, 0 ≤ inner ℝ (R x) x) (hRb : ∀ x, ‖R x‖ ≤ ‖x‖) (hRi : Function.Injective R) (a : ℝ) :
    C(spectrum ℝ (complexResolvent R hRs hRp hRb hRi), ℝ) :=
  ⟨fun s => scalarHeatMultiplier (Real.exp a) s,
    (scalarHeatMultiplier_continuous (Real.exp_pos a)).comp continuous_subtype_val⟩

def heatLogInverseContinuous (R : H →L[ℝ] H) (hRs : R.IsSymmetric)
    (hRp : ∀ x, 0 ≤ inner ℝ (R x) x) (hRb : ∀ x, ‖R x‖ ≤ ‖x‖) (hRi : Function.Injective R) (a : ℝ) :
    C(spectrum ℝ (complexResolvent R hRs hRp hRb hRi), ℝ) :=
  ⟨fun s => scalarHeatInverseMultiplier (Real.exp a) s,
    (scalarHeatInverseMultiplier_continuous (Real.exp_pos a)).comp continuous_subtype_val⟩

def heatLogDerivativeContinuous (R : H →L[ℝ] H) (hRs : R.IsSymmetric)
    (hRp : ∀ x, 0 ≤ inner ℝ (R x) x) (hRb : ∀ x, ‖R x‖ ≤ ‖x‖) (hRi : Function.Injective R) (a : ℝ) :
    C(spectrum ℝ (complexResolvent R hRs hRp hRb hRi), ℝ) :=
  Real.exp a • (heatLogContinuous R hRs hRp hRb hRi a - heatLogInverseContinuous R hRs hRp hRb hRi a)

theorem heatLogDerivative_continuous (R : H →L[ℝ] H) (hRs : R.IsSymmetric)
    (hRp : ∀ x, 0 ≤ inner ℝ (R x) x) (hRb : ∀ x, ‖R x‖ ≤ ‖x‖) (hRi : Function.Injective R) : Continuous (heatLogDerivativeContinuous R hRs hRp hRb hRi) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun p : ℝ × spectrum ℝ (complexResolvent R hRs hRp hRb hRi) =>
    Real.exp p.1 * (scalarHeatMultiplier (Real.exp p.1) p.2 - scalarHeatInverseMultiplier (Real.exp p.1) p.2))
  simp_rw [scalarHeatMultiplier_eq_glue (Real.exp_pos _),
    scalarHeatInverseMultiplier_eq_glue (Real.exp_pos _)]
  have hT : Continuous (fun p : ℝ × spectrum ℝ (complexResolvent R hRs hRp hRb hRi) => Real.exp p.1) :=
    Real.continuous_exp.comp continuous_fst
  have hq : Continuous (fun p : ℝ × spectrum ℝ (complexResolvent R hRs hRp hRb hRi) =>
      (p.2 : ℝ) / Real.exp p.1) :=
    (continuous_subtype_val.comp continuous_snd).div hT (fun _ => Real.exp_ne_zero _)
  have hg : Continuous (fun x : ℝ => x⁻¹ * expNegInvGlue x) := by
    simpa only [Polynomial.eval_X] using
      expNegInvGlue.continuous_polynomial_eval_inv_mul (Polynomial.X : Polynomial ℝ)
  exact hT.mul (((Real.continuous_exp.comp hT).mul ((expNegInvGlue.contDiff (n := 0)).continuous.comp hq)).sub
    (((Real.continuous_exp.comp hT).div hT (fun _ => Real.exp_ne_zero _)).mul (hg.comp hq)))

theorem heatLogContinuous_hasDerivAt (R : H →L[ℝ] H) (hRs : R.IsSymmetric)
    (hRp : ∀ x, 0 ≤ inner ℝ (R x) x) (hRb : ∀ x, ‖R x‖ ≤ ‖x‖) (hRi : Function.Injective R) (a : ℝ) :
    HasDerivAt (heatLogContinuous R hRs hRp hRb hRi) (heatLogDerivativeContinuous R hRs hRp hRb hRi a) a := by
  apply heatContinuousMap_hasDerivAt _ _ (heatLogDerivative_continuous R hRs hRp hRb hRi)
  intro b s
  have h := (scalarHeatMultiplier_hasDerivAt (Real.exp b) (s : ℝ)).comp b (Real.hasDerivAt_exp b)
  simpa only [heatLogContinuous, heatLogDerivativeContinuous,
    heatLogInverseContinuous, ContinuousMap.coe_mk, ContinuousMap.smul_apply,
    ContinuousMap.sub_apply, smul_eq_mul, mul_comm, Function.comp_def] using h

theorem heatLog_cfcL (R : H →L[ℝ] H) (hRs : R.IsSymmetric)
    (hRp : ∀ x, 0 ≤ inner ℝ (R x) x) (hRb : ∀ x, ‖R x‖ ≤ ‖x‖) (hRi : Function.Injective R) (a : ℝ) :
    cfcL (complexResolvent_selfAdjoint R hRs hRp hRb hRi) (heatLogContinuous R hRs hRp hRb hRi a) =
      complexHeat R hRs hRp hRb hRi (Real.exp a) := by
  rw [complexHeat_of_pos R hRs hRp hRb hRi (Real.exp_pos a),
    cfc_eq_cfcL (complexResolvent_selfAdjoint R hRs hRp hRb hRi)
      (scalarHeatMultiplier_continuous (Real.exp_pos a)).continuousOn]
  rfl

theorem heatLogInverse_cfcL (R : H →L[ℝ] H) (hRs : R.IsSymmetric)
    (hRp : ∀ x, 0 ≤ inner ℝ (R x) x) (hRb : ∀ x, ‖R x‖ ≤ ‖x‖) (hRi : Function.Injective R) (a : ℝ) :
    cfcL (complexResolvent_selfAdjoint R hRs hRp hRb hRi) (heatLogInverseContinuous R hRs hRp hRb hRi a) =
      complexHeatInverse R hRs hRp hRb hRi (Real.exp a) := by
  rw [complexHeatInverse,
    cfc_eq_cfcL (complexResolvent_selfAdjoint R hRs hRp hRb hRi)
      (scalarHeatInverseMultiplier_continuous (Real.exp_pos a)).continuousOn]
  rfl

theorem heatLogDerivative_cfcL (R : H →L[ℝ] H) (hRs : R.IsSymmetric)
    (hRp : ∀ x, 0 ≤ inner ℝ (R x) x) (hRb : ∀ x, ‖R x‖ ≤ ‖x‖) (hRi : Function.Injective R) (a : ℝ) :
    cfcL (complexResolvent_selfAdjoint R hRs hRp hRb hRi) (heatLogDerivativeContinuous R hRs hRp hRb hRi a) =
      Real.exp a • (complexHeat R hRs hRp hRb hRi (Real.exp a) - complexHeatInverse R hRs hRp hRb hRi (Real.exp a)) := by
  rw [heatLogDerivativeContinuous, map_smul, map_sub, heatLog_cfcL, heatLogInverse_cfcL]

theorem complexHeat_log_hasDerivAt (R : H →L[ℝ] H) (hRs : R.IsSymmetric)
    (hRp : ∀ x, 0 ≤ inner ℝ (R x) x) (hRb : ∀ x, ‖R x‖ ≤ ‖x‖) (hRi : Function.Injective R) (a : ℝ) :
    HasDerivAt (fun b => complexHeat R hRs hRp hRb hRi (Real.exp b))
      (Real.exp a • (complexHeat R hRs hRp hRb hRi (Real.exp a) - complexHeatInverse R hRs hRp hRb hRi (Real.exp a))) a := by
  have h := HasFDerivAt.comp_hasDerivAt
    (𝕜 := ℝ) (F := C(spectrum ℝ (complexResolvent R hRs hRp hRb hRi), ℝ))
    (E := ComplexHilbert H →L[ℂ] ComplexHilbert H)
    (f := heatLogContinuous R hRs hRp hRb hRi) a
    (cfcL (R := ℝ) (complexResolvent_selfAdjoint R hRs hRp hRb hRi)).hasFDerivAt
    (heatLogContinuous_hasDerivAt R hRs hRp hRb hRi a)
  simpa only [Function.comp_def, heatLog_cfcL, heatLogDerivative_cfcL] using h

/-- The time derivative exists in operator norm at every positive time and
is the actual bounded energy factor dictated by the same CFC. -/
theorem complexHeat_hasDerivAt (R : H →L[ℝ] H) (hRs : R.IsSymmetric)
    (hRp : ∀ x, 0 ≤ inner ℝ (R x) x) (hRb : ∀ x, ‖R x‖ ≤ ‖x‖) (hRi : Function.Injective R) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (complexHeat R hRs hRp hRb hRi)
      (complexHeat R hRs hRp hRb hRi t - complexHeatInverse R hRs hRp hRb hRi t) t := by
  have h := (complexHeat_log_hasDerivAt R hRs hRp hRb hRi (Real.log t)).scomp t
    (Real.hasDerivAt_log ht.ne')
  rw [Real.exp_log ht] at h
  have h' : HasDerivAt (fun u => complexHeat R hRs hRp hRb hRi (Real.exp (Real.log u)))
      (complexHeat R hRs hRp hRb hRi t - complexHeatInverse R hRs hRp hRb hRi t) t := by
    simpa only [Function.comp_def, smul_smul, inv_mul_cancel₀ ht.ne', one_smul] using h
  apply h'.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds ht] with u hu
  rw [Real.exp_log hu]


end Yau.NodeProofs.P06Aux.Spectral
