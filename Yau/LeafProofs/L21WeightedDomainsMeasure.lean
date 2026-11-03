import Yau.LeafProofs.L21BoundaryWeight
import Yau.LeafProofs.L21LocalWeakGain
import Yau.LeafProofs.L21WeightedBasicIdentity

open MeasureTheory Filter Set
open scoped Topology ContDiff ENNReal
noncomputable section
namespace Yau.LeafProofs.L21Aux

variable {n : ℕ}

def weightedBallDensity (K : ℝ) (x : X n) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-boundaryWeight K x))

def weightedBallMeasure (n : ℕ) (K : ℝ) : Measure (X n) :=
  ((Yau.lebesgueC n).restrict (Metric.ball 0 1)).withDensity (weightedBallDensity K)

abbrev WeightedScalar (n : ℕ) (K : ℝ) := Lp ℂ 2 (weightedBallMeasure n K)
abbrev WeightedOneForm (n : ℕ) (K : ℝ) := Lp (X n) 2 (weightedBallMeasure n K)
abbrev WeightedTwoForm (n : ℕ) (K : ℝ) :=
  Lp (EuclideanSpace ℂ (Fin n × Fin n)) 2 (weightedBallMeasure n K)

theorem measurable_weightedBallDensity (K : ℝ) : Measurable (weightedBallDensity (n := n) K) := by
  exact ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
    ((measurable_const.div contDiff_rho.continuous.measurable).neg))

theorem weightedBallDensity_ne_zero (K : ℝ) (x : X n) : weightedBallDensity K x ≠ 0 := by
  exact (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'

theorem weightedBallMeasure_ae_iff (K : ℝ) (P : X n → Prop) :
    (∀ᵐ x ∂weightedBallMeasure n K, P x) ↔
      ∀ᵐ x ∂(Yau.lebesgueC n).restrict (Metric.ball 0 1), P x := by
  change (∀ᵐ x ∂((Yau.lebesgueC n).restrict (Metric.ball 0 1)).withDensity
    (weightedBallDensity K), P x) ↔ _
  exact (ae_withDensity_iff (measurable_weightedBallDensity K)).trans (by
    constructor
    · intro h
      filter_upwards [h] with x hx
      exact hx (weightedBallDensity_ne_zero K x)
    · intro h
      filter_upwards [h] with x hx
      exact fun _ => hx)

theorem weightedBallMeasure_le_restrict (K : ℝ) (hK : 0 ≤ K) :
    weightedBallMeasure n K ≤ (Yau.lebesgueC n).restrict (Metric.ball 0 1) := by
  have h := withDensity_mono (μ := (Yau.lebesgueC n).restrict (Metric.ball 0 1))
    (f := weightedBallDensity K) (g := fun _ => (1 : ℝ≥0∞)) (by
      filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx
      have hp : 0 ≤ boundaryWeight K x := div_nonneg hK (rho_pos hx).le
      have he : Real.exp (-boundaryWeight K x) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
      simpa only [weightedBallDensity,ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal he)
  simpa only [weightedBallMeasure,withDensity_const,one_smul] using h

/-- The density has a genuine positive lower bound on each compact subset
of the ball. No global lower bound near the true boundary is claimed. -/
theorem exists_compact_measure_le_weightedBall (K : ℝ) {S : Set (X n)}
    (hS : IsCompact S) (hSB : S ⊆ Metric.ball 0 1) :
    ∃ C : ℝ≥0∞, C ≠ (⊤ : ℝ≥0∞) ∧ (Yau.lebesgueC n).restrict S ≤ C • weightedBallMeasure n K := by
  obtain ⟨R,hR⟩ := hS.bddAbove_image ((contDiffOn_boundaryWeight K).continuousOn.mono hSB)
  let C : ℝ≥0∞ := ENNReal.ofReal (Real.exp R)
  refine ⟨C,ENNReal.ofReal_ne_top,?_⟩
  have hRestrict : (Yau.lebesgueC n).restrict S =
      ((Yau.lebesgueC n).restrict (Metric.ball 0 1)).withDensity (S.indicator 1) := by
    rw [withDensity_indicator_one hS.measurableSet,Measure.restrict_restrict hS.measurableSet,
      inter_eq_left.mpr hSB]
  rw [hRestrict,weightedBallMeasure,← withDensity_smul C (measurable_weightedBallDensity K)]
  apply withDensity_mono
  filter_upwards [] with x
  by_cases hx : x ∈ S
  · have hxR : boundaryWeight K x ≤ R := hR (mem_image_of_mem _ hx)
    have he : 1 ≤ Real.exp R*Real.exp (-boundaryWeight K x) := by
      rw [← Real.exp_add]
      exact Real.one_le_exp_iff.mpr (by linarith)
    simpa only [indicator_of_mem hx,Pi.one_apply,Pi.smul_apply,smul_eq_mul,C,
      weightedBallDensity,ENNReal.ofReal_mul (Real.exp_nonneg _),ENNReal.ofReal_one] using
      ENNReal.ofReal_le_ofReal he
  · simp only [indicator_of_notMem hx]
    exact zero_le

theorem weightedBall_memLp_restrict_compact {V : Type*} [NormedAddCommGroup V]
    (K : ℝ) {u : X n → V} (hu : MemLp u 2 (weightedBallMeasure n K))
    {S : Set (X n)} (hS : IsCompact S) (hSB : S ⊆ Metric.ball 0 1) :
    MemLp u 2 ((Yau.lebesgueC n).restrict S) := by
  obtain ⟨C,hC,hMeasure⟩ := exists_compact_measure_le_weightedBall K hS hSB
  exact hu.of_measure_le_smul hC hMeasure

theorem locallyL2On_of_weightedBall_memLp (K : ℝ) {u : X n → ℂ}
    (hu : MemLp u 2 (weightedBallMeasure n K)) : LocallyL2On u (Metric.ball 0 1) := by
  intro S hS hSB
  exact weightedBall_memLp_restrict_compact K hu hS hSB

theorem weightedScalar_locallyL2On (K : ℝ) (u : WeightedScalar n K) :
    LocallyL2On (u : X n → ℂ) (Metric.ball 0 1) :=
  locallyL2On_of_weightedBall_memLp K (Lp.memLp u)


/-- Quotient equality for the weighted Hilbert space has its exact
unweighted almost-everywhere meaning inside the ball. -/
theorem weightedBall_ae_eq_iff (K : ℝ) {V : Type*} (u v : X n → V) :
    u =ᵐ[weightedBallMeasure n K] v ↔
      u =ᵐ[(Yau.lebesgueC n).restrict (Metric.ball 0 1)] v :=
  weightedBallMeasure_ae_iff K (fun x => u x = v x)

theorem weightedOneForm_component_locallyL2On (K : ℝ) (v : WeightedOneForm n K) (j : Fin n) :
    LocallyL2On (fun x => v x j) (Metric.ball 0 1) :=
  locallyL2On_of_weightedBall_memLp K ((Lp.memLp v).eval_piLp j)

theorem weightedTwoForm_component_locallyL2On (K : ℝ) (v : WeightedTwoForm n K)
    (i j : Fin n) : LocallyL2On (fun x => v x (i,j)) (Metric.ball 0 1) :=
  locallyL2On_of_weightedBall_memLp K ((Lp.memLp v).eval_piLp (i,j))

theorem compactTest_weightedBall_memLp (K : ℝ) (hK : 0 ≤ K)
    (ψ : CompactTest (Metric.ball (0 : X n) 1)) :
    MemLp (ψ : X n → ℂ) 2 (weightedBallMeasure n K) := by
  letI : IsLocallyFiniteMeasure (Yau.lebesgueC n) := by
    rw [Yau.LeafProofs.lebesgueC_eq_volume]
    infer_instance
  exact (ψ.property.1.continuous.memLp_of_hasCompactSupport ψ.property.2.1).mono_measure
    ((weightedBallMeasure_le_restrict K hK).trans Measure.restrict_le_self)

def compactToWeightedScalar (K : ℝ) (hK : 0 ≤ K)
    (ψ : CompactTest (Metric.ball (0 : X n) 1)) : WeightedScalar n K :=
  (compactTest_weightedBall_memLp K hK ψ).toLp ψ

theorem compactToWeightedScalar_coeFn (K : ℝ) (hK : 0 ≤ K)
    (ψ : CompactTest (Metric.ball (0 : X n) 1)) :
    (compactToWeightedScalar K hK ψ : X n → ℂ) =ᵐ[weightedBallMeasure n K] ψ :=
  (compactTest_weightedBall_memLp K hK ψ).coeFn_toLp

/-- This is the literal density change of measure, with no boundedness
assumption at the true boundary. -/
theorem integral_weightedBallMeasure {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (K : ℝ) (f : X n → V) :
    (∫ x, f x ∂weightedBallMeasure n K) =
      ∫ x in Metric.ball (0 : X n) 1, Real.exp (-boundaryWeight K x) • f x ∂Yau.lebesgueC n := by
  rw [weightedBallMeasure,integral_withDensity_eq_integral_toReal_smul
    (measurable_weightedBallDensity K) (by
      filter_upwards [] with x
      exact ENNReal.ofReal_lt_top)]
  simp only [weightedBallDensity,ENNReal.toReal_ofReal (Real.exp_nonneg _)]

theorem compactToWeightedScalar_norm_sq (K : ℝ) (hK : 0 ≤ K)
    (ψ : CompactTest (Metric.ball (0 : X n) 1)) :
    ‖compactToWeightedScalar K hK ψ‖^2 = weightedScalarEnergy (boundaryWeight K) ψ := by
  rw [compactToWeightedScalar,complex_toLp_norm_sq,integral_weightedBallMeasure]
  change (∫ x in Metric.ball (0 : X n) 1,
    Real.exp (-boundaryWeight K x)*‖ψ x‖^2 ∂Yau.lebesgueC n) = _
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
    have hz : ψ x = 0 := image_eq_zero_of_notMem_tsupport (fun hh => hx (ψ.property.2.2 hh))
    simp only [hz,norm_zero,zero_pow (by decide : 2 ≠ 0),mul_zero])]
  apply integral_congr_ae
  filter_upwards [] with x
  exact mul_comm _ _

end Yau.LeafProofs.L21Aux
