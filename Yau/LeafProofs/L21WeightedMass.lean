import Yau.LeafProofs.L21WeightedDomainsMeasure
import Yau.LeafProofs.L21QuantitativeWeakC1

/-! Actual weighted small norms control the original unweighted inner
mass, and the literal rho-scaled graph-column source has a small norm. -/

open MeasureTheory Filter
open scoped ContDiff
noncomputable section
namespace Yau.LeafProofs.L21Aux

variable {n : ℕ}

theorem compact_closure_ball (r : ℝ) : IsCompact (closure (Metric.ball (0 : X n) r)) :=
  (isCompact_closedBall (0 : X n) r).of_isClosed_subset isClosed_closure
    (closure_minimal Metric.ball_subset_closedBall Metric.isClosed_closedBall)

theorem closure_ball_subset_ball_of_lt {r R : ℝ} (h : r < R) :
    closure (Metric.ball (0 : X n) r) ⊆ Metric.ball (0 : X n) R :=
  (closure_minimal Metric.ball_subset_closedBall Metric.isClosed_closedBall).trans
    (Metric.closedBall_subset_ball h)

theorem exists_weighted_inner_mass_constant (K : ℝ) {O : Set (X n)}
    (hcO : IsCompact (closure O)) (hOB : closure O ⊆ Metric.ball (0 : X n) 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : X n → ℂ, MemLp u 2 (weightedBallMeasure n K) →
      MemLp u 2 ((Yau.lebesgueC n).restrict O) ∧
      (∫ x in O, ‖u x‖ ^ 2 ∂Yau.lebesgueC n) ≤
        C * ∫ x, ‖u x‖ ^ 2 ∂weightedBallMeasure n K := by
  obtain ⟨C, hC, hMeasure⟩ := exists_compact_measure_le_weightedBall K hcO hOB
  have hMeasureO : (Yau.lebesgueC n).restrict O ≤ C • weightedBallMeasure n K :=
    (Measure.restrict_mono subset_closure le_rfl).trans hMeasure
  refine ⟨C.toReal + 1, by positivity, ?_⟩
  intro u hu
  refine ⟨hu.of_measure_le_smul hC hMeasureO, ?_⟩
  have hh := integral_mono_measure hMeasureO (Eventually.of_forall fun x => sq_nonneg ‖u x‖)
    ((hu.smul_measure hC).integrable_norm_pow (p := 2) (by decide))
  rw [integral_smul_measure, smul_eq_mul] at hh
  exact hh.trans (mul_le_mul_of_nonneg_right (by linarith)
    (integral_nonneg fun x => sq_nonneg ‖u x‖))

theorem weighted_source_column_bound (K : ℝ) (hK : 0 ≤ K)
    {A : X n → Matrix (Fin n) (Fin n) ℂ} (hA : MatrixSmoothOn A (Metric.ball (0 : X n) 1))
    {δ : ℝ} (hδ : 0 ≤ δ) (hJet : JetBound 0 δ A (Metric.ball 0 1)) (k : Fin n) :
    (∀ j, MemLp (fun x => (rho x : ℂ) * A x j k) 2 (weightedBallMeasure n K)) ∧
      (∑ j, ∫ x, ‖(rho x : ℂ) * A x j k‖ ^ 2 ∂weightedBallMeasure n K) ≤
        (n : ℝ) * (∫ x in Metric.ball (0 : X n) 1, (1 : ℝ) ∂Yau.lebesgueC n) * δ ^ 2 := by
  have hColumn (j : Fin n) := bounded_local_scalar_energy Metric.isOpen_ball (compact_closure_ball 1)
    (fun x => (rho x : ℂ) * A x j k)
    ((Complex.ofRealCLM.contDiff.comp contDiff_rho).continuous.continuousOn.mul (hA j k).continuousOn) hδ
    (fun x hx => by
      have hr := rho_pos hx
      have ha : ‖A x j k‖ ≤ δ := by simpa only [norm_iteratedFDeriv_zero] using hJet 0 le_rfl x hx j k
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
      exact (mul_le_mul_of_nonneg_right (rho_le_one x) (norm_nonneg _)).trans
        ((one_mul _).le.trans ha))
  have hMeasure := weightedBallMeasure_le_restrict (n := n) K hK
  refine ⟨fun j => (hColumn j).1.mono_measure hMeasure, ?_⟩
  have hOne (j : Fin n) : (∫ x, ‖(rho x : ℂ) * A x j k‖ ^ 2 ∂weightedBallMeasure n K) ≤
      δ ^ 2 * ∫ x in Metric.ball (0 : X n) 1, (1 : ℝ) ∂Yau.lebesgueC n :=
    (integral_mono_measure hMeasure (Eventually.of_forall fun x => sq_nonneg _)
      ((hColumn j).1.integrable_norm_pow (p := 2) (by decide))).trans (hColumn j).2
  exact (Finset.sum_le_sum fun j (_ : j ∈ (Finset.univ : Finset (Fin n))) => hOne j).trans_eq (by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring)

end Yau.LeafProofs.L21Aux
