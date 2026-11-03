import Yau.LeafProofs.L21WeightedMass

/-! A genuine small weighted graph-column solution has one smooth
representative with uniformly small actual first derivative on the half ball. -/

open MeasureTheory
open scoped ContDiff
noncomputable section
namespace Yau.LeafProofs.L21Aux

variable {n : ℕ}

theorem exists_weighted_column_C1_constant (K : ℝ) (hK : 0 ≤ K) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (A : X n → Matrix (Fin n) (Fin n) ℂ), MatrixSmoothOn A (Metric.ball (0 : X n) 1) →
      (∀ x ∈ Metric.ball (0 : X n) 1, Yau.LeafCandidates.matrixOpNorm (A x) ≤ 1 / 2) →
      JetBound (realDimension n + 1) 1 A (Metric.ball 0 1) →
      ∀ δ : ℝ, 0 ≤ δ → JetBound (realDimension n + 1) δ A (Metric.ball 0 1) →
      ∀ (u : X n → ℂ), MemLp u 2 (weightedBallMeasure n K) → ∀ k : Fin n,
      DbarWeakOn A u (fun x i => A x i k) (Metric.ball 0 1) →
      (∫ x, ‖u x‖ ^ 2 ∂weightedBallMeasure n K) ≤
        (∑ j, ∫ x, ‖(rho x : ℂ) * A x j k‖ ^ 2 ∂weightedBallMeasure n K) →
      ∃ v : X n → ℂ, ContDiff ℝ ∞ v ∧
        v =ᵐ[(Yau.lebesgueC n).restrict (Metric.ball (0 : X n) (1 / 2 : ℝ))] u ∧
        (∀ x ∈ Metric.ball (0 : X n) (1 / 2 : ℝ), ∀ i, dbarA A i v x = A x i k) ∧
        ∀ x ∈ Metric.ball (0 : X n) (1 / 2 : ℝ), ‖fderiv ℝ v x‖ ^ 2 ≤ C * δ ^ 2 := by
  let O := Metric.ball (0 : X n) (3 / 4 : ℝ)
  let R := Metric.ball (0 : X n) (1 / 2 : ℝ)
  have hOB : closure O ⊆ Metric.ball (0 : X n) 1 := closure_ball_subset_ball_of_lt (by norm_num)
  have hRO : closure R ⊆ O := closure_ball_subset_ball_of_lt (by norm_num)
  have hOB0 : O ⊆ Metric.ball (0 : X n) 1 := subset_closure.trans hOB
  obtain ⟨CM, hCM, hMass⟩ := exists_weighted_inner_mass_constant K (compact_closure_ball (3 / 4)) hOB
  obtain ⟨C1, hC1, hRegular⟩ := exists_inner_smooth_column_with_C1
    (O := O) (R := R) Metric.isOpen_ball Metric.isOpen_ball (compact_closure_ball (1 / 2)) hRO
  let V : ℝ := (n : ℝ) * ∫ x in Metric.ball (0 : X n) 1, (1 : ℝ) ∂Yau.lebesgueC n
  have hV : 0 ≤ V := mul_nonneg (Nat.cast_nonneg _) (integral_nonneg fun x => by norm_num)
  refine ⟨C1 * (CM * V + 1) + 1, by positivity, ?_⟩
  intro A hA hsmall hJet δ hδ hSmallJet u hu k heq hSmallU
  have hSource := (weighted_source_column_bound K hK hA hδ
    (jetBound_mono_order (Nat.zero_le _) hSmallJet) k).2
  have hMassU := hMass u hu
  have hMassBound : (∫ x in O, ‖u x‖ ^ 2 ∂Yau.lebesgueC n) ≤ CM * V * δ ^ 2 := by
    apply hMassU.2.trans
    exact (mul_le_mul_of_nonneg_left (hSmallU.trans hSource) hCM.le).trans_eq (by dsimp [V]; ring)
  obtain ⟨v, hv, hAE, hvEq, hvBound⟩ := hRegular A (fun i j => (hA i j).mono hOB0)
    (fun x hx => hsmall x (hOB0 hx)) (jetBound_mono_domain hOB0 hJet) δ hδ
    (jetBound_mono_domain hOB0 hSmallJet) u hMassU.1 k (dbarWeakOn_mono heq hOB0)
  refine ⟨v, hv, hAE, hvEq, ?_⟩
  intro x hx
  calc
    _ ≤ C1 * ((∫ y in O, ‖u y‖ ^ 2 ∂Yau.lebesgueC n) + δ ^ 2) := hvBound x hx
    _ ≤ C1 * (CM * V * δ ^ 2 + δ ^ 2) := mul_le_mul_of_nonneg_left
      (add_le_add hMassBound (le_refl _)) hC1.le
    _ = (C1 * (CM * V + 1)) * δ ^ 2 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg δ)

end Yau.LeafProofs.L21Aux
