import Yau.LeafProofs.L21ColumnCoordinates

/-! With a dimension-dependent jet tolerance fixed first, genuine small
weighted column solutions produce actual smooth graph coordinates close to id. -/

open MeasureTheory
open scoped ContDiff
noncomputable section
namespace Yau.LeafProofs.L21Aux

variable {n : ℕ}

theorem exists_small_weighted_column_coordinates (K : ℝ) (hK : 0 ≤ K) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ (A : X n → Matrix (Fin n) (Fin n) ℂ), MatrixSmoothOn A (Metric.ball (0 : X n) 1) →
      (∀ x ∈ Metric.ball (0 : X n) 1, Yau.LeafCandidates.matrixOpNorm (A x) ≤ 1 / 2) →
      JetBound (realDimension n + 1) 1 A (Metric.ball 0 1) →
      JetBound (realDimension n + 1) δ A (Metric.ball 0 1) →
      (∀ k : Fin n, ∃ u : X n → ℂ, MemLp u 2 (weightedBallMeasure n K) ∧
        DbarWeakOn A u (fun x i => A x i k) (Metric.ball 0 1) ∧
        (∫ x, ‖u x‖ ^ 2 ∂weightedBallMeasure n K) ≤
          (∑ j, ∫ x, ‖(rho x : ℂ) * A x j k‖ ^ 2 ∂weightedBallMeasure n K)) →
      ∃ F : X n → X n, ContDiff ℝ ∞ F ∧
        (∀ x ∈ Metric.ball (0 : X n) (1 / 2 : ℝ), ∀ i k,
          dbarA A i (fun y => F y k) x = 0) ∧
        ∀ x ∈ Metric.ball (0 : X n) (1 / 2 : ℝ),
          ‖fderiv ℝ F x - ContinuousLinearMap.id ℝ (X n)‖ ≤ 1 / 4 := by
  classical
  obtain ⟨C, hC, hRegular⟩ := exists_weighted_column_C1_constant (n := n) K hK
  let L : ℝ := C + 1
  let δ : ℝ := 1 / (4 * ((n : ℝ) * L + 1))
  have hL : 0 < L := by dsimp [L]; positivity
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hThreshold : (n : ℝ) * L * δ ≤ 1 / 4 := by
    dsimp only [δ]
    rw [mul_one_div]
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith
  have hCSquare : C ≤ L ^ 2 := by dsimp [L]; nlinarith [sq_nonneg C]
  refine ⟨δ, hδ, ?_⟩
  intro A hA hsmall hJet hSmallJet hSolutions
  have hV (k : Fin n) : ∃ v : X n → ℂ, ContDiff ℝ ∞ v ∧
      v =ᵐ[(Yau.lebesgueC n).restrict (Metric.ball (0 : X n) (1 / 2 : ℝ))]
        (Classical.choose (hSolutions k)) ∧
      (∀ x ∈ Metric.ball (0 : X n) (1 / 2 : ℝ), ∀ i, dbarA A i v x = A x i k) ∧
      ∀ x ∈ Metric.ball (0 : X n) (1 / 2 : ℝ), ‖fderiv ℝ v x‖ ^ 2 ≤ C * δ ^ 2 := by
    have hU := Classical.choose_spec (hSolutions k)
    exact hRegular A hA hsmall hJet δ hδ.le hSmallJet _ hU.1 k hU.2.1 hU.2.2
  choose v hv hAE hEq hBound using hV
  have hNorm (k : Fin n) (x : X n) (hx : x ∈ Metric.ball (0 : X n) (1 / 2 : ℝ)) :
      ‖fderiv ℝ (v k) x‖ ≤ L * δ := by
    have hh : ‖fderiv ℝ (v k) x‖ ^ 2 ≤ (L * δ) ^ 2 :=
      (hBound k x hx).trans ((mul_le_mul_of_nonneg_right hCSquare (sq_nonneg δ)).trans_eq (by ring))
    exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hL.le hδ.le)).mp hh
  refine ⟨correctedCoordinates v, contDiff_correctedCoordinates v hv, ?_, ?_⟩
  · intro x hx i k
    exact correctedCoordinates_dbar_eq_zero v hv A x (fun r s => hEq s x hx r) i k
  · intro x hx
    exact (correctedCoordinates_fderiv_close v hv x (fun k => hNorm k x hx)).trans
      ((show (n : ℝ) * (L * δ) = (n : ℝ) * L * δ by ring).le.trans hThreshold)

end Yau.LeafProofs.L21Aux
