import Yau.Proofs.F03ComparisonWeightHessian

/-! The amplitude and far threshold are chosen before every point, time and genuine volume. -/
noncomputable section
namespace Yau.Proofs.F03Aux

theorem weightBaseError_nonneg {B : ℝ} (hB : 0 ≤ B) (k : ℕ) : 0 ≤ weightBaseError B k := by
  unfold weightBaseError
  positivity

theorem weightDecayError_nonneg {B A : ℝ} (hB : 0 ≤ B) (hA : 0 ≤ A) : 0 ≤ weightDecayError B A := by
  unfold weightDecayError
  positivity

theorem exists_weight_parameters {B θ : ℝ} (hB : 0 ≤ B) (hθ : 0 < θ) (k : ℕ) :
    ∃ A : ℝ,0 < A ∧ ∃ R : ℝ,1 ≤ R ∧
      ∀ r : ℝ,R ≤ r → weightBaseError B k+weightDecayError B A/r^θ ≤ A := by
  let A := 1+2*weightBaseError B k
  have hBase := weightBaseError_nonneg hB k
  have hA : 0 < A := by dsimp [A];linarith
  have hDecay := weightDecayError_nonneg hB hA.le
  let M := 1+2*weightDecayError B A/A
  have hM : 1 ≤ M := by
    have hh : 0 ≤ 2*weightDecayError B A/A := by positivity
    dsimp [M]
    linarith
  have hM0 : 0 < M := zero_lt_one.trans_le hM
  let R := M^(1/θ)
  have hR : 1 ≤ R := Real.one_le_rpow hM (one_div_nonneg.mpr hθ.le)
  have hRPower : R^θ=M := by
    dsimp [R]
    rw [← Real.rpow_mul hM0.le]
    have hCancel : (1/θ)*θ=1 := by field_simp
    rw [hCancel,Real.rpow_one]
  refine ⟨A,hA,R,hR,fun r hr => ?_⟩
  have hr0 : 0 < r := zero_lt_one.trans_le (hR.trans hr)
  have hrPower : 0 < r^θ := Real.rpow_pos_of_pos hr0 _
  have hLower : M ≤ r^θ := by
    rw [← hRPower]
    exact Real.rpow_le_rpow (zero_le_one.trans hR) hr hθ.le
  have hRate : 2*weightDecayError B A/A ≤ r^θ := by dsimp [M] at hLower;linarith
  have hRate' := (div_le_iff₀ hA).mp hRate
  have hHalf : weightDecayError B A/r^θ ≤ A/2 := (div_le_iff₀ hrPower).mpr (by nlinarith)
  dsimp [A] at hHalf ⊢
  nlinarith

end Yau.Proofs.F03Aux
