import Yau.LeafProofs.L21ScaledCoreCalculus

/-! Comparison of the genuine unscaled compact form with the exact
rho-scaled Hilbert complex, using the bounded D-rho correction only. -/

open scoped ContDiff
noncomputable section
namespace Yau.LeafProofs.L21Aux

variable {n : ℕ}

theorem scaled_curl_energy_bound
    {A : X n → Matrix (Fin n) (Fin n) ℂ} (hA : MatrixSmoothOn A (Metric.ball (0 : X n) 1))
    (hJet : JetBound 0 1 A (Metric.ball 0 1))
    {φ : X n → ℝ} (hφ : ContDiffOn ℝ ∞ φ (Metric.ball (0 : X n) 1))
    (v : Fin n → CompactTest (Metric.ball (0 : X n) 1)) (i j : Fin n) :
    weightedScalarEnergy φ ((testD Metric.isOpen_ball hA i (testRhoMul Metric.isOpen_ball (v j)) -
      testD Metric.isOpen_ball hA j (testRhoMul Metric.isOpen_ball (v i))) : CompactTest (Metric.ball (0 : X n) 1)) ≤
      2 * weightedScalarEnergy φ (testScaledS Metric.isOpen_ball hA v i j) +
        16 * (8 * (n : ℝ)) ^ 2 * (weightedScalarEnergy φ (v i) + weightedScalarEnergy φ (v j)) := by
  let B : ℝ := 8 * (n : ℝ)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hDρ (x : X n) (hx : x ∈ Metric.ball (0 : X n) 1) (r : Fin n) :
      ‖dbarA A r (fun y => (rho y : ℂ)) x‖ ≤ B :=
    dbarA_rho_norm_le A hx (fun s t => by
      simpa only [norm_iteratedFDeriv_zero] using hJet 0 le_rfl x hx s t) r
  let a (r : Fin n) := contDiffOn_dbarA Metric.isOpen_ball hA r contDiff_complex_rho.contDiffOn
  have hMi := weightedScalarEnergy_multiply_le Metric.isOpen_ball hφ (a i) hB (fun x hx => hDρ x hx i) (v j)
  have hMj := weightedScalarEnergy_multiply_le Metric.isOpen_ball hφ (a j) hB (fun x hx => hDρ x hx j) (v i)
  have hWedge := weightedScalarEnergy_sub_le Metric.isOpen_ball hφ
    (multiplyLocalTest Metric.isOpen_ball (a i) (v j)) (multiplyLocalTest Metric.isOpen_ball (a j) (v i))
  have hW : weightedScalarEnergy φ (testRhoWedge Metric.isOpen_ball hA v i j) ≤
      2 * B ^ 2 * (weightedScalarEnergy φ (v i) + weightedScalarEnergy φ (v j)) := by
    change weightedScalarEnergy φ (testRhoWedge Metric.isOpen_ball hA v i j) ≤ _ at hWedge
    nlinarith
  let two := multiplyLocalTest Metric.isOpen_ball (a := fun _ : X n => (2 : ℂ)) contDiffOn_const
    (testRhoWedge Metric.isOpen_ball hA v i j)
  have hTwo : weightedScalarEnergy φ two ≤ 4 * weightedScalarEnergy φ (testRhoWedge Metric.isOpen_ball hA v i j) := by
    have hh := weightedScalarEnergy_multiply_le Metric.isOpen_ball hφ
      (a := fun _ : X n => (2 : ℂ)) contDiffOn_const (C := 2) (by norm_num)
      (fun x hx => by norm_num) (testRhoWedge Metric.isOpen_ball hA v i j)
    norm_num only [show (2 : ℝ) ^ 2 = 4 by norm_num] at hh
    exact hh
  rw [test_scaled_curl_identity]
  have hAdd := weightedScalarEnergy_add_le Metric.isOpen_ball hφ (testScaledS Metric.isOpen_ball hA v i j) two
  change weightedScalarEnergy φ ((testScaledS Metric.isOpen_ball hA v i j + two) : CompactTest (Metric.ball (0 : X n) 1)) ≤ _
  change weightedScalarEnergy φ ((testScaledS Metric.isOpen_ball hA v i j + two) : CompactTest (Metric.ball (0 : X n) 1)) ≤ _ at hAdd
  dsimp only [B] at hW
  nlinarith

def scaledCoreRemainder (n : ℕ) : ℝ := 16 * (n : ℝ) * (8 * (n : ℝ)) ^ 2

theorem scaledCoreRemainder_nonneg (n : ℕ) : 0 ≤ scaledCoreRemainder n := by unfold scaledCoreRemainder; positivity

theorem compactFormQ_scaled_upper
    {A : X n → Matrix (Fin n) (Fin n) ℂ} (hA : MatrixSmoothOn A (Metric.ball (0 : X n) 1))
    (hJet : JetBound 0 1 A (Metric.ball 0 1))
    {φ : X n → ℝ} (hφ : ContDiffOn ℝ ∞ φ (Metric.ball (0 : X n) 1))
    (v : Fin n → CompactTest (Metric.ball (0 : X n) 1)) :
    compactFormQ Metric.isOpen_ball hA hφ (fun i => testRhoMul Metric.isOpen_ball (v i)) ≤
      weightedScalarEnergy φ (fun x => ∑ i, weightedDStar A φ i (fun y => (rho y : ℂ) * v i y) x) +
        (∑ i, ∑ j, weightedScalarEnergy φ (fun x => degenerateS A (fun y k => v k y) x i j)) +
        scaledCoreRemainder n * coreScalarEnergy φ v := by
  have hSum := Finset.sum_le_sum fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) =>
    Finset.sum_le_sum fun j (_ : j ∈ (Finset.univ : Finset (Fin n))) => scaled_curl_energy_bound hA hJet hφ v i j
  have hEsum : (∑ i : Fin n, ∑ j : Fin n, (weightedScalarEnergy φ (v i) + weightedScalarEnergy φ (v j))) =
      2 * (n : ℝ) * coreScalarEnergy φ v := by
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, ← Finset.mul_sum, coreScalarEnergy]
    ring
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hSum
  simp only [Finset.sum_add_distrib] at hEsum
  rw [hEsum] at hSum
  have hT : weightedScalarEnergy φ
      ((∑ i, testDs Metric.isOpen_ball hA hφ i (testRhoMul Metric.isOpen_ball (v i))) : CompactTest (Metric.ball (0 : X n) 1)) =
      weightedScalarEnergy φ (fun x => ∑ i, weightedDStar A φ i (fun y => (rho y : ℂ) * v i y) x) := by
    congr 1
    funext x
    rw [compactTest_sum_apply]
    rfl
  have hS : (∑ i, ∑ j, weightedScalarEnergy φ (testScaledS Metric.isOpen_ball hA v i j)) =
      ∑ i, ∑ j, weightedScalarEnergy φ (fun x => degenerateS A (fun y k => v k y) x i j) := rfl
  unfold compactFormQ
  rw [hT, ← hS]
  dsimp only [scaledCoreRemainder]
  linarith

end Yau.LeafProofs.L21Aux
