import Yau.LeafProofs.L05PerturbationImprovementParameters

open Set
noncomputable section
set_option maxHeartbeats 1200000
namespace Yau.LeafProofs.L05Aux

theorem perturb_normalization_radius {alpha beta mu0 af0 M fB : ℝ}
    (ha : 0 < alpha) (hb : 0 < beta) (hmu : 0 < mu0) (haf : 0 < af0)
    (hM : 0 ≤ M) (hf : 0 ≤ fB) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1/16 ∧ M*r^beta ≤ mu0 ∧ fB*r^(2+alpha) ≤ af0 := by
  let m := min alpha beta
  let D := 1+M+fB
  let C := min mu0 af0
  have hm : 0 < m := lt_min ha hb
  have hD : 0 < D := by dsimp only [D]; positivity
  have hC : 0 < C := lt_min hmu haf
  obtain ⟨r,hr,hrb,hPow⟩ := perturb_positive_power_threshold
    (by norm_num : (0 : ℝ) < 1/16) (div_pos hC hD) hm
  have hr1 : r ≤ 1 := hrb.trans (by norm_num)
  have hMNorm : M*(C/D) ≤ C := by
    have hMD : M ≤ D := by dsimp only [D]; linarith only [hf]
    calc
      _ ≤ D*(C/D) := mul_le_mul_of_nonneg_right hMD (div_pos hC hD).le
      _ = C := by field_simp [hD.ne']
  have hfNorm : fB*(C/D) ≤ C := by
    have hfD : fB ≤ D := by dsimp only [D]; linarith only [hM]
    calc
      _ ≤ D*(C/D) := mul_le_mul_of_nonneg_right hfD (div_pos hC hD).le
      _ = C := by field_simp [hD.ne']
  have hBeta : r^beta ≤ r^m := Real.rpow_le_rpow_of_exponent_ge hr hr1 (min_le_right _ _)
  have hAlpha : r^(2+alpha) ≤ r^m := Real.rpow_le_rpow_of_exponent_ge hr hr1
    (by have hh : m ≤ alpha := min_le_left _ _; linarith only [hh])
  refine ⟨r,hr,hrb,?_,?_⟩
  · exact ((mul_le_mul_of_nonneg_left hBeta hM).trans
      (mul_le_mul_of_nonneg_left hPow hM)).trans (hMNorm.trans (min_le_left _ _))
  · exact ((mul_le_mul_of_nonneg_left hAlpha hf).trans
      (mul_le_mul_of_nonneg_left hPow hf)).trans (hfNorm.trans (min_le_right _ _))

theorem perturb_normalization_numeric_data {alpha beta mu0 af0 M fB uB : ℝ}
    (ha : 0 < alpha) (hb : 0 < beta) (hmu : 0 < mu0) (haf : 0 < af0)
    (hM : 0 ≤ M) (hf : 0 ≤ fB) (hu : 0 ≤ uB) :
    let N := 1+2*uB+3*M+fB
    let Q0 := 3*M+fB
    ∃ r : ℝ, 0 < r ∧ r ≤ 1/16 ∧ 1 ≤ N ∧ 0 < N ∧ 0 ≤ Q0 ∧
      2*uB+Q0 ≤ N ∧ M*r^beta ≤ mu0 ∧ (fB/N)*r^(2+alpha) ≤ af0 := by
  let N := 1+2*uB+3*M+fB
  let Q0 := 3*M+fB
  have hN1 : 1 ≤ N := by dsimp only [N]; linarith only [hu,hM,hf]
  have hN : 0 < N := lt_of_lt_of_le zero_lt_one hN1
  obtain ⟨r,hr,hrb,hMu,hAf⟩ := perturb_normalization_radius ha hb hmu haf hM hf
  have hfDiv : fB/N ≤ fB := (div_le_iff₀ hN).mpr
    (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hN1 hf)
  refine ⟨r,hr,hrb,hN1,hN,by change 0 ≤ 3*M+fB; positivity,?_,hMu,?_⟩
  · change 2*uB+(3*M+fB) ≤ 1+2*uB+3*M+fB
    linarith
  · exact (mul_le_mul_of_nonneg_right hfDiv (Real.rpow_nonneg hr.le _)).trans hAf

end Yau.LeafProofs.L05Aux
