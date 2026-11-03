import spec.CHAIN.CONTRACTS

/-! The original integrated Harnack inequality bounds scalar curvature
on a fixed-radius moving region, using the same physical future time t+1. -/

noncomputable section
open Set
namespace Yau.Blueprint.C02Proof
variable {n : ℕ} {X : KahlerManifold n}

theorem scalarCurvature_bound_on_harnack_radius
    (o : Pt X) (h : Flow X) (hC01 : HarnackCompleteness X o h)
    (R : ℝ) (hR : 0 ≤ R) :
    ∃ B : ℝ, 0 < B ∧ ∀ t : ℝ, 1 ≤ t → ∀ x : Pt X,
      |distFrom (h t) x o| ≤ R → scalarCurvature (h t) x ≤ B := by
  obtain ⟨_hBis, _hComplete, _hRicci, _hMatrix, _hScalar, _hMono,
    hOrigin, hIntegrated, _hShrink⟩ := hC01
  obtain ⟨C₀, hC₀⟩ := hOrigin
  obtain ⟨A, hA⟩ := hIntegrated
  let M : ℝ := |C₀| + 1
  let B : ℝ := M * 2 * Real.exp (|A| * R ^ 2)
  have hM : 0 < M := by dsimp [M]; positivity
  refine ⟨B, by dsimp [B]; positivity, ?_⟩
  intro t ht x hx
  have htpos : 0 < t := by linarith
  have hRatio : 0 ≤ (t + 1) / t := div_nonneg (by linarith) htpos.le
  have hRatioUpper : (t + 1) / t ≤ 2 := (div_le_iff₀ htpos).mpr (by linarith)
  have hOriginBound : scalarCurvature (h (t + 1)) o ≤ M := by
    have h₀ := hC₀ (t + 1) (by linarith : 0 ≤ t + 1)
    dsimp only [M]
    linarith [le_abs_self C₀]
  have hRadiusSq : distFrom (h t) x o ^ 2 ≤ R ^ 2 := by
    have hsq := (sq_le_sq₀ (abs_nonneg (distFrom (h t) x o)) hR).mpr hx
    simpa only [sq_abs] using hsq
  have hExponent : A * distFrom (h t) x o ^ 2 ≤ |A| * R ^ 2 :=
    (mul_le_mul_of_nonneg_right (le_abs_self A) (sq_nonneg _)).trans
      (mul_le_mul_of_nonneg_left hRadiusSq (abs_nonneg A))
  have hH := hA x o t (t + 1) htpos (by linarith : t < t + 1)
  have hH' : scalarCurvature (h t) x ≤ scalarCurvature (h (t + 1)) o *
      ((t + 1) / t) * Real.exp (A * distFrom (h t) x o ^ 2) := by
    simpa only [add_sub_cancel_left, div_one] using hH
  calc
    scalarCurvature (h t) x ≤ scalarCurvature (h (t + 1)) o *
      ((t + 1) / t) * Real.exp (A * distFrom (h t) x o ^ 2) := hH'
    _ ≤ M * ((t + 1) / t) * Real.exp (A * distFrom (h t) x o ^ 2) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hOriginBound hRatio)
        (Real.exp_pos _).le
    _ ≤ M * 2 * Real.exp (A * distFrom (h t) x o ^ 2) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hRatioUpper hM.le)
        (Real.exp_pos _).le
    _ ≤ B := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hExponent) (by positivity)

end Yau.Blueprint.C02Proof
