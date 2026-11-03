import Yau.LeafProofs.L21CoreEnergy

/-! Pointwise corrected Levi positivity integrates on the actual common
compact core, including the precise inverse-rho squared norm. -/

open MeasureTheory
open scoped ContDiff
noncomputable section
namespace Yau.LeafProofs.L21Aux

variable {n : ℕ}

theorem contDiffOn_complex_rho_inverse :
    ContDiffOn ℝ ∞ (fun x : X n => ((rho x)⁻¹ : ℂ)) (Metric.ball 0 1) := by
  have hh : ContDiffOn ℝ ∞ (fun x : X n => (rho x : ℂ)) (Metric.ball 0 1) :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn contDiff_rho.contDiffOn
  exact hh.inv (fun x hx => by exact_mod_cast (rho_pos hx).ne')

def testRhoInverse (u : CompactTest (Metric.ball (0 : X n) 1)) : CompactTest (Metric.ball (0 : X n) 1) :=
  multiplyLocalTest Metric.isOpen_ball contDiffOn_complex_rho_inverse u

theorem testRhoInverse_apply (u : CompactTest (Metric.ball (0 : X n) 1)) (x : X n) :
    testRhoInverse u x = ((rho x)⁻¹ : ℂ) * u x := rfl

theorem coreLeviEnergy_boundaryWeight_lower {A : X n → Matrix (Fin n) (Fin n) ℂ}
    (hA : MatrixSmoothOn A (Metric.ball (0 : X n) 1))
    {d : Fin n → Fin n → Fin n → X n → ℂ}
    (hd : ∀ i j k, ContDiffOn ℝ ∞ (d i j k) (Metric.ball 0 1))
    {K : ℝ} (hK : 0 ≤ K)
    (hLevi : ∀ x ∈ Metric.ball (0 : X n) 1, ∀ ξ : Fin n → ℂ,
      (K / 2) * (rho x)⁻¹ ^ 2 * (∑ i, ‖ξ i‖ ^ 2) ≤
        (∑ i, ∑ j, star (ξ i) * correctedLevi A (boundaryWeight K) d i j x * ξ j).re)
    (v : Fin n → CompactTest (Metric.ball (0 : X n) 1)) :
    (K / 2) * coreScalarEnergy (boundaryWeight K) (fun i => testRhoInverse (v i)) ≤
      coreLeviEnergy Metric.isOpen_ball hA (contDiffOn_boundaryWeight K) hd v := by
  let φ : X n → ℝ := boundaryWeight K
  let H (i j : Fin n) := correctedLevi A φ d i j
  let I (i j : Fin n) (x : X n) : ℝ :=
    (star (v i x) * (H i j x * v j x) * weightDensity φ x).re
  let J (i : Fin n) (x : X n) : ℝ :=
    (K / 2) * (‖testRhoInverse (v i) x‖ ^ 2 * Real.exp (-φ x))
  have hI (i j : Fin n) : Integrable (I i j) (Yau.lebesgueC n) :=
    (integrable_test_pair Metric.isOpen_ball (contDiffOn_boundaryWeight K) (v i)
      (multiplyLocalTest Metric.isOpen_ball
        (contDiffOn_correctedLevi Metric.isOpen_ball hA (contDiffOn_boundaryWeight K) hd i j) (v j))).re
  have hJ (i : Fin n) : Integrable (J i) (Yau.lebesgueC n) :=
    (integrable_weighted_test_norm_sq Metric.isOpen_ball (contDiffOn_boundaryWeight K) (testRhoInverse (v i))).const_mul _
  have hItotal := integrable_finsetSum Finset.univ (fun i _ => integrable_finsetSum Finset.univ (fun j _ => hI i j))
  have hJtotal := integrable_finsetSum Finset.univ (fun i _ => hJ i)
  have hPoint (x : X n) : (∑ i, J i x) ≤ ∑ i, ∑ j, I i j x := by
    by_cases hx : x ∈ Metric.ball (0 : X n) 1
    · have hr := rho_pos hx
      have hLeft : (∑ i, J i x) =
          ((K / 2) * (rho x)⁻¹ ^ 2 * (∑ i, ‖v i x‖ ^ 2)) * Real.exp (-φ x) := by
        dsimp only [J]
        simp only [testRhoInverse_apply, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos hr, mul_pow, Finset.sum_mul, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      have hRight : (∑ i, ∑ j, I i j x) =
          (∑ i, ∑ j, star (v i x) * H i j x * v j x).re * Real.exp (-φ x) := by
        simp only [Complex.re_sum, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        change (star (v i x) * (H i j x * v j x) * (Real.exp (-φ x) : ℂ)).re = _
        rw [← mul_assoc, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
      rw [hLeft, hRight]
      exact mul_le_mul_of_nonneg_right (hLevi x hx (fun i => v i x)) (Real.exp_pos _).le
    · have hz (i : Fin n) : v i x = 0 :=
        image_eq_zero_of_notMem_tsupport (fun hh => hx ((v i).property.2.2 hh))
      simp only [J, I, testRhoInverse_apply, hz, mul_zero, norm_zero,
        zero_pow (by decide : 2 ≠ 0), star_zero, zero_mul, Complex.zero_re,
        Finset.sum_const_zero, le_refl]
  have hBound := integral_mono hJtotal hItotal hPoint
  calc
    _ = ∫ x, ∑ i, J i x ∂Yau.lebesgueC n := by
      rw [integral_finsetSum _ (fun i _ => hJ i)]
      simp only [J, integral_const_mul, coreScalarEnergy, weightedScalarEnergy, Finset.mul_sum]
      rfl
    _ ≤ ∫ x, ∑ i, ∑ j, I i j x ∂Yau.lebesgueC n := hBound
    _ = _ := by
      rw [integral_finsetSum _ (fun i _ => integrable_finsetSum Finset.univ (fun j _ => hI i j))]
      unfold coreLeviEnergy
      apply Finset.sum_congr rfl
      intro i _
      rw [integral_finsetSum _ (fun j _ => hI i j)]
      apply Finset.sum_congr rfl
      intro j _
      unfold testPair
      exact integral_re (integrable_test_pair Metric.isOpen_ball (contDiffOn_boundaryWeight K) (v i)
        (multiplyLocalTest Metric.isOpen_ball
          (contDiffOn_correctedLevi Metric.isOpen_ball hA (contDiffOn_boundaryWeight K) hd i j) (v j)))


theorem weightedScalarEnergy_le_testRhoInverse (K : ℝ)
    (u : CompactTest (Metric.ball (0 : X n) 1)) :
    weightedScalarEnergy (boundaryWeight K) u ≤ weightedScalarEnergy (boundaryWeight K) (testRhoInverse u) := by
  apply integral_mono (integrable_weighted_test_norm_sq Metric.isOpen_ball (contDiffOn_boundaryWeight K) u)
    (integrable_weighted_test_norm_sq Metric.isOpen_ball (contDiffOn_boundaryWeight K) (testRhoInverse u))
  intro x
  change ‖u x‖ ^ 2 * Real.exp (-boundaryWeight K x) ≤
    ‖testRhoInverse u x‖ ^ 2 * Real.exp (-boundaryWeight K x)
  apply mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
  by_cases hx : x ∈ Metric.ball (0 : X n) 1
  · have hr := rho_pos hx
    have hri : 1 ≤ (rho x)⁻¹ := by
      have hh : (1 : ℝ) ≤ 1 / rho x := (le_div_iff₀ hr).mpr (by simpa only [one_mul] using rho_le_one x)
      simpa only [one_div] using hh
    have hri2 : 1 ≤ (rho x)⁻¹ ^ 2 := by nlinarith [sq_nonneg ((rho x)⁻¹ - 1)]
    rw [testRhoInverse_apply, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr, mul_pow]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hri2 (sq_nonneg ‖u x‖)
  · have hz : u x = 0 := image_eq_zero_of_notMem_tsupport (fun hh => hx (u.property.2.2 hh))
    simp only [testRhoInverse_apply, hz, mul_zero, norm_zero, le_refl]

theorem coreScalarEnergy_le_inverse (K : ℝ)
    (v : Fin n → CompactTest (Metric.ball (0 : X n) 1)) :
    coreScalarEnergy (boundaryWeight K) v ≤
      coreScalarEnergy (boundaryWeight K) (fun i => testRhoInverse (v i)) :=
  Finset.sum_le_sum fun i _ => weightedScalarEnergy_le_testRhoInverse K (v i)

end Yau.LeafProofs.L21Aux
