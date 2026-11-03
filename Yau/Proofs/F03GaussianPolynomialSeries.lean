import Yau.Proofs.F03GaussianBallEnvelope

/-! Polynomial radial mass bounds give a genuine dimension-only finite Gaussian budget. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace Yau.Proofs.F03Aux

theorem summable_polynomial_gaussian (D : ℕ) {c : ℝ} (hc : 0 < c) :
    Summable (fun j : ℕ => ((j : ℝ)+1)^D*Real.exp (-c*(j : ℝ)^2)) := by
  have hShift : Summable (fun j : ℕ => ((j : ℝ)+1)^D*Real.exp (-c*((j : ℝ)+1))) := by
    simpa only [Nat.cast_add,Nat.cast_one,Nat.cast_pow] using
      (summable_nat_add_iff 1).mpr (Real.summable_pow_mul_exp_neg_nat_mul D hc)
  have hMajor := Summable.mul_left (Real.exp c) hShift
  apply hMajor.of_nonneg_of_le (fun j => by positivity)
  intro j
  have hj : (j : ℝ) ≤ (j : ℝ)^2 := by
    by_cases hj0 : j=0
    · subst j;norm_num
    · have hj1 : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hj0
      nlinarith
  have hExp : Real.exp (-c*(j : ℝ)^2) ≤ Real.exp c*Real.exp (-c*((j : ℝ)+1)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg hc.le (sub_nonneg.mpr hj)]
  have hh := mul_le_mul_of_nonneg_left hExp (by positivity : 0 ≤ ((j : ℝ)+1)^D)
  convert hh using 1
  ring

theorem exists_gaussian_polynomial_mass_budget {α : Type*} [MeasurableSpace α]
    (D : ℕ) {c : ℝ} (hc : 0 < c) :
    ∃ C : ℝ,0 < C ∧ ∀ (μ : Measure α) (r : α → ℝ),Measurable r → (∀ x,0 ≤ r x) →
      ∀ A : ℝ,0 ≤ A →
      (∀ j : ℕ,μ {x | r x<(j : ℝ)+1} ≤ ENNReal.ofReal (A*((j : ℝ)+1)^D)) →
      (∫⁻ x,ENNReal.ofReal (Real.exp (-c*(r x)^2)) ∂μ) ≤ ENNReal.ofReal (C*A) := by
  let S : ℝ := ∑' j : ℕ,((j : ℝ)+1)^D*Real.exp (-c*(j : ℝ)^2)
  have hSummable := summable_polynomial_gaussian D hc
  have hTerms (j : ℕ) : 0 ≤ ((j : ℝ)+1)^D*Real.exp (-c*(j : ℝ)^2) := by positivity
  have hS : 0 ≤ S := tsum_nonneg hTerms
  refine ⟨1+S,by linarith,fun μ r hr hr0 A hA hMass => ?_⟩
  calc
    _ ≤ ∑' j : ℕ,ENNReal.ofReal (Real.exp (-c*(j : ℝ)^2))*μ {x | r x<(j : ℝ)+1} :=
      gaussian_lintegral_le_ball_mass_series μ r hr hr0 hc.le
    _ ≤ ∑' j : ℕ,ENNReal.ofReal (Real.exp (-c*(j : ℝ)^2))*
        ENNReal.ofReal (A*((j : ℝ)+1)^D) :=
      ENNReal.tsum_le_tsum (fun j => mul_le_mul_of_nonneg_left (hMass j) (by positivity))
    _ = ∑' j : ℕ,ENNReal.ofReal A*ENNReal.ofReal
        (((j : ℝ)+1)^D*Real.exp (-c*(j : ℝ)^2)) := by
      congr 1
      funext j
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le,← ENNReal.ofReal_mul hA]
      congr 1
      ring
    _ = ENNReal.ofReal (A*S) := by
      rw [ENNReal.tsum_mul_left,← ENNReal.ofReal_tsum_of_nonneg hTerms hSummable,
        ← ENNReal.ofReal_mul hA]
    _ ≤ ENNReal.ofReal ((1+S)*A) := ENNReal.ofReal_le_ofReal (by nlinarith)

end Yau.Proofs.F03Aux
