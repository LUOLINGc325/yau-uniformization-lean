import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! The four finite coefficients depend only on dimension, coercivity and jet size. -/
noncomputable section
namespace Yau.Proofs.C05InverseRicciJetUniformBudgetAux

def coefficientZero (n : ℕ) (μ : ℝ) : ℝ := Real.sqrt (2*n:ℕ) / μ
def coefficientOne (n : ℕ) (μ B : ℝ) : ℝ :=
  (2*n:ℕ) * coefficientZero n μ ^ 2 * B
def coefficientTwo (n : ℕ) (μ B : ℝ) : ℝ :=
  (2*n:ℕ) * (2 * coefficientZero n μ * coefficientOne n μ B) * B +
    (2*n:ℕ) * coefficientZero n μ ^ 2 * B
def coefficientThree (n : ℕ) (μ B : ℝ) : ℝ :=
  (2*n:ℕ) * ((2 * coefficientZero n μ * coefficientTwo n μ B +
    2 * coefficientOne n μ B ^ 2) * B +
    4 * coefficientZero n μ * coefficientOne n μ B * B + coefficientZero n μ ^ 2 * B)
def inverseRicciJetBudget (n : ℕ) (μ B : ℝ) : ℝ :=
  1 + coefficientZero n μ + coefficientOne n μ B +
    coefficientTwo n μ B + coefficientThree n μ B

theorem coefficients_nonneg (n : ℕ) {μ B : ℝ} (hμ : 0 < μ) (hB : 0 ≤ B) :
    0 ≤ coefficientZero n μ ∧ 0 ≤ coefficientOne n μ B ∧
      0 ≤ coefficientTwo n μ B ∧ 0 ≤ coefficientThree n μ B := by
  have h0 : 0 ≤ coefficientZero n μ := div_nonneg (Real.sqrt_nonneg _) hμ.le
  have h1 : 0 ≤ coefficientOne n μ B := by unfold coefficientOne; positivity
  have h2 : 0 ≤ coefficientTwo n μ B := by unfold coefficientTwo; positivity
  refine ⟨h0,h1,h2,?_⟩
  unfold coefficientThree
  positivity

theorem inverseRicciJetBudget_pos (n : ℕ) {μ B : ℝ} (hμ : 0 < μ) (hB : 0 ≤ B) :
    0 < inverseRicciJetBudget n μ B := by
  obtain ⟨h0,h1,h2,h3⟩ := coefficients_nonneg n hμ hB
  unfold inverseRicciJetBudget
  linarith

theorem polynomial_majorants (n : ℕ) {μ B N0 N1 N2 N3 R1 R2 R3 : ℝ}
    (hμ : 0 < μ) (hB : 0 ≤ B)
    (hN0 : 0 ≤ N0) (hN1 : 0 ≤ N1) (hN2 : 0 ≤ N2)
    (hR1 : 0 ≤ R1) (hR2 : 0 ≤ R2) (hR3 : 0 ≤ R3)
    (h0 : N0 ≤ coefficientZero n μ) (hR1B : R1 ≤ B) (hR2B : R2 ≤ B) (hR3B : R3 ≤ B)
    (he1 : N1 ≤ (2*n:ℕ) * N0 ^ 2 * R1)
    (he2 : N2 ≤ (2*n:ℕ) * (2*N0*N1) * R1 + (2*n:ℕ) * N0 ^ 2 * R2)
    (he3 : N3 ≤ (2*n:ℕ) * ((2*N0*N2+2*N1 ^ 2)*R1+4*N0*N1*R2+N0 ^ 2*R3)) :
    N1 ≤ coefficientOne n μ B ∧ N2 ≤ coefficientTwo n μ B ∧ N3 ≤ coefficientThree n μ B := by
  obtain ⟨hC0,hC1,hC2,hC3⟩ := coefficients_nonneg n hμ hB
  have h1 : N1 ≤ coefficientOne n μ B := he1.trans (by
    unfold coefficientOne
    gcongr <;> assumption)
  have h2 : N2 ≤ coefficientTwo n μ B := he2.trans (by
    unfold coefficientTwo
    gcongr <;> assumption)
  refine ⟨h1,h2,he3.trans ?_⟩
  unfold coefficientThree
  gcongr <;> assumption

end Yau.Proofs.C05InverseRicciJetUniformBudgetAux
