import Yau.Proofs.C02OpenBilinearJets
import spec.CHAIN.CONTRACTS

/-! The Hermitian coefficient extraction is a fixed norm-bounded real
linear map from physical real bilinear forms. -/

noncomputable section
open Set
open scoped ContDiff
namespace Yau.Blueprint.C02Proof
variable {n : ℕ}
local instance rmc_dual_group : NormedAddCommGroup (ComplexVector n →L[ℝ] ℝ) := inferInstance
local instance rmc_dual_space : NormedSpace ℝ (ComplexVector n →L[ℝ] ℝ) := inferInstance
local instance rmc_form_group : NormedAddCommGroup
    (ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ℝ) := inferInstance
local instance rmc_form_space : NormedSpace ℝ
    (ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ℝ) := inferInstance

def realMetricCoefficientEntry (a b : Fin n) :
    (ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ℝ) →L[ℝ] ℂ :=
  (1 / 2 : ℝ) • Complex.ofRealCLM.comp
    ((ContinuousLinearMap.apply ℝ ℝ (stdVec b)).comp
      (ContinuousLinearMap.apply ℝ (ComplexVector n →L[ℝ] ℝ) (stdVec a))) +
    Complex.I • ((1 / 2 : ℝ) • Complex.ofRealCLM.comp
      ((ContinuousLinearMap.apply ℝ ℝ (stdVec b)).comp
        (ContinuousLinearMap.apply ℝ (ComplexVector n →L[ℝ] ℝ) (Complex.I • stdVec a))))

theorem realMetricCoefficientEntry_apply (a b : Fin n)
    (Q : ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ℝ) :
    realMetricCoefficientEntry a b Q =
      ((1 / 2 : ℝ) * Q (stdVec a) (stdVec b) : ℂ) +
        Complex.I * ((1 / 2 : ℝ) * Q (Complex.I • stdVec a) (stdVec b) : ℂ) := by
  simp [realMetricCoefficientEntry, smul_eq_mul]

theorem realMetricCoefficientEntry_norm_le_one (a b : Fin n) :
    ‖realMetricCoefficientEntry a b‖ ≤ 1 := by
  apply (realMetricCoefficientEntry a b).opNorm_le_bound (by norm_num)
  intro Q
  have hStd (i : Fin n) : ‖stdVec i‖ = 1 := EuclideanSpace.orthonormal_single.norm_eq_one i
  have hEval (u : ComplexVector n) (hu : ‖u‖ = 1) : ‖Q u (stdVec b)‖ ≤ ‖Q‖ := by
    calc
      _ ≤ ‖Q u‖ * ‖stdVec b‖ := (Q u).le_opNorm _
      _ = ‖Q u‖ := by rw [hStd, mul_one]
      _ ≤ ‖Q‖ * ‖u‖ := Q.le_opNorm _
      _ = ‖Q‖ := by rw [hu, mul_one]
  have hFirst := hEval (stdVec a) (hStd a)
  have hSecond := hEval (Complex.I • stdVec a) (by rw [norm_smul, Complex.norm_I, hStd, one_mul])
  rw [realMetricCoefficientEntry_apply]
  calc
    _ ≤ ‖((1 / 2 : ℝ) * Q (stdVec a) (stdVec b) : ℂ)‖ +
        ‖Complex.I * ((1 / 2 : ℝ) * Q (Complex.I • stdVec a) (stdVec b) : ℂ)‖ := norm_add_le _ _
    _ = (1 / 2 : ℝ) * ‖Q (stdVec a) (stdVec b)‖ +
        (1 / 2 : ℝ) * ‖Q (Complex.I • stdVec a) (stdVec b)‖ := by
      simp only [Complex.norm_real, norm_mul, Complex.norm_I, one_mul, Real.norm_eq_abs,
        abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    _ ≤ 1 * ‖Q‖ := by linarith

theorem realMetricCoefficientEntry_jet_le
    {O : Set (ComplexVector n)} (hO : IsOpen O)
    {Q : ComplexVector n → ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ℝ}
    (hQ : ContDiffOn ℝ ∞ Q O) {x : ComplexVector n} (hx : x ∈ O)
    (m : ℕ) (a b : Fin n) :
    ‖iteratedFDeriv ℝ m (realMetricCoefficientEntry a b ∘ Q) x‖ ≤
      ‖iteratedFDeriv ℝ m Q x‖ :=
  norm_iteratedFDeriv_linear_on_le _ (realMetricCoefficientEntry_norm_le_one a b) hO hQ hx m

end Yau.Blueprint.C02Proof
