import Yau.Proofs.P06WeakLeviApproximation

noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff ComplexOrder

namespace Yau.NodeProofs.P06Aux
open Yau Yau.Blueprint Yau.LeafProofs.L18Aux

theorem trace_rankOne_family {n : ℕ} {ι : Type*} [Fintype ι]
    (A : Matrix (Fin n) (Fin n) ℂ) (c : ι → ℝ) (v : ι → ComplexVector n) :
    (Matrix.trace (A * ∑ i, (c i : ℂ) •
      Matrix.vecMulVec (WithLp.ofLp (v i)) (star (WithLp.ofLp (v i))))).re =
      ∑ i, c i * leviDirection A (v i) := by
  simp only [Finset.mul_sum, Matrix.mul_smul, Matrix.trace_sum, Matrix.trace_smul,
    Matrix.mul_vecMulVec, Matrix.trace_vecMulVec, Complex.re_sum, smul_eq_mul,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    leviDirection, dotProduct_comm]

theorem rankOne_family_quadratic_order {n : ℕ} {ι : Type*} [Fintype ι]
    (A H : Matrix (Fin n) (Fin n) ℂ) (c : ι → ℝ) (v : ι → ComplexVector n)
    (hAH : HermLE A H)
    (hp : (∑ i, (c i : ℂ) •
      Matrix.vecMulVec (WithLp.ofLp (v i)) (star (WithLp.ofLp (v i)))).PosSemidef) :
    (∑ i, c i * leviDirection A (v i)) ≤ ∑ i, c i * leviDirection H (v i) := by
  have h := matrix_trace_mul_nonneg (H - A) _ hAH hp
  rw [Matrix.sub_mul, Matrix.trace_sub, Complex.sub_re,
    trace_rankOne_family, trace_rankOne_family] at h
  exact sub_nonneg.mp h

theorem leviDirection_hasCompactSupport {n : ℕ} (φ : ComplexVector n → ℝ)
    (hcφ : HasCompactSupport φ) (v : ComplexVector n) :
    HasCompactSupport (fun z => leviDirection (leviC φ z) v) ∧
      tsupport (fun z => leviDirection (leviC φ z) v) ⊆ tsupport φ := by
  have hs : tsupport (fun z => leviDirection (leviC φ z) v) ⊆ tsupport φ := by
    apply closure_minimal ?_ (isClosed_tsupport φ)
    intro z hz
    by_contra hn
    have hzero := leviC_zero_off_tsupport φ hn
    simp only [Function.mem_support, hzero, leviDirection, Matrix.zero_mulVec,
      dotProduct_zero, Complex.zero_re, ne_eq, not_true_eq_false] at hz
  exact ⟨hcφ.of_isClosed_subset (isClosed_tsupport _) hs, hs⟩

/-- Uniform local approximation controls the true distributional test
pairing; integrability and the support of the second derivatives are
proved from the literal compact test. -/
theorem integral_test_error_bound {n : ℕ} {O K : Set (ComplexVector n)}
    (hO : IsOpen O) {u U q : ComplexVector n → ℝ}
    (hu : ContinuousOn u O) (hU : Continuous U) (hq : Continuous q)
    (hcq : HasCompactSupport q) (hqO : tsupport q ⊆ O) (hqK : tsupport q ⊆ K)
    {ε : ℝ} (hε : 0 ≤ ε) (he : ∀ z ∈ K, |U z - u z| ≤ ε) :
    |(∫ z, u z * q z ∂lebesgueC n) - ∫ z, U z * q z ∂lebesgueC n| ≤
      ε * ∫ z, |q z| ∂lebesgueC n := by
  letI : (lebesgueC n).IsAddHaarMeasure := by
    rw [Yau.LeafProofs.lebesgueC_eq_volume]
    infer_instance
  have huq : Integrable (fun z => u z * q z) (lebesgueC n) := by
    simpa only [mul_comm] using integrable_compactTest_mul (lebesgueC n) hO hq hcq hqO hu
  have hUq : Integrable (fun z => U z * q z) (lebesgueC n) :=
    (hU.mul hq).integrable_of_hasCompactSupport hcq.mul_left
  have hIq : Integrable (fun z => |q z|) (lebesgueC n) :=
    (hq.integrable_of_hasCompactSupport hcq).abs
  rw [← integral_sub huq hUq]
  have hnorm := norm_integral_le_of_norm_le (f := fun z => u z * q z - U z * q z)
    (hIq.const_mul ε) (Filter.Eventually.of_forall fun z => by
    rw [Real.norm_eq_abs, ← sub_mul, abs_mul, abs_sub_comm]
    by_cases hz : z ∈ tsupport q
    · exact mul_le_mul_of_nonneg_right (he z (hqK hz)) (abs_nonneg _)
    · rw [image_eq_zero_of_notMem_tsupport hz, abs_zero, mul_zero, mul_zero])
  rw [integral_const_mul] at hnorm
  exact hnorm

end Yau.NodeProofs.P06Aux
