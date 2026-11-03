import Yau.Proofs.V02CoronaAlgebra

/-! Pointwise facts for the source's actual reciprocal outer damping.
The input is a squared vector norm, with no positive lower bound required. -/

noncomputable section
namespace Yau.Blueprint.V02Proof

def reciprocalDamping (P s : ℝ) : ℝ := (1 + s / P)⁻¹

theorem reciprocalDamping_pos {P s : ℝ} (hP : 0 < P) (hs : 0 ≤ s) :
    0 < reciprocalDamping P s := by
  unfold reciprocalDamping
  positivity

theorem reciprocalDamping_le_one {P s : ℝ} (hP : 0 < P) (hs : 0 ≤ s) :
    reciprocalDamping P s ≤ 1 := by
  exact (inv_le_one₀ (by positivity : 0 < 1 + s / P)).mpr
    (by linarith [div_nonneg hs hP.le])

theorem reciprocalDamping_loss {P s : ℝ} (hP : 0 < P) (hs : 0 ≤ s) :
    0 ≤ 1 - reciprocalDamping P s ^ 2 ∧
      1 - reciprocalDamping P s ^ 2 ≤ 2 * s / P := by
  have ht : 0 ≤ s / P := div_nonneg hs hP.le
  have hden : 0 < 1 + s / P := by positivity
  have he : reciprocalDamping P s * (1 + s / P) = 1 :=
    inv_mul_cancel₀ hden.ne'
  have hr := reciprocalDamping_pos hP hs
  have hr1 := reciprocalDamping_le_one hP hs
  constructor
  · nlinarith
  · have hsmall : 1 - reciprocalDamping P s ≤ s / P := by
      nlinarith [mul_nonneg ht (sub_nonneg.mpr hr1)]
    rw [mul_div_assoc]
    nlinarith [sq_nonneg (1 - reciprocalDamping P s)]

theorem dampingLog_bounds {P s : ℝ} (hP : 0 < P) (hs : 0 ≤ s) :
    0 ≤ Real.log (1 + s / P) ∧ Real.log (1 + s / P) ≤ s / P := by
  have ht : 0 ≤ s / P := div_nonneg hs hP.le
  refine ⟨Real.log_nonneg (by linarith), ?_⟩
  have h := Real.log_le_sub_one_of_pos (by positivity : 0 < 1 + s / P)
  linarith

theorem reciprocalDamping_mul_norm_bound {P x : ℝ} (hP : 0 < P) (hx : 0 ≤ x) :
    reciprocalDamping P (x ^ 2) * x ≤ Real.sqrt P / 2 := by
  have hs : 0 < Real.sqrt P := Real.sqrt_pos.mpr hP
  have hsq := Real.sq_sqrt hP.le
  have hden : 0 < 1 + x ^ 2 / P := by positivity
  have he : reciprocalDamping P (x ^ 2) = P / (P + x ^ 2) := by
    unfold reciprocalDamping
    field_simp
  rw [he, div_mul_eq_mul_div]
  apply (div_le_iff₀ (by positivity : 0 < P + x ^ 2)).mpr
  nlinarith [sq_nonneg (x - Real.sqrt P)]

theorem dampingLog_radial_derivative_bound {P x : ℝ} (hP : 0 < P) (hx : 0 ≤ x) :
    2 * x / (P + x ^ 2) ≤ (Real.sqrt P)⁻¹ := by
  have hs : 0 < Real.sqrt P := Real.sqrt_pos.mpr hP
  have hsq := Real.sq_sqrt hP.le
  apply (div_le_iff₀ (by positivity : 0 < P + x ^ 2)).mpr
  apply (le_inv_mul_iff₀ hs).mpr
  nlinarith [sq_nonneg (x - Real.sqrt P)]

end Yau.Blueprint.V02Proof
