import Yau.Proofs.P04CanonicalNorm
import Yau.LeafProofs.L18

/-! Uniform elementary bounds for the genuine smooth regularization of the
canonical logarithm. The value of `Real.log` at zero is never identified with
an extended logarithm. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff Matrix ComplexOrder
namespace Yau.NodeProofs.P08Aux
open Yau Yau.Blueprint Yau.LeafProofs

/-- A single growth constant works for every positive regularization parameter
at most one. -/
theorem log_add_regularization_upper {q r C ε : ℝ}
    (hq : 0 ≤ q) (hr : 0 ≤ r) (hlog : Real.log q ≤ C * (1 + r))
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    Real.log (q + ε) ≤ (max C 0 + 1) * (1 + r) := by
  let a := max C 0 * (1 + r)
  have ha : 0 ≤ a := mul_nonneg (le_max_right C 0) (by linarith)
  have hqexp : q ≤ Real.exp a := by
    apply Real.le_exp_of_log_le
    exact hlog.trans (mul_le_mul_of_nonneg_right (le_max_left C 0) (by linarith))
  have heexp : ε ≤ Real.exp a := hε1.trans (Real.one_le_exp_iff.mpr ha)
  have hupper : q + ε ≤ 2 * Real.exp a := by linarith
  have hlogupper := Real.log_le_log (add_pos_of_nonneg_of_pos hq hε) hupper
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (Real.exp_ne_zero a), Real.log_exp] at hlogupper
  have hlog2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  dsimp only [a] at hlogupper
  nlinarith

theorem log_add_regularization_lower {q ε : ℝ} (hq : 0 ≤ q) (hε : 0 < ε) :
    Real.log ε ≤ Real.log (q + ε) :=
  Real.log_le_log hε (by linarith)

theorem log_add_regularization_basepoint {q ε : ℝ} (hq : 0 < q) (hε : 0 < ε) :
    Real.log q ≤ Real.log (q + ε) :=
  Real.log_le_log hq (by linarith)

/-- For a fixed regularization, the absolute value has linear growth as well.
Only the additive constant is allowed to depend on the parameter. -/
theorem abs_log_add_regularization_upper {q r C ε : ℝ}
    (hq : 0 ≤ q) (hr : 0 ≤ r) (hlog : Real.log q ≤ C * (1 + r))
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    |Real.log (q + ε)| ≤ (max C 0 + 1) * (1 + r) + |Real.log ε| := by
  have hu := log_add_regularization_upper hq hr hlog hε hε1
  have hl := log_add_regularization_lower hq hε
  have ha : 0 ≤ (max C 0 + 1) * (1 + r) := by positivity
  exact abs_le.mpr ⟨by linarith [neg_abs_le (Real.log ε)], by linarith [abs_nonneg (Real.log ε)]⟩

/-- A concrete sequence stays in the allowed regularization range and
exposes the size of the logarithm on the zero set. -/
def logRegularizationParameter (j : ℕ) : ℝ := Real.exp (-((j : ℝ) + 1))

theorem logRegularizationParameter_pos (j : ℕ) :
    0 < logRegularizationParameter j := Real.exp_pos _

theorem logRegularizationParameter_le_one (j : ℕ) :
    logRegularizationParameter j ≤ 1 := by
  apply Real.exp_le_one_iff.mpr
  exact neg_nonpos.mpr (by positivity)

theorem log_logRegularizationParameter (j : ℕ) :
    Real.log (logRegularizationParameter j) = -((j : ℝ) + 1) := Real.log_exp _

theorem logRegularizationParameter_tendsto :
    Tendsto logRegularizationParameter atTop (𝓝 0) := by
  exact Real.tendsto_exp_neg_atTop_nhds_zero.comp
    (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)

theorem regularized_log_tendsto {q : ℝ} (hq : q ≠ 0) :
    Tendsto (fun j => Real.log (q + logRegularizationParameter j)) atTop (𝓝 (Real.log q)) := by
  exact (Real.continuousAt_log hq).tendsto.comp
    (by simpa using tendsto_const_nhds.add logRegularizationParameter_tendsto)

variable {n : ℕ} {M : ComplexManifold n}

/-- The original logarithmic growth witness produces a uniform positive
constant before the regularization parameter is introduced. -/
theorem canonical_regularized_log_growth (g : SmoothMetric M) (S : CanonicalSection M)
    (o : M.Carrier) (hgrowth : ∃ C : ℝ, ∀ x,
      Real.log (canonicalNormSq g.form S x) ≤ C * (1 + distFrom g.form o x)) :
    ∃ A : ℝ, 0 < A ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ x,
      Real.log (canonicalNormSq g.form S x + ε) ≤ A * (1 + distFrom g.form o x) := by
  obtain ⟨C, hC⟩ := hgrowth
  refine ⟨max C 0 + 1, by positivity, ?_⟩
  intro ε hε hε1 x
  exact log_add_regularization_upper (Yau.Proofs.P04Aux.canonicalNormSq_nonneg g.form S x)
    (g.induced_distance_nonneg o x) (hC x) hε hε1

end Yau.NodeProofs.P08Aux
