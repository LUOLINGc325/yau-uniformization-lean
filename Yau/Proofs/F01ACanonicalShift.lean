import Yau.Proofs.F01CanonicalRegularizer

/-! Uniform positive regularization and its limit use one fixed section. -/
noncomputable section
open Filter
open scoped Topology

namespace Yau.NodeProofs.F01Aux
open Yau Yau.Blueprint Yau.Proofs.P04Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false

/-- The small parameter may depend on the majorant, while the final shift
depends only on the canonical linear-growth bound. This estimate includes zeros. -/
theorem canonical_regularizer_uniform_shift_of_bounds
    (g : SmoothMetric M) (S : CanonicalSection M) (Ξ u : M.Carrier → ℝ)
    {A B ε δ : ℝ} (hA : 1 ≤ A) (hδ : 0 < δ)
    (hδsmall : δ ≤ Real.exp (A - B))
    (hq : ∀ x, canonicalNormSq g.form S x ≤ Real.exp (ε * u x ^ 2 + A))
    (hΞ : ∀ x, Ξ x ≤ ε * u x ^ 2 + B) (x : M.Carrier) :
    canonicalRegularizer g S Ξ δ x - ε * u x ^ 2 - 2 * A ≤ 0 := by
  have hterm : δ * Real.exp (Ξ x) ≤ Real.exp (ε * u x ^ 2 + A) := by
    calc
      _ ≤ Real.exp (A - B) * Real.exp (Ξ x) :=
        mul_le_mul_of_nonneg_right hδsmall (Real.exp_pos _).le
      _ = Real.exp (A - B + Ξ x) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith [hΞ x])
  have hsum : canonicalNormSq g.form S x + δ * Real.exp (Ξ x) ≤
      2 * Real.exp (ε * u x ^ 2 + A) := by linarith [hq x]
  have hp : 0 < canonicalNormSq g.form S x + δ * Real.exp (Ξ x) :=
    add_pos_of_nonneg_of_pos (canonicalNormSq_nonneg _ _ _)
      (mul_pos hδ (Real.exp_pos _))
  have hlog := Real.log_le_log hp hsum
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (Real.exp_ne_zero _), Real.log_exp] at hlog
  have htwo : Real.log 2 ≤ (1 : ℝ) := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  change Real.log (canonicalNormSq g.form S x + δ * Real.exp (Ξ x)) -
    ε * u x ^ 2 - 2 * A ≤ 0
  linarith

def canonicalRegularizerDeltaSeq (δmax : ℝ) (j : ℕ) : ℝ := δmax / ((j : ℝ) + 1)

theorem canonicalRegularizerDeltaSeq_pos {δmax : ℝ} (hδmax : 0 < δmax) (j : ℕ) :
    0 < canonicalRegularizerDeltaSeq δmax j := by
  exact div_pos hδmax (by positivity)

theorem canonicalRegularizerDeltaSeq_le {δmax : ℝ} (hδmax : 0 ≤ δmax) (j : ℕ) :
    canonicalRegularizerDeltaSeq δmax j ≤ δmax := by
  apply (div_le_iff₀ (by positivity : 0 < (j : ℝ) + 1)).mpr
  nlinarith [mul_nonneg hδmax (Nat.cast_nonneg j : (0 : ℝ) ≤ j)]

theorem canonicalRegularizerDeltaSeq_tendsto (δmax : ℝ) :
    Tendsto (canonicalRegularizerDeltaSeq δmax) atTop (𝓝 0) := by
  change Tendsto (fun j : ℕ => δmax / ((j : ℝ) + 1)) atTop (𝓝 0)
  simpa [div_eq_mul_inv] using
    (tendsto_const_nhds (x := δmax)).mul
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

/-- Only nonzero norms have a finite singular logarithmic limit. -/
theorem canonicalRegularizer_tendsto (g : SmoothMetric M) (S : CanonicalSection M)
    (Ξ : M.Carrier → ℝ) {δ : ℕ → ℝ} (hδ : Tendsto δ atTop (𝓝 0))
    (x : M.Carrier) (hqx : canonicalNormSq g.form S x ≠ 0) :
    Tendsto (fun j => canonicalRegularizer g S Ξ (δ j) x) atTop
      (𝓝 (Real.log (canonicalNormSq g.form S x))) := by
  apply (Real.continuousAt_log hqx).tendsto.comp
  simpa using tendsto_const_nhds.add (hδ.mul_const (Real.exp (Ξ x)))

/-- Passage to the singular comparison changes neither the section nor U/P. -/
theorem canonical_comparison_limit (g : SmoothMetric M) (S : CanonicalSection M)
    (Ξ : M.Carrier → ℝ) {δ : ℕ → ℝ} (hδ : Tendsto δ atTop (𝓝 0))
    (x : M.Carrier) (hqx : canonicalNormSq g.form S x ≠ 0)
    {D t p v ε ux A N : ℝ}
    (hcomp : ∀ j, 0 ≤ (D - t) * p + v -
      D * (canonicalRegularizer g S Ξ (δ j) x - ε * ux ^ 2 - A) + N * t) :
    0 ≤ (D - t) * p + v -
      D * (Real.log (canonicalNormSq g.form S x) - ε * ux ^ 2 - A) + N * t := by
  have hl := canonicalRegularizer_tendsto g S Ξ hδ x hqx
  have hlim : Tendsto (fun j => (D - t) * p + v -
      D * (canonicalRegularizer g S Ξ (δ j) x - ε * ux ^ 2 - A) + N * t) atTop
      (𝓝 ((D - t) * p + v -
        D * (Real.log (canonicalNormSq g.form S x) - ε * ux ^ 2 - A) + N * t)) :=
    (tendsto_const_nhds.sub (((hl.sub_const (ε * ux ^ 2)).sub_const A).const_mul D)).add_const (N * t)
  exact ge_of_tendsto' hlim hcomp

end Yau.NodeProofs.F01Aux
