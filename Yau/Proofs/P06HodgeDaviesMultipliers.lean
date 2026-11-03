import Yau.LeafProofs.L03CutoffEnergyBounds

noncomputable section
open MeasureTheory Filter
open scoped Topology InnerProductSpace

namespace Yau.NodeProofs.P06Aux.Davies
open Yau Yau.LeafProofs Yau.LeafProofs.L03
variable {n k : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false

/-- Multiplication identities on the genuine form completion follow from
pointwise identities on actual sections. -/
theorem multiplier_comp_eq (g : SmoothMetric M) (μ : Measure M.Carrier)
    (a b c : M.Carrier → ℝ)
    (ha : AEStronglyMeasurable a μ) (hb : AEStronglyMeasurable b μ)
    (hc : AEStronglyMeasurable c μ)
    (A B C : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hab : ∀ x, |a x| ≤ A) (hbb : ∀ x, |b x| ≤ B) (hcb : ∀ x, |c x| ≤ C)
    (heq : ∀ x, a x * b x = c x) (u : L2FormHilbert g μ k) :
    multiplyL2FormHilbert g μ a ha A hA hab
        (multiplyL2FormHilbert g μ b hb B hB hbb u) =
      multiplyL2FormHilbert g μ c hc C hC hcb u := by
  let P := multiplyL2FormHilbert (k := k) g μ a ha A hA hab
  let Q := multiplyL2FormHilbert (k := k) g μ b hb B hB hbb
  let R := multiplyL2FormHilbert (k := k) g μ c hc C hC hcb
  refine UniformSpace.Completion.induction_on u (p := fun u => P (Q u) = R u) ?_ ?_
  · exact isClosed_eq (P.continuous.comp Q.continuous) R.continuous
  · intro v
    change P (Q (realizeL2Form g μ v)) = R (realizeL2Form g μ v)
    dsimp only [P, Q, R]
    rw [multiplyL2FormHilbert_realize, multiplyL2FormHilbert_realize,
      multiplyL2FormHilbert_realize]
    congr 1
    apply L2FormSpace.toSection_injective g μ k
    funext x
    change a x • (b x • v.toSection x) = c x • v.toSection x
    rw [smul_smul, heq]

/-- Pointwise domination of scalar multipliers gives domination of their
actual Hilbert norms in every form degree. -/
theorem multiplier_norm_compare (g : SmoothMetric M) (μ : Measure M.Carrier)
    (a b : M.Carrier → ℝ)
    (ha : AEStronglyMeasurable a μ) (hb : AEStronglyMeasurable b μ)
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hab : ∀ x, |a x| ≤ A) (hbb : ∀ x, |b x| ≤ B)
    (C : ℝ) (hC : 0 ≤ C) (hcmp : ∀ x, |a x| ≤ C * |b x|)
    (u : L2FormHilbert g μ k) :
    ‖multiplyL2FormHilbert g μ a ha A hA hab u‖ ≤
      C * ‖multiplyL2FormHilbert g μ b hb B hB hbb u‖ := by
  let P := multiplyL2FormHilbert (k := k) g μ a ha A hA hab
  let Q := multiplyL2FormHilbert (k := k) g μ b hb B hB hbb
  refine UniformSpace.Completion.induction_on u
    (p := fun u => ‖P u‖ ≤ C * ‖Q u‖) ?_ ?_
  · exact isClosed_le (continuous_norm.comp P.continuous)
      (continuous_const.mul (continuous_norm.comp Q.continuous))
  · intro v
    have hp := formNormSq_integrable g μ _
      (multiplyL2FormLinear g μ a ha A hA hab v).toSection_l2
    have hq := formNormSq_integrable g μ _
      (multiplyL2FormLinear g μ b hb B hB hbb v).toSection_l2
    have hi : (∫ x, formNormSq g.form
        (multiplyRealForm a v.toSection) x ∂μ) ≤
        C ^ 2 * ∫ x, formNormSq g.form (multiplyRealForm b v.toSection) x ∂μ := by
      rw [← integral_const_mul]
      apply integral_mono hp (hq.const_mul _)
      intro x
      change formNormSq g.form (multiplyRealForm a v.toSection) x ≤
        C ^ 2 * formNormSq g.form (multiplyRealForm b v.toSection) x
      rw [multiplyRealForm_normSq, multiplyRealForm_normSq]
      have hs := (sq_le_sq₀ (abs_nonneg (a x))
        (mul_nonneg hC (abs_nonneg (b x)))).2 (hcmp x)
      simp only [mul_pow, sq_abs] at hs
      nlinarith [mul_le_mul_of_nonneg_right hs
        (formNormSq_nonneg g.form v.toSection x)]
    have heP : ‖P (realizeL2Form g μ v)‖ ^ 2 =
        ∫ x, formNormSq g.form (multiplyRealForm a v.toSection) x ∂μ := by
      dsimp only [P]
      rw [multiplyL2FormHilbert_realize, realizeL2Form_norm_sq]
      rfl
    have heQ : ‖Q (realizeL2Form g μ v)‖ ^ 2 =
        ∫ x, formNormSq g.form (multiplyRealForm b v.toSection) x ∂μ := by
      dsimp only [Q]
      rw [multiplyL2FormHilbert_realize, realizeL2Form_norm_sq]
      rfl
    rw [← heP, ← heQ] at hi
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (norm_nonneg _))).mp
    change ‖P (realizeL2Form g μ v)‖ ^ 2 ≤ (C * ‖Q (realizeL2Form g μ v)‖) ^ 2
    simpa only [mul_pow] using hi

end Yau.NodeProofs.P06Aux.Davies
