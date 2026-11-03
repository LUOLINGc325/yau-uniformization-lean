import Yau.Proofs.F04FormMultiplierLimit

open MeasureTheory Filter Set
open scoped Topology InnerProductSpace

noncomputable section

namespace Yau.F04Proof

open Yau.LeafProofs.L03

variable {n k : ℕ} {M : ComplexManifold n}

theorem realize_multiply_sub (g : SmoothMetric M) (μ : Measure M.Carrier)
    (A : RealForm M k) (c d : M.Carrier → ℝ)
    (hc : L2RealForm g.form μ (multiplyRealForm c A))
    (hd : L2RealForm g.form μ (multiplyRealForm d A))
    (hcd : L2RealForm g.form μ (multiplyRealForm (c - d) A)) :
    realizeL2Form g μ (L2FormSpace.ofSection (multiplyRealForm (c - d) A) hcd) =
      realizeL2Form g μ (L2FormSpace.ofSection (multiplyRealForm c A) hc) -
        realizeL2Form g μ (L2FormSpace.ofSection (multiplyRealForm d A) hd) := by
  rw [← realizeL2Form_sub]
  apply congrArg (realizeL2Form g μ)
  apply L2FormSpace.toSection_injective g μ k
  funext x
  exact sub_smul (c x) (d x) (A x)

/-- Strong convergence of bounded scalar multipliers on a fixed actual form;
the weighted hypothesis permits discontinuities precisely on its zero set. -/
theorem bounded_form_multipliers_tendsto
    (g : SmoothMetric M) (μ : Measure M.Carrier)
    (A : RealForm M k) (hA : L2RealForm g.form μ A)
    (c : ℕ → M.Carrier → ℝ) (d : M.Carrier → ℝ)
    (hcm : ∀ j, AEStronglyMeasurable (c j) μ) (hdm : AEStronglyMeasurable d μ)
    (C : ℝ) (hC : 0 ≤ C) (hc : ∀ j x, |c j x| ≤ C) (hd : ∀ x, |d x| ≤ C)
    (hlim : ∀ᵐ x ∂μ, Tendsto
      (fun j => (c j x - d x) ^ 2 * formNormSq g.form A x) atTop (𝓝 0)) :
    Tendsto (fun j => multiplyL2FormHilbert g μ (c j) (hcm j) C hC (hc j)
      (realizeL2Form g μ (L2FormSpace.ofSection A hA))) atTop
      (𝓝 (multiplyL2FormHilbert g μ d hdm C hC hd
        (realizeL2Form g μ (L2FormSpace.ofSection A hA)))) := by
  have hb (j : ℕ) (x : M.Carrier) : |(c j - d) x| ≤ 2 * C := by
    calc
      _ ≤ |c j x| + |d x| := abs_sub _ _
      _ ≤ 2 * C := by linarith [hc j x, hd x]
  have hz := bounded_form_multiplier_tendsto_zero g μ A hA (fun j => c j - d)
    (fun j => (hcm j).sub hdm) (2 * C) (by positivity) hb hlim
  have he (j : ℕ) :
      multiplyL2FormHilbert g μ (c j) (hcm j) C hC (hc j)
          (realizeL2Form g μ (L2FormSpace.ofSection A hA)) -
        multiplyL2FormHilbert g μ d hdm C hC hd
          (realizeL2Form g μ (L2FormSpace.ofSection A hA)) =
      realizeL2Form g μ (L2FormSpace.ofSection (multiplyRealForm (c j - d) A)
        (l2RealForm_multiply_bounded g μ (c j - d) ((hcm j).sub hdm)
          (2 * C) (by positivity) (hb j) A hA)) := by
    rw [multiplyL2FormHilbert_realize, multiplyL2FormHilbert_realize]
    exact (realize_multiply_sub g μ A (c j) d _ _ _).symm
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [he, norm_zero] using hz.norm

end Yau.F04Proof
