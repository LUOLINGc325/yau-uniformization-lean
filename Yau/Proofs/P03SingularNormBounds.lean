import Yau.Proofs.P03WeightMonotonicity

open scoped Manifold Topology ContDiff ENNReal
open Set Filter MeasureTheory

noncomputable section

namespace Yau.NodeProofs.P03Aux

open Yau.BundleDbar Yau.LeafProofs.L14Aux

variable {n r : ℕ} {M : ComplexManifold n}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (Bundle.TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

/-- The singular norm is the supremum of the original regularized
integrands. This definition also keeps the correct value at a pole. -/
def singularTopIntegrand (g : HermitianField M) (h : Metric (M := M) E)
    (φ : ℕ → M.Carrier → ℝ) (u : NQForm E 0) (x : M.Carrier) : ℝ≥0∞ :=
  ⨆ j, ENNReal.ofReal (BundleDbar.formNormSq (r := r) E g h u x * Real.exp (-φ j x))

theorem singularTopIntegrand_lintegral_le (g : Yau.SmoothMetric M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (h : Metric (M := M) E) (hh : BundleDbar.SmoothMetric (r := r) E h)
    (φ : ℕ → M.Carrier → ℝ) (hφ : ∀ j, SmoothFn (φ j))
    (hm : ∀ x, Antitone (fun j => φ j x))
    (u : NQForm E 0) (hu : LocallyL2 (r := r) E u)
    (B : ℝ) (hb : ∀ j, weightedNormSq (r := r) E g.form h μ (φ j) u ≤ ENNReal.ofReal B) :
    ∫⁻ x, singularTopIntegrand (r := r) E g.form h φ u x ∂μ ≤ ENNReal.ofReal B := by
  have hmeas (j : ℕ) : AEMeasurable
      (fun x => ENNReal.ofReal (BundleDbar.formNormSq (r := r) E g.form h u x *
        Real.exp (-φ j x))) μ :=
    ENNReal.measurable_ofReal.comp_aemeasurable
      ((formNormSq_top_aemeasurable E g μ hμ h hh u hu).mul
        (Real.continuous_exp.comp (Yau.LeafProofs.L18Aux.continuous_of_smoothFn (hφ j)).neg).measurable.aemeasurable)
  have hmono (x : M.Carrier) : Monotone (fun j =>
      ENNReal.ofReal (BundleDbar.formNormSq (r := r) E g.form h u x * Real.exp (-φ j x))) := by
    intro i j hij
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (neg_le_neg (hm x hij))) (formNormSq_top_nonneg E g.form h u x))
  change (∫⁻ x, ⨆ j, ENNReal.ofReal (BundleDbar.formNormSq (r := r) E g.form h u x *
    Real.exp (-φ j x)) ∂μ) ≤ ENNReal.ofReal B
  rw [lintegral_iSup' hmeas (Eventually.of_forall hmono)]
  exact iSup_le hb

end Yau.NodeProofs.P03Aux
