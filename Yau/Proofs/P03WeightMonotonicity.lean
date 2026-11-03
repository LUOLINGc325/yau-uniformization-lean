import Yau.LeafProofs.L14

open MeasureTheory

noncomputable section

namespace Yau.NodeProofs.P03Aux

open Yau.BundleDbar Yau.LeafProofs.L14Aux

variable {n r : ℕ} {M : ComplexManifold n}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (Bundle.TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

theorem weightedTopNormSq_antitone_weight (g : HermitianField M) (h : Metric (M := M) E)
    (μ : Measure M.Carrier) (u : NQForm E 0) {φ Φ : M.Carrier → ℝ}
    (hle : ∀ x, φ x ≤ Φ x) :
    weightedNormSq (r := r) E g h μ Φ u ≤ weightedNormSq (r := r) E g h μ φ u := by
  apply lintegral_mono
  intro x
  exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (neg_le_neg (hle x))) (formNormSq_top_nonneg E g h u x))

theorem weightedTopL2_mono_weight (g : HermitianField M) (h : Metric (M := M) E)
    (μ : Measure M.Carrier) (u : NQForm E 0) {φ Φ : M.Carrier → ℝ}
    (hle : ∀ x, φ x ≤ Φ x) (hu : WeightedL2 (r := r) E g h μ φ u) :
    WeightedL2 (r := r) E g h μ Φ u :=
  ⟨hu.1, (weightedTopNormSq_antitone_weight E g h μ u hle).trans_lt hu.2⟩

end Yau.NodeProofs.P03Aux
