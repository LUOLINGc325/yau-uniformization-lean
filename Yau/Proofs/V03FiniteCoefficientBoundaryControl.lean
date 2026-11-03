import Yau.Proofs.V03CoefficientBoundaryEnergy

/-! One constant controls any fixed finite family of genuine smooth
intrinsic coefficients before every original admissible disc. -/

open scoped Topology ContDiff

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

theorem finiteCoefficients_uniform_boundary_control {n q : ℕ} {X : KahlerManifold n}
    {d : VariationData X q} (hd : VariationSetup d) (j : ℕ)
    {ι : Type*} [Fintype ι] {b : ι → CotangentPoint X.manifold → ℂ}
    (hb : ∀ i x, ContDiffOn ℝ ∞ (fun z => b i (cotangentChartInv x z)) (cotangentTarget x)) :
    ∃ C M : ℝ, 0 ≤ C ∧ 0 ≤ M ∧ ∀ F : VariationDisc X,
      AdmissibleVariationDisc d j F → ∀ i,
      (∀ θ, ‖b i (F.f (circlePoint θ))‖ ≤ M) ∧
      boundaryDSq (fun θ (_ : Unit) => b i (F.f (circlePoint θ))) ≤
        ENNReal.ofReal C * variationEnergy d j F := by
  classical
  choose C M hC hM hbound using
    (fun i => cotangentCoefficient_uniform_boundary_control hd j (hb i))
  refine ⟨∑ i, C i, ∑ i, M i, Finset.sum_nonneg (fun i _ => hC i),
    Finset.sum_nonneg (fun i _ => hM i), fun F hF i => ?_⟩
  have hCi : C i ≤ ∑ i, C i := Finset.single_le_sum (fun i _ => hC i) (Finset.mem_univ i)
  have hMi : M i ≤ ∑ i, M i := Finset.single_le_sum (fun i _ => hM i) (Finset.mem_univ i)
  refine ⟨fun θ => ((hbound i F hF).1 θ).trans hMi, (hbound i F hF).2.trans ?_⟩
  gcongr

end Yau.Blueprint.V03Proof
