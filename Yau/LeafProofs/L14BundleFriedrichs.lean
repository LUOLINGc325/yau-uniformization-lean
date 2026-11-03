import Yau.LeafProofs.L14LocalFriedrichs

noncomputable section
open scoped Manifold Topology ContDiff
open MeasureTheory Bundle Filter Module

namespace Yau.LeafProofs.L14Aux
open BundleDbar

variable {n r : ℕ} {M : ComplexManifold n}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

variable (g : Yau.SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
  (h : Metric E) (hh : BundleDbar.SmoothMetric (r := r) E h) (φ : M.Carrier → ℝ) (hφ : SmoothFn φ)
  (hE : Holomorphic (r := r) E)

include hE in
/-- An actual rough adjoint-and-dbar bundle graph has a common smooth
finite-system approximation whose supports stay in one fixed chart compact. -/
theorem exists_localized_bundle_graph_approx
    (U : WeightedOneSection E g μ hμ h hh φ hφ)
    (S : WeightedTopSection E g μ hμ h hh φ hφ)
    (hUS : (realizeWeightedOneSection E g μ hμ h hh φ hφ U,
      realizeWeightedTopSection E g μ hμ h hh φ hφ S) ∈
      (weightedMaximalDbar E g μ hμ h hh φ hφ).adjoint.graph)
    (f : NQForm E 2) (huf : WeakDbar (r := r) E U.1 f)
    (a : M.Carrier) (χ : ComplexVector n → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hcχ : HasCompactSupport χ) (hsχ : tsupport χ ⊆ localDomain (r := r) E a) :
    ∃ (L : Set (ComplexVector n)) (V : ℕ → ComplexVector n → (Fin n × Fin r) → ℂ),
      IsCompact L ∧ L ⊆ localDomain (r := r) E a ∧
      (∀ j c, ContDiff ℝ ∞ (fun z => V j z c) ∧ tsupport (fun z => V j z c) ⊆ L) ∧
      (∀ c, (∀ j, MemLp (fun z => V j z c - localizedBundleSystemInput (r := r) E U.1 a χ z c)
        2 (lebesgueC n)) ∧
        Tendsto (fun j => ∫ z, ‖V j z c - localizedBundleSystemInput (r := r) E U.1 a χ z c‖ ^ 2
          ∂lebesgueC n) atTop (𝓝 0)) ∧
      ∀ row, (∀ j, MemLp (fun z => complexFirstOrderSystemApply realVec
        (bundleFirstOrderDerivative (r := r) E g.form h φ a)
        (bundleFirstOrderValue (r := r) E g.form h φ a) (V j) z row -
        localizedBundleSystemOutput (r := r) E g.form h φ U.1 S.1 f a χ z row) 2 (lebesgueC n)) ∧
        Tendsto (fun j => ∫ z, ‖complexFirstOrderSystemApply realVec
          (bundleFirstOrderDerivative (r := r) E g.form h φ a)
          (bundleFirstOrderValue (r := r) E g.form h φ a) (V j) z row -
          localizedBundleSystemOutput (r := r) E g.form h φ U.1 S.1 f a χ z row‖ ^ 2 ∂lebesgueC n)
          atTop (𝓝 0) := by
  apply exists_fixed_support_complex_firstOrder_graph_approx_norm
    (localDomain_isOpen E a) hcχ hsχ realVec
    (bundleFirstOrderDerivative (r := r) E g.form h φ a)
    (bundleFirstOrderValue (r := r) E g.form h φ a)
    (bundleFirstOrderDerivative_contDiffOn E g h hh φ hφ a)
    (bundleFirstOrderValue_contDiffOn E g h hh φ hφ a)
    (localizedBundleSystemInput (r := r) E U.1 a χ)
    (localizedBundleSystemOutput (r := r) E g.form h φ U.1 S.1 f a χ)
  · exact fun c => (localizedBundleSystemInput_properties E U.1 U.2.1 a χ hχ hcχ hsχ c).1
  · exact fun row => (localizedBundleSystemOutput_properties E g h hh φ hφ U.1 U.2.1 S.1 S.2.1
      f huf.2.1 a χ hχ hcχ hsχ row).1
  · exact fun c => (localizedBundleSystemInput_properties E U.1 U.2.1 a χ hχ hcχ hsχ c).2
  · exact fun row => (localizedBundleSystemOutput_properties E g h hh φ hφ U.1 U.2.1 S.1 S.2.1
      f huf.2.1 a χ hχ hcχ hsχ row).2
  · exact bundle_graph_localized_complex_rows E g μ hμ h hh φ hφ hE U S hUS f huf a χ hχ hcχ hsχ

end Yau.LeafProofs.L14Aux
