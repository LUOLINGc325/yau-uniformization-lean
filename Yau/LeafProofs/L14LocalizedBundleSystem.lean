import Yau.LeafProofs.L14ModelLocalization

set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped Manifold Topology ContDiff ComplexOrder ENNReal Matrix
open MeasureTheory Bundle Filter Module

namespace Yau.LeafProofs.L14Aux
open BundleDbar

variable {n r : ℕ} {M : ComplexManifold n}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

theorem bundleSystemInput_memLp_compact
    (u : NQForm E 1) (hu : LocallyL2 (r := r) E u) (a : M.Carrier)
    (K : Set (ComplexVector n)) (hK : IsCompact K) (hs : K ⊆ localDomain (r := r) E a)
    (c : Fin n × Fin r) :
    MemLp (fun z => bundleSystemInput (r := r) E u a z c) 2 ((lebesgueC n).restrict K) :=
  locallyL2_coefficients_memLp E u hu a (fun _ => c.1) c.2 K hK hs

theorem bundleSystemOutput_memLp_compact
    (h : Metric E) (hh : BundleDbar.SmoothMetric (r := r) E h) (φ : M.Carrier → ℝ) (hφ : SmoothFn φ)
    (S : NQForm E 0) (hS : LocallyL2 (r := r) E S) (f : NQForm E 2) (hf : LocallyL2 (r := r) E f)
    (a : M.Carrier) (K : Set (ComplexVector n)) (hK : IsCompact K) (hs : K ⊆ localDomain (r := r) E a)
    (row : BundleSystemRow n r) :
    MemLp (fun z => bundleSystemOutput (r := r) E h φ S f a z row) 2 ((lebesgueC n).restrict K) := by
  cases row with
  | inl α => exact weightedTopDualCoefficient_memLp_compact E h hh φ hφ S hS a K hK hs α
  | inr k => exact locallyL2_coefficients_memLp E f hf a ![k.1.1,k.1.2] k.2 K hK hs

theorem bundleSystemInput_locallyIntegrableOn
    (u : NQForm E 1) (hu : LocallyL2 (r := r) E u) (a : M.Carrier) (c : Fin n × Fin r) :
    LocallyIntegrableOn (fun z => bundleSystemInput (r := r) E u a z c) (localDomain (r := r) E a) (lebesgueC n) :=
  locallyL2_coefficients_locallyIntegrableOn E u hu a (fun _ => c.1) c.2

theorem bundleSystemOutput_locallyIntegrableOn
    (h : Metric E) (hh : BundleDbar.SmoothMetric (r := r) E h) (φ : M.Carrier → ℝ) (hφ : SmoothFn φ)
    (S : NQForm E 0) (hS : LocallyL2 (r := r) E S) (f : NQForm E 2) (hf : LocallyL2 (r := r) E f)
    (a : M.Carrier) (row : BundleSystemRow n r) :
    LocallyIntegrableOn (fun z => bundleSystemOutput (r := r) E h φ S f a z row)
      (localDomain (r := r) E a) (lebesgueC n) := by
  cases row with
  | inl α => exact weightedTopDualCoefficient_locallyIntegrableOn E h hh φ hφ S hS a α
  | inr k => exact locallyL2_coefficients_locallyIntegrableOn E f hf a ![k.1.1,k.1.2] k.2

def localizedBundleSystemInput (u : NQForm E 1) (a : M.Carrier) (χ : ComplexVector n → ℝ)
    (z : ComplexVector n) (c : Fin n × Fin r) : ℂ := (χ z : ℂ) * bundleSystemInput (r := r) E u a z c

def localizedBundleSystemOutput (g : HermitianField M) (h : Metric E) (φ : M.Carrier → ℝ)
    (u : NQForm E 1) (S : NQForm E 0) (f : NQForm E 2) (a : M.Carrier) (χ : ComplexVector n → ℝ) :
    ComplexVector n → BundleSystemRow n r → ℂ :=
  localizedComplexSystemOutput realVec (bundleFirstOrderDerivative (r := r) E g h φ a) χ
    (bundleSystemInput (r := r) E u a) (bundleSystemOutput (r := r) E h φ S f a)

theorem localizedBundleSystemInput_properties
    (u : NQForm E 1) (hu : LocallyL2 (r := r) E u) (a : M.Carrier)
    (χ : ComplexVector n → ℝ) (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hsχ : tsupport χ ⊆ localDomain (r := r) E a) (c : Fin n × Fin r) :
    MemLp (fun z => localizedBundleSystemInput (r := r) E u a χ z c) 2 (lebesgueC n) ∧
      tsupport (fun z => localizedBundleSystemInput (r := r) E u a χ z c) ⊆ tsupport χ := by
  refine ⟨localizedComplexSystemInput_memLp χ hχ hcχ hsχ _
    (fun K hK hs => bundleSystemInput_memLp_compact E u hu a K hK hs c), ?_⟩
  exact tsupport_mul_subset_left.trans (tsupport_comp_subset Complex.ofReal_zero χ)

theorem localizedBundleSystemOutput_properties (g : Yau.SmoothMetric M) (h : Metric E)
    (hh : BundleDbar.SmoothMetric (r := r) E h) (φ : M.Carrier → ℝ) (hφ : SmoothFn φ)
    (u : NQForm E 1) (hu : LocallyL2 (r := r) E u) (S : NQForm E 0) (hS : LocallyL2 (r := r) E S)
    (f : NQForm E 2) (hf : LocallyL2 (r := r) E f) (a : M.Carrier)
    (χ : ComplexVector n → ℝ) (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hsχ : tsupport χ ⊆ localDomain (r := r) E a) (row : BundleSystemRow n r) :
    MemLp (fun z => localizedBundleSystemOutput (r := r) E g.form h φ u S f a χ z row) 2 (lebesgueC n) ∧
      tsupport (fun z => localizedBundleSystemOutput (r := r) E g.form h φ u S f a χ z row) ⊆ tsupport χ := by
  refine ⟨localizedComplexSystemOutput_memLp (localDomain_isOpen E a) realVec
    (bundleFirstOrderDerivative (r := r) E g.form h φ a)
    (bundleFirstOrderDerivative_contDiffOn E g h hh φ hφ a) χ hχ hcχ hsχ
    _ _ (fun c K hK hs => bundleSystemInput_memLp_compact E u hu a K hK hs c)
    (fun row K hK hs => bundleSystemOutput_memLp_compact E h hh φ hφ S hS f hf a K hK hs row) row, ?_⟩
  exact localizedComplexSystemOutput_tsupport_subset realVec _ χ _ _ row

variable (g : Yau.SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
  (h : Metric E) (hh : BundleDbar.SmoothMetric (r := r) E h) (φ : M.Carrier → ℝ) (hφ : SmoothFn φ)
  (hE : Holomorphic (r := r) E)

include hE in
theorem bundle_graph_localized_complex_rows
    (U : WeightedOneSection E g μ hμ h hh φ hφ)
    (S : WeightedTopSection E g μ hμ h hh φ hφ)
    (hUS : (realizeWeightedOneSection E g μ hμ h hh φ hφ U,
      realizeWeightedTopSection E g μ hμ h hh φ hφ S) ∈
      (weightedMaximalDbar E g μ hμ h hh φ hφ).adjoint.graph)
    (f : NQForm E 2) (huf : WeakDbar (r := r) E U.1 f)
    (a : M.Carrier) (χ : ComplexVector n → ℝ) (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hsχ : tsupport χ ⊆ localDomain (r := r) E a)
    (row : BundleSystemRow n r) (ψ : ComplexVector n → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ) :
    (∫ z, (ψ z : ℂ) * localizedBundleSystemOutput (r := r) E g.form h φ U.1 S.1 f a χ z row ∂lebesgueC n) =
      ∫ z, ∑ c : Fin n × Fin r, localizedBundleSystemInput (r := r) E U.1 a χ z c *
        complexFormalAdjointTestRow realVec (bundleFirstOrderDerivative (r := r) E g.form h φ a)
          (bundleFirstOrderValue (r := r) E g.form h φ a) row c ψ z ∂lebesgueC n :=
  complex_firstOrder_rows_localize (localDomain_isOpen E a) realVec
    (bundleFirstOrderDerivative (r := r) E g.form h φ a) (bundleFirstOrderValue (r := r) E g.form h φ a)
    (bundleFirstOrderDerivative_contDiffOn E g h hh φ hφ a) (bundleFirstOrderValue_contDiffOn E g h hh φ hφ a)
    _ _ (bundleSystemInput_locallyIntegrableOn E U.1 U.2.1 a)
    (bundleSystemOutput_locallyIntegrableOn E h hh φ hφ S.1 S.2.1 f huf.2.1 a)
    (bundle_graph_complex_firstOrder_rows E g μ hμ h hh φ hφ hE U S hUS f huf a)
    χ hχ hcχ hsχ row ψ hψ hcψ

end Yau.LeafProofs.L14Aux
