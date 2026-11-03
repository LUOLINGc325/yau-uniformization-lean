import Yau.LeafProofs.L14CurlRows

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

abbrev BundleSystemRow (n r : ℕ) := Sum (Fin r) ((Fin n × Fin n) × Fin r)

def bundleFirstOrderDerivative (g : HermitianField M) (h : Metric E) (φ : M.Carrier → ℝ)
    (a : M.Carrier) (row : BundleSystemRow n r) (c : Fin n × Fin r) (p : RIdx n)
    (z : ComplexVector n) : ℂ := match row with
  | .inl α => weightedAdjointFirstOrderDerivative (r := r) E g h φ a α c p z
  | .inr k => curlFirstOrderDerivative k c p z

def bundleFirstOrderValue (g : HermitianField M) (h : Metric E) (φ : M.Carrier → ℝ)
    (a : M.Carrier) (row : BundleSystemRow n r) (c : Fin n × Fin r) (z : ComplexVector n) : ℂ := match row with
  | .inl α => weightedAdjointFirstOrderValue (r := r) E g h φ a α c z
  | .inr k => curlFirstOrderValue k c z

def bundleSystemInput (u : NQForm E 1) (a : M.Carrier) (z : ComplexVector n) (c : Fin n × Fin r) : ℂ :=
  coefficients (r := r) E u a z (fun _ => c.1) c.2

def bundleSystemOutput (h : Metric E) (φ : M.Carrier → ℝ) (S : NQForm E 0) (f : NQForm E 2)
    (a : M.Carrier) (z : ComplexVector n) (row : BundleSystemRow n r) : ℂ := match row with
  | .inl α => weightedTopDualCoefficient (r := r) E h φ S a z α
  | .inr k => coefficients (r := r) E f a z ![k.1.1,k.1.2] k.2

theorem bundleFirstOrderDerivative_contDiffOn (g : Yau.SmoothMetric M) (h : Metric E)
    (hh : BundleDbar.SmoothMetric (r := r) E h) (φ : M.Carrier → ℝ) (hφ : SmoothFn φ)
    (a : M.Carrier) (row : BundleSystemRow n r) (c : Fin n × Fin r) (p : RIdx n) :
    ContDiffOn ℝ ∞ (bundleFirstOrderDerivative (r := r) E g.form h φ a row c p)
      (localDomain (r := r) E a) := by
  cases row with
  | inl α =>
    exact contDiffOn_const.mul (localDualCoefficient_contDiffOn E g h hh φ hφ a α c p.1)
  | inr k => exact contDiffOn_const

theorem bundleFirstOrderValue_contDiffOn (g : Yau.SmoothMetric M) (h : Metric E)
    (hh : BundleDbar.SmoothMetric (r := r) E h) (φ : M.Carrier → ℝ) (hφ : SmoothFn φ)
    (a : M.Carrier) (row : BundleSystemRow n r) (c : Fin n × Fin r) :
    ContDiffOn ℝ ∞ (bundleFirstOrderValue (r := r) E g.form h φ a row c)
      (localDomain (r := r) E a) := by
  cases row with
  | inl α =>
    apply ContDiffOn.neg
    apply ContDiffOn.sum
    intro i _
    exact wirt_contDiffOn (localDomain_isOpen E a) _
      (localDualCoefficient_contDiffOn E g h hh φ hφ a α c i) (stdVec i)
  | inr k => exact contDiffOn_const

theorem bundleFirstOrder_apply (g : Yau.SmoothMetric M) (h : Metric E)
    (hh : BundleDbar.SmoothMetric (r := r) E h) (φ : M.Carrier → ℝ) (hφ : SmoothFn φ)
    (a : M.Carrier) (F : ComplexVector n → Fin n → ComplexVector r) (hF : ContDiff ℝ ∞ F)
    (z : ComplexVector n) (hz : z ∈ localDomain (r := r) E a) (row : BundleSystemRow n r) :
    complexFirstOrderSystemApply realVec (bundleFirstOrderDerivative (r := r) E g.form h φ a)
      (bundleFirstOrderValue (r := r) E g.form h φ a) (fun w c => F w c.1 c.2) z row =
    match row with
    | .inl α => (∑ β, BundleDbar.metricMatrix (r := r) E h a z α β *
        chartDbarAdjoint (r := r) E g.form h φ a F z β) * (Real.exp (-φ (chartInv a z)) : ℂ)
    | .inr k => modelOneDbar F z k.1.1 k.1.2 k.2 := by
  cases row with
  | inl α => exact weightedAdjointFirstOrder_apply E g h hh φ hφ a F hF z hz α
  | inr k => exact curlFirstOrder_apply (fun w c => F w c.1 c.2) z k

variable (g : Yau.SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
  (h : Metric E) (hh : BundleDbar.SmoothMetric (r := r) E h) (φ : M.Carrier → ℝ) (hφ : SmoothFn φ)
  (hE : Holomorphic (r := r) E)

include hE in
theorem bundle_graph_complex_firstOrder_rows
    (U : WeightedOneSection E g μ hμ h hh φ hφ)
    (S : WeightedTopSection E g μ hμ h hh φ hφ)
    (hUS : (realizeWeightedOneSection E g μ hμ h hh φ hφ U,
      realizeWeightedTopSection E g μ hμ h hh φ hφ S) ∈
      (weightedMaximalDbar E g μ hμ h hh φ hφ).adjoint.graph)
    (f : NQForm E 2) (huf : WeakDbar (r := r) E U.1 f)
    (a : M.Carrier) (row : BundleSystemRow n r) (ψ : ComplexVector n → ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ ⊆ localDomain (r := r) E a) :
    (∫ z, (ψ z : ℂ) * bundleSystemOutput (r := r) E h φ S.1 f a z row ∂lebesgueC n) =
      ∫ z, ∑ c : Fin n × Fin r, bundleSystemInput (r := r) E U.1 a z c *
        (-(∑ p : RIdx n,
          (bundleFirstOrderDerivative (r := r) E g.form h φ a row c p z * (fderiv ℝ ψ z (realVec p) : ℂ) +
          fderiv ℝ (bundleFirstOrderDerivative (r := r) E g.form h φ a row c p) z (realVec p) * (ψ z : ℂ))) +
          bundleFirstOrderValue (r := r) E g.form h φ a row c z * (ψ z : ℂ)) ∂lebesgueC n := by
  cases row with
  | inl α => exact adjoint_graph_complex_firstOrder_rows E g μ hμ h hh φ hφ hE U S hUS a α ψ hψ hc hs
  | inr k => exact weakDbar_complex_firstOrder_curl_rows E U.1 f huf a k ψ hψ hc hs

end Yau.LeafProofs.L14Aux
