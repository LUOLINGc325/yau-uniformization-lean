import Yau.LeafProofs.L14CompactBKN

set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped Manifold Topology ContDiff ComplexOrder ENNReal Matrix
open MeasureTheory Bundle Filter Module

namespace Yau.LeafProofs.L14Aux
open BundleDbar

def complexTopTest {n r : ℕ} (α : Fin r) (ψ : ComplexVector n → ℂ) (z : ComplexVector n) :
    ComplexVector r := ψ z • stdVec α

theorem complexTopTest_properties {n r : ℕ} (α : Fin r) (ψ : ComplexVector n → ℂ)
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ) :
    ContDiff ℝ ∞ (complexTopTest α ψ) ∧ HasCompactSupport (complexTopTest α ψ) ∧
      tsupport (complexTopTest α ψ) ⊆ tsupport ψ := by
  let f : ℂ → ComplexVector r := fun t => t • stdVec α
  have hf : f 0 = 0 := by simp [f]
  exact ⟨hψ.smul contDiff_const, hc.comp_left hf, tsupport_comp_subset hf ψ⟩

theorem complexTopTest_apply {n r : ℕ} (α β : Fin r) (ψ : ComplexVector n → ℂ) (z : ComplexVector n) :
    complexTopTest α ψ z β = if β = α then ψ z else 0 := by
  classical
  by_cases h : β = α
  · subst β; simp [complexTopTest, stdVec, PiLp.single_apply]
  · simp [complexTopTest, stdVec, PiLp.single_apply, h]

theorem modelTopDbar_complexTopTest {n r : ℕ} (α β : Fin r) (ψ : ComplexVector n → ℂ)
    (z : ComplexVector n) (i : Fin n) :
    modelTopDbar (complexTopTest α ψ) z i β =
      if β = α then wirtBar ψ z (stdVec i) else 0 := by
  classical
  change wirtBar (fun w => complexTopTest α ψ w β) z (stdVec i) = _
  by_cases h : β = α
  · simp only [complexTopTest_apply, h, ite_true]
  · simp only [complexTopTest_apply, h, ite_false]
    simp [wirtBar]

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
theorem adjoint_graph_scalar_distribution
    (U : WeightedOneSection E g μ hμ h hh φ hφ)
    (S : WeightedTopSection E g μ hμ h hh φ hφ)
    (hUS : (realizeWeightedOneSection E g μ hμ h hh φ hφ U,
      realizeWeightedTopSection E g μ hμ h hh φ hφ S) ∈
      (weightedMaximalDbar E g μ hμ h hh φ hφ).adjoint.graph)
    (a : M.Carrier) (α : Fin r) (ψ : ComplexVector n → ℂ)
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ ⊆ localDomain (r := r) E a) :
    (∫ z, star (weightedTopDualCoefficient (r := r) E h φ S.1 a z α) * ψ z ∂lebesgueC n) =
      ∫ z, ∑ i, star (chartOneDual (r := r) E g.form h φ a
        (fun w j => coefficients (r := r) E U.1 a w (fun _ => j)) z i α) *
        wirtBar ψ z (stdVec i) ∂lebesgueC n := by
  classical
  let F := fun w j => coefficients (r := r) E U.1 a w (fun _ => j)
  let G := complexTopTest α ψ
  obtain ⟨hG, hcG, hsG⟩ := complexTopTest_properties α ψ hψ hc
  have hsGO := hsG.trans hs
  have hp := adjoint_graph_chart_test_pairing E g μ hμ h hh φ hφ hE U S hUS a G hG hcG hsGO
  have hpointL (z : ComplexVector n) :
      (∑ β, ∑ γ, star (coefficients (r := r) E S.1 a z Fin.elim0 β) *
        BundleDbar.metricMatrix (r := r) E h a z β γ * G z γ) *
        (Real.exp (-φ (chartInv a z)) : ℂ) =
      star (weightedTopDualCoefficient (r := r) E h φ S.1 a z α) * ψ z := by
    by_cases hz : z ∈ localDomain (r := r) E a
    · rw [hermitian_real_weight_pairing _ (metricMatrix_posDef E h a z hz).isHermitian]
      simp [G, complexTopTest_apply, weightedTopDualCoefficient, Matrix.mulVec, dotProduct]
    · have hzψ : ψ z = 0 := image_eq_zero_of_notMem_tsupport (fun hn => hz (hs hn))
      simp only [G, complexTopTest, hzψ, zero_smul, PiLp.zero_apply, mul_zero,
        Finset.sum_const_zero, zero_mul]
  have hpointR (z : ComplexVector n) :
      (∑ i, ∑ β, star (F z i β) * chartOneDual (r := r) E g.form h φ a (modelTopDbar G) z i β) =
      ∑ i, star (chartOneDual (r := r) E g.form h φ a F z i α) * wirtBar ψ z (stdVec i) := by
    by_cases hz : z ∈ localDomain (r := r) E a
    · rw [chartOneDual_conj_symm E g.form h φ a z hz F (modelTopDbar G)]
      simp only [G, modelTopDbar_complexTopTest]
      simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    · have hdG : modelTopDbar G z = 0 := image_eq_zero_of_notMem_tsupport
        (fun hn => hz ((tsupport_modelTopDbar_subset G).trans hsGO hn))
      have hdψ (i : Fin n) : wirtBar ψ z (stdVec i) = 0 := by
        by_contra hn
        exact hz (hs (support_wirtBar_subset ψ (stdVec i) hn))
      simp only [chartOneDual, hdG, Pi.zero_apply, PiLp.zero_apply, hdψ,
        mul_zero, Finset.sum_const_zero]
  calc
    _ = ∫ z, (∑ β, ∑ γ, star (coefficients (r := r) E S.1 a z Fin.elim0 β) *
        BundleDbar.metricMatrix (r := r) E h a z β γ * G z γ) *
        (Real.exp (-φ (chartInv a z)) : ℂ) ∂lebesgueC n :=
      integral_congr_ae (Eventually.of_forall fun z => (hpointL z).symm)
    _ = _ := hp
    _ = _ := integral_congr_ae (Eventually.of_forall hpointR)

end Yau.LeafProofs.L14Aux
