import Yau.LeafProofs.L14DivergenceSystem

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

def weightedAdjointFirstOrderDerivative (g : HermitianField M) (h : Metric E) (φ : M.Carrier → ℝ)
    (a : M.Carrier) : Fin r → (Fin n × Fin r) → RIdx n → ComplexVector n → ℂ :=
  wirtDivergenceDerivative (localDualCoefficient (r := r) E g h φ a)

def weightedAdjointFirstOrderValue (g : HermitianField M) (h : Metric E) (φ : M.Carrier → ℝ)
    (a : M.Carrier) : Fin r → (Fin n × Fin r) → ComplexVector n → ℂ :=
  wirtDivergenceValue (localDualCoefficient (r := r) E g h φ a)

theorem weightedAdjointFirstOrder_apply (g : Yau.SmoothMetric M) (h : Metric E)
    (hh : BundleDbar.SmoothMetric (r := r) E h) (φ : M.Carrier → ℝ) (hφ : SmoothFn φ)
    (a : M.Carrier) (F : ComplexVector n → Fin n → ComplexVector r) (hF : ContDiff ℝ ∞ F)
    (z : ComplexVector n) (hz : z ∈ localDomain (r := r) E a) (α : Fin r) :
    complexFirstOrderSystemApply realVec (weightedAdjointFirstOrderDerivative (r := r) E g.form h φ a)
      (weightedAdjointFirstOrderValue (r := r) E g.form h φ a)
      (fun w c => F w c.1 c.2) z α =
    (∑ β, BundleDbar.metricMatrix (r := r) E h a z α β *
      chartDbarAdjoint (r := r) E g.form h φ a F z β) * (Real.exp (-φ (chartInv a z)) : ℂ) := by
  let C := localDualCoefficient (r := r) E g.form h φ a
  have hC (c : Fin n × Fin r) (i : Fin n) : DifferentiableAt ℝ (C α c i) z :=
    ((localDualCoefficient_contDiffOn E g h hh φ hφ a α c i).contDiffAt
      ((localDomain_isOpen E a).mem_nhds hz)).differentiableAt (by simp)
  have hdF (c : Fin n × Fin r) : DifferentiableAt ℝ (fun w => F w c.1 c.2) z :=
    (((contDiff_piLp 2).mp ((contDiff_pi.mp hF) c.1) c.2)).differentiable (by simp) z
  change complexFirstOrderSystemApply realVec (wirtDivergenceDerivative C) (wirtDivergenceValue C)
    (fun w c => F w c.1 c.2) z α = _
  rw [wirtDivergence_system_apply C _ z α hC hdF]
  have hB (i : Fin n) : (fun w => ∑ c : Fin n × Fin r, C α c i w * F w c.1 c.2) =
      (fun w => chartOneDual (r := r) E g.form h φ a F w i α) := by
    funext w
    exact (chartOneDual_eq_flat_sum E g.form h φ a F w i α).symm
  simp_rw [hB]
  exact (chartDbarAdjoint_dual E g.form h φ a F z hz α).symm

variable (g : Yau.SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
  (h : Metric E) (hh : BundleDbar.SmoothMetric (r := r) E h) (φ : M.Carrier → ℝ) (hφ : SmoothFn φ)
  (hE : Holomorphic (r := r) E)

include hE in
theorem adjoint_graph_complex_firstOrder_rows
    (U : WeightedOneSection E g μ hμ h hh φ hφ)
    (S : WeightedTopSection E g μ hμ h hh φ hφ)
    (hUS : (realizeWeightedOneSection E g μ hμ h hh φ hφ U,
      realizeWeightedTopSection E g μ hμ h hh φ hφ S) ∈
      (weightedMaximalDbar E g μ hμ h hh φ hφ).adjoint.graph)
    (a : M.Carrier) (α : Fin r) (ψ : ComplexVector n → ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ ⊆ localDomain (r := r) E a) :
    (∫ z, (ψ z : ℂ) * weightedTopDualCoefficient (r := r) E h φ S.1 a z α ∂lebesgueC n) =
      ∫ z, ∑ c : Fin n × Fin r, coefficients (r := r) E U.1 a z (fun _ => c.1) c.2 *
        (-(∑ p : RIdx n,
          (weightedAdjointFirstOrderDerivative (r := r) E g.form h φ a α c p z * (fderiv ℝ ψ z (realVec p) : ℂ) +
          fderiv ℝ (weightedAdjointFirstOrderDerivative (r := r) E g.form h φ a α c p) z (realVec p) * (ψ z : ℂ))) +
          weightedAdjointFirstOrderValue (r := r) E g.form h φ a α c z * (ψ z : ℂ)) ∂lebesgueC n := by
  let C := localDualCoefficient (r := r) E g.form h φ a
  let F := fun w j => coefficients (r := r) E U.1 a w (fun _ => j)
  have hψC : ContDiff ℝ ∞ (fun z => (ψ z : ℂ)) := Complex.ofRealCLM.contDiff.comp hψ
  have hcψC : HasCompactSupport (fun z => (ψ z : ℂ)) := hc.comp_left Complex.ofReal_zero
  have hsψC : tsupport (fun z => (ψ z : ℂ)) ⊆ localDomain (r := r) E a :=
    (tsupport_comp_subset Complex.ofReal_zero ψ).trans hs
  have he := adjoint_graph_scalar_distribution_unconjugated E g μ hμ h hh φ hφ hE
    U S hUS a α _ hψC hcψC hsψC
  have hpoint (z : ComplexVector n) :
      (∑ i, chartOneDual (r := r) E g.form h φ a F z i α * wirt (fun w => (ψ w : ℂ)) z (stdVec i)) =
      ∑ c : Fin n × Fin r, F z c.1 c.2 *
        (-(∑ p : RIdx n,
          (weightedAdjointFirstOrderDerivative (r := r) E g.form h φ a α c p z * (fderiv ℝ ψ z (realVec p) : ℂ) +
          fderiv ℝ (weightedAdjointFirstOrderDerivative (r := r) E g.form h φ a α c p) z (realVec p) * (ψ z : ℂ))) +
          weightedAdjointFirstOrderValue (r := r) E g.form h φ a α c z * (ψ z : ℂ)) := by
    by_cases hz : z ∈ localDomain (r := r) E a
    · have hC (c : Fin n × Fin r) (i : Fin n) : DifferentiableAt ℝ (C α c i) z :=
        ((localDualCoefficient_contDiffOn E g h hh φ hφ a α c i).contDiffAt
          ((localDomain_isOpen E a).mem_nhds hz)).differentiableAt (by simp)
      have hformal (c : Fin n × Fin r) :
          (-(∑ p : RIdx n,
            (weightedAdjointFirstOrderDerivative (r := r) E g.form h φ a α c p z * (fderiv ℝ ψ z (realVec p) : ℂ) +
            fderiv ℝ (weightedAdjointFirstOrderDerivative (r := r) E g.form h φ a α c p) z (realVec p) * (ψ z : ℂ))) +
            weightedAdjointFirstOrderValue (r := r) E g.form h φ a α c z * (ψ z : ℂ)) =
          ∑ i, C α c i z * wirt (fun w => (ψ w : ℂ)) z (stdVec i) :=
        wirtDivergence_formal_test_row C α c z (hC c) ψ (hψ.differentiable (by simp) z)
      simp_rw [hformal, chartOneDual_eq_flat_sum E g.form h φ a F z,
        Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro c _
      apply Finset.sum_congr rfl
      intro i _
      ring
    · have hn : z ∉ tsupport ψ := fun h => hz (hs h)
      have hψz : ψ z = 0 := image_eq_zero_of_notMem_tsupport hn
      have hdψ : fderiv ℝ ψ z = 0 := fderiv_of_notMem_tsupport (𝕜 := ℝ) hn
      have hw (i : Fin n) : wirt (fun w => (ψ w : ℂ)) z (stdVec i) = 0 := by
        rw [wirt_ofReal_eq_real_directions ψ z (hψ.differentiable (by simp) z) i, hdψ]
        simp
      simp only [hψz, hdψ, hw, ContinuousLinearMap.zero_apply, Complex.ofReal_zero,
        mul_zero, Finset.sum_const_zero, zero_add, neg_zero]
  calc
    _ = ∫ z, weightedTopDualCoefficient (r := r) E h φ S.1 a z α * (ψ z : ℂ) ∂lebesgueC n :=
      integral_congr_ae (Eventually.of_forall fun z => mul_comm _ _)
    _ = _ := he
    _ = _ := integral_congr_ae (Eventually.of_forall hpoint)

end Yau.LeafProofs.L14Aux
