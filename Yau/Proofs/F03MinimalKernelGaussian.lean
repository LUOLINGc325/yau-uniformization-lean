import Yau.Proofs.F03MinimalExhaustionProducer
import Yau.Proofs.F02InitialRicci
import Yau.LeafProofs.L24Complete

/-! The actual same minimal kernel satisfies the native Gaussian and gradient estimates uniformly before all volumes and exhaustions. -/
noncomputable section
open MeasureTheory Set
open scoped ComplexOrder
namespace Yau.Proofs.F03Aux
open Yau Blueprint HeatConcreteBindings HeatTargetCandidates
variable {n : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem dirichletMinimalKernelCandidate_gaussian_gradient
    (X : KahlerManifold n) (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hf : LocalizedFlow X o h U P ρ) :
    ∃ C₀ c₀ C₁ c₁ : ℝ,0 < C₀ ∧ 0 < c₀ ∧ 0 < C₁ ∧ 0 < c₁ ∧
      ∀ (μ : Measure (Pt X)) (hμ : IsRiemannianVolume X.metric.form μ)
        (O : ℕ → Set (Pt X)) (hO : SmoothExhaustion O) (t : ℝ),0 < t → ∀ x y,
      dirichletMinimalKernelCandidate X.metric X.kahler_metric μ hμ O hO t x y ≤
        C₀*Real.exp (-c₀*distFrom X.metric.form x y^2/t)/
          Real.sqrt ((μ (distBall X.metric.form x (Real.sqrt t))).toReal*
            (μ (distBall X.metric.form y (Real.sqrt t))).toReal) ∧
      Real.sqrt (gradNormSq X.metric.form (fun z =>
        dirichletMinimalKernelCandidate X.metric X.kahler_metric μ hμ O hO t z y) x) ≤
        C₁/Real.sqrt t*Real.exp (-c₁*distFrom X.metric.form x y^2/t)/
          Real.sqrt ((μ (distBall X.metric.form x (Real.sqrt t))).toReal*
            (μ (distBall X.metric.form y (Real.sqrt t))).toReal) := by
  have hn : 0 < n := complexManifold_dimension_pos X.manifold
  obtain ⟨C₀,c₀,hC₀,hc₀,hGauss⟩ := LeafProofs.L19Aux.liYauGaussian n hn
  obtain ⟨C₁,c₁,hC₁,hc₁,hGrad⟩ := LeafProofs.L24 n hn
  have hRic := F02Aux.initialRicci_posSemidef X o h U P ρ hf
  refine ⟨C₀,c₀,C₁,c₁,hC₀,hc₀,hC₁,hc₁,fun μ hμ O hO t ht x y => ?_⟩
  have hKernel := dirichletMinimalKernelCandidate_scalarHeatKernel X.metric X.kahler_metric μ hμ O hO
  exact ⟨hGauss X.manifold X.metric X.complete_metric X.kahler_metric hRic μ hμ
      _ hKernel t ht x y,
    hGrad X.manifold X.metric X.complete_metric X.kahler_metric hRic μ hμ
      _ hKernel t ht x y⟩

end Yau.Proofs.F03Aux
