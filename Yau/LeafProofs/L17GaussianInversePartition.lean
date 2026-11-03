import Yau.LeafProofs.L17GaussianResidualOperator

open Set Metric
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17Aux
open L17HolderAux L17SchauderAux L17ParabolicOperatorAux
variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}

theorem BoundedChartFamily.exists_uniform_approximate_scalar_inverse_with_partition
    (A : BoundedChartFamily g) (hg : MetricSmooth g) :
    ∃ N : ℕ, ∃ B : ℕ → ℝ, ∃ D E : Ioo (0 : ℝ) 1 → ℝ,
      (∀ k,0<B k) ∧ (∀ γ,0 < D γ) ∧ (∀ γ,0 < E γ) ∧
      ∀ ε : ℝ, 0 < ε → ∃ P : UniformChartPartition g,
        P.charts=A ∧ P.radius<ε ∧ P.radius≤1 ∧ 2*P.radius<A.radius ∧ P.overlapBudget=N ∧
        (∀ k (p : P.centers) q z, z ∈ ball (0 : ComplexVector n) (2*P.radius) →
          ‖iteratedFDeriv ℝ k (fun w => P.weight p (P.charts.chart q w)) z‖ ≤ B k*(P.radius⁻¹)^k ∧
          ‖iteratedFDeriv ℝ k (fun w => P.localization p (P.charts.chart q w)) z‖ ≤ B k*(P.radius⁻¹)^k) ∧
        ∀ (T : ℝ) (hT : 0 < T) (hSmall : T ≤ P.radius^2) (hr : P.radius≤1), ∀ γ : Ioo (0 : ℝ) 1,
          ∃ Q : HolderSpace P T γ.val →L[ℝ] SchauderSpace P T γ.val hT,
            (∀ f,schauderFun (Q f)=gaussianParametrixFun P T hT.le f) ∧ ‖Q‖ ≤ D γ ∧
            ‖(scalarParabolicCLM P T γ.val hT hSmall γ.property.2.le hr).comp Q-
              ContinuousLinearMap.id ℝ (HolderSpace P T γ.val)‖ ≤
              E γ*(P.radius+(T/P.radius^2)^(1/2 : ℝ)+(T/P.radius^2)^((1-γ.val)/2)) := by
  obtain ⟨N,B,C,K,R,D,hB,hC,hK,hR,hD,hPart⟩ := A.exists_uniform_gaussian_parametrix hg
  choose L hL hBudget using fun γ : Ioo (0 : ℝ) 1 =>
    exists_uniform_gaussian_operator_residual_budget A hg N γ.val γ.property.1 γ.property.2
  refine ⟨N,B,D,fun γ => L γ*R γ,hB,hD,fun γ => mul_pos (hL γ) (hR γ),?_⟩
  intro ε hε
  obtain ⟨P,hA,hρε,hr,hρA,hN,hJets,hAll⟩ := hPart ε hε
  refine ⟨P,hA,hρε,hr,hρA,hN,hJets,?_⟩
  intro T hT hSmall hr' γ
  obtain ⟨hKernel,Q,hValue,hNorm⟩ := hAll T hT hSmall γ
  refine ⟨Q,hValue,hNorm,?_⟩
  apply hBudget γ P hA hN.le hr' hρA T hT hSmall C (R γ) (hR γ).le Q hValue
  · intro f p
    exact (hKernel f p).1
  · intro f p
    simpa only [add_assoc] using (hKernel f p).2.2.2.2


end Yau.LeafProofs.L17Aux
