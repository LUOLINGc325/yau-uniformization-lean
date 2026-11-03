import Yau.LeafProofs.L17GaussianSumEquation
import Yau.LeafProofs.L17GaussianParametrix

/-! The actual operator P Q - id has the proved small Gaussian residual norm. -/

open Set Metric
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17Aux

open Yau.Parabolic L17HolderAux L17SchauderAux L17SourceLocalizationAux L17ParabolicOperatorAux

variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}

theorem exists_uniform_gaussian_operator_residual_budget (A : BoundedChartFamily g) (hg : MetricSmooth g)
    (N : ℕ) (γ : ℝ) (hγ : 0 < γ) (hγ1 : γ < 1) :
    ∃ L : ℝ, 0 < L ∧ ∀ (P : UniformChartPartition g), P.charts=A → P.overlapBudget ≤ N →
      ∀ (hr : P.radius ≤ 1), 2*P.radius < A.radius → ∀ (T : ℝ) (hT : 0 < T) (hSmall : T ≤ P.radius^2),
      ∀ (Cs R : ℝ), 0 ≤ R → ∀ Q : HolderSpace P T γ →L[ℝ] SchauderSpace P T γ hT,
      (∀ f,schauderFun (Q f)=gaussianParametrixFun P T hT.le f) →
      (∀ (f : HolderSpace P T γ) (p : P.centers), HolderBound γ Set.univ (rescaledSource P T hT.le f p) (Cs*‖f‖)) →
      (∀ (f : HolderSpace P T γ) (p : P.centers),
        HolderBound γ (cylinder (ball (0 : Space n) 2) 0 (T/P.radius^2))
          (unitGaussianResidual P T hT.le f p)
          (R*‖f‖*(P.radius+(T/P.radius^2)^(1/2 : ℝ)+(T/P.radius^2)^((1-γ)/2)))) →
      ‖(scalarParabolicCLM P T γ hT hSmall hγ1.le hr).comp Q-
        ContinuousLinearMap.id ℝ (HolderSpace P T γ)‖ ≤
        (L*R)*(P.radius+(T/P.radius^2)^(1/2 : ℝ)+(T/P.radius^2)^((1-γ)/2)) := by
  obtain ⟨L,hL,hRaw⟩ := exists_uniform_gaussian_residual_holder_budget A hg N γ hγ
  refine ⟨L,hL,?_⟩
  intro P hA hN hr hρA T hT hSmall Cs R hR Q hValue hSource hUnit
  let E : HolderSpace P T γ →L[ℝ] HolderSpace P T γ :=
    (scalarParabolicCLM P T γ hT hSmall hγ1.le hr).comp Q-ContinuousLinearMap.id ℝ (HolderSpace P T γ)
  let s := P.radius+(T/P.radius^2)^(1/2 : ℝ)+(T/P.radius^2)^((1-γ)/2)
  have hs : 0 ≤ s := by
    dsimp only [s]
    exact add_nonneg (add_nonneg P.radius_pos.le (Real.rpow_nonneg (by positivity) _))
      (Real.rpow_nonneg (by positivity) _)
  apply E.opNorm_le_bound (mul_nonneg (mul_nonneg hL.le hR) hs)
  intro f
  have hC : 0 ≤ R*‖f‖*s := mul_nonneg (mul_nonneg hR (norm_nonneg f)) hs
  obtain ⟨e,⟨heValue,heNorm⟩,_⟩ := hRaw P hA hN hr hρA T hT.le (R*‖f‖*s) hC f (hUnit f)
  have hEq : E f=e := by
    apply holderFun_injective P T γ
    funext q
    exact (gaussian_operator_residual_value P T hT hSmall hr (by simpa only [hA] using hρA)
      hγ hγ1 Q hValue f (hSource f) q).trans (congrFun heValue q).symm
  rw [hEq]
  simpa only [mul_assoc,mul_left_comm,mul_comm] using heNorm

theorem BoundedChartFamily.exists_uniform_approximate_scalar_inverse
    (A : BoundedChartFamily g) (hg : MetricSmooth g) :
    ∃ D E : Ioo (0 : ℝ) 1 → ℝ, (∀ γ,0 < D γ) ∧ (∀ γ,0 < E γ) ∧
      ∀ ε : ℝ, 0 < ε → ∃ P : UniformChartPartition g,
        P.charts=A ∧ P.radius<ε ∧ P.radius≤1 ∧ 2*P.radius<A.radius ∧
        ∀ (T : ℝ) (hT : 0 < T) (hSmall : T ≤ P.radius^2) (hr : P.radius≤1), ∀ γ : Ioo (0 : ℝ) 1,
          ∃ Q : HolderSpace P T γ.val →L[ℝ] SchauderSpace P T γ.val hT,
            (∀ f,schauderFun (Q f)=gaussianParametrixFun P T hT.le f) ∧ ‖Q‖ ≤ D γ ∧
            ‖(scalarParabolicCLM P T γ.val hT hSmall γ.property.2.le hr).comp Q-
              ContinuousLinearMap.id ℝ (HolderSpace P T γ.val)‖ ≤
              E γ*(P.radius+(T/P.radius^2)^(1/2 : ℝ)+(T/P.radius^2)^((1-γ.val)/2)) := by
  obtain ⟨N,B,C,K,R,D,hB,hC,hK,hR,hD,hPart⟩ := A.exists_uniform_gaussian_parametrix hg
  choose L hL hBudget using fun γ : Ioo (0 : ℝ) 1 =>
    exists_uniform_gaussian_operator_residual_budget A hg N γ.val γ.property.1 γ.property.2
  refine ⟨D,fun γ => L γ*R γ,hD,fun γ => mul_pos (hL γ) (hR γ),?_⟩
  intro ε hε
  obtain ⟨P,hA,hρε,hr,hρA,hN,hJets,hAll⟩ := hPart ε hε
  refine ⟨P,hA,hρε,hr,hρA,?_⟩
  intro T hT hSmall hr' γ
  obtain ⟨hKernel,Q,hValue,hNorm⟩ := hAll T hT hSmall γ
  refine ⟨Q,hValue,hNorm,?_⟩
  apply hBudget γ P hA hN.le hr' hρA T hT hSmall C (R γ) (hR γ).le Q hValue
  · intro f p
    exact (hKernel f p).1
  · intro f p
    simpa only [add_assoc] using (hKernel f p).2.2.2.2

end Yau.LeafProofs.L17Aux
