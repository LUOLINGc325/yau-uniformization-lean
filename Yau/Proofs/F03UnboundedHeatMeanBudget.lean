import Yau.Proofs.F03HeatMeanBudget
import Yau.Proofs.F03GaussianLinearBudget

/-! The original supplied linear ball means control actual unbounded same-kernel heat at the matching scale. -/
noncomputable section
open MeasureTheory Set
namespace Yau.Proofs.F03Aux
open Yau Blueprint HeatConcreteBindings HeatTargetCandidates LeafProofs.L18Aux
variable {n : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem dirichletMinimalKernel_linear_ball_mean_bound
    (X : KahlerManifold n) (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hf : LocalizedFlow X o h U P ρ) (C₀ : ℝ) (hC₀ : 0 ≤ C₀) :
    ∃ C : ℝ,0 < C ∧
      ∀ (μ : Measure (Pt X)) (hμ : IsRiemannianVolume X.metric.form μ)
        (O : ℕ → Set (Pt X)) (hO : SmoothExhaustion O)
        (f : Pt X → ℝ),Measurable f → (∀ y,0 ≤ f y) →
      ∀ A : ℝ,0 ≤ A →
      (∀ R : ℝ,1 ≤ R → BallIntegralLE X.metric.form μ o f R (A*R)) →
      ∀ L : ℝ,1 ≤ L → ∀ x,inducedDistance X.metric.form o x ≤ C₀*L →
      Integrable (fun y => dirichletMinimalKernelCandidate X.metric X.kahler_metric μ hμ O hO (L^2) x y*f y) μ ∧
      (∫ y,dirichletMinimalKernelCandidate X.metric X.kahler_metric μ hμ O hO (L^2) x y*f y ∂μ) ≤ C*A*L := by
  obtain ⟨K,c,hK,hc,hKernel⟩ := dirichletMinimalKernelCandidate_coarse_gaussian X o h U P ρ hf C₀ hC₀
  obtain ⟨J,hJ,hBudget⟩ := exists_gaussian_linear_mean_budget X.metric X.complete_metric X.kahler_metric
    (F02Aux.initialRicci_posSemidef X o h U P ρ hf) hc
  let D := C₀+1
  have hD : 1 ≤ D := by dsimp [D];linarith
  refine ⟨K*J*D,by positivity,fun μ hμ O hO f hfMeas hf0 A hA hMean L hL x hx => ?_⟩
  let R := D*L
  let V := (μ (distBall X.metric.form o R)).toReal
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hR1 : 1 ≤ R := by dsimp [R];nlinarith
  have hR0 : 0 < R := zero_lt_one.trans_le hR1
  have hV : 0 < V := ENNReal.toReal_pos
    (riemannianVolume_distBall_pos X.metric μ hμ o hR0).ne'
    (riemannianVolume_distBall_lt_top X.metric μ hμ o hR0).ne
  have hSqrt : Real.sqrt (L^2)=L := Real.sqrt_sq hL0.le
  have hKBound (y : Pt X) :
      dirichletMinimalKernelCandidate X.metric X.kahler_metric μ hμ O hO (L^2) x y ≤
        (K/V)*Real.exp (-c*(inducedDistance X.metric.form o y/R)^2) := by
    have hh := hKernel μ hμ O hO L hL (L^2) (sq_pos_of_pos hL0) le_rfl x hx y
    rw [hSqrt,div_self hL0.ne',one_pow,mul_one] at hh
    convert hh using 1 <;> dsimp [R,D,V] <;> ring
  have hGauss := gaussian_linear_mean_integrable X.metric X.complete_metric X.kahler_metric
    (F02Aux.initialRicci_posSemidef X o h U P ρ hf) μ hμ o f hfMeas hf0 hA hMean hc hR1
  have hInt : Integrable (fun y => dirichletMinimalKernelCandidate X.metric X.kahler_metric μ hμ O hO (L^2) x y*f y) μ := by
    apply (hGauss.const_mul (K/V)).mono'
      ((kernelSmooth_univ_continuous_right _
        (dirichletMinimalKernelCandidate_joint_smooth X.metric X.kahler_metric μ hμ O hO)
        (sq_pos_of_pos hL0) x).aestronglyMeasurable.mul hfMeas.aestronglyMeasurable)
    apply ae_of_all μ
    intro y
    change |dirichletMinimalKernelCandidate X.metric X.kahler_metric μ hμ O hO (L^2) x y*f y| ≤ _
    rw [abs_of_nonneg (mul_nonneg
      (dirichletMinimalKernelCandidate_nonneg X.metric X.kahler_metric μ hμ O hO (sq_pos_of_pos hL0) x y) (hf0 y))]
    convert mul_le_mul_of_nonneg_right (hKBound y) (hf0 y) using 1 <;> ring
  refine ⟨hInt,?_⟩
  have hIntegral := integral_le_of_gaussian_lintegral_budget μ
    (fun y => dirichletMinimalKernelCandidate X.metric X.kahler_metric μ hμ O hO (L^2) x y*f y)
    (fun y => Real.exp (-c*(inducedDistance X.metric.form o y/R)^2)*f y) hInt
    (fun y => mul_nonneg (dirichletMinimalKernelCandidate_nonneg X.metric X.kahler_metric μ hμ O hO
      (sq_pos_of_pos hL0) x y) (hf0 y))
    (K := K/V) (B := J*A*R*V) (by positivity) (by positivity)
    (fun y => by convert mul_le_mul_of_nonneg_right (hKBound y) (hf0 y) using 1 <;> ring)
    (hBudget μ hμ o f hfMeas A hA hMean R hR1)
  calc
    _ ≤ (K/V)*(J*A*R*V) := hIntegral
    _ = _ := by dsimp [R];field_simp <;> ring

end Yau.Proofs.F03Aux
