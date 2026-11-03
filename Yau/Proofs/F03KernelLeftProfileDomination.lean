import Yau.Proofs.F03KernelLeftGradientGaussian
import Yau.Proofs.F03TerminalEnvelopeGaussian

/-! One actual integrable envelope controls the left kernel differential on every fixed bounded spatial region. -/
noncomputable section
open MeasureTheory Set
namespace Yau.Proofs.F03Aux
open Yau Blueprint HeatConcreteBindings HeatTargetCandidates LeafProofs.L18Aux
variable {n : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem dirichletMinimalKernel_left_profile_domination
    (X : KahlerManifold n) (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hf : LocalizedFlow X o h U P ρ) {T : ℝ} (hT : 0 ≤ T)
    (μ : Measure (Pt X)) (hμ : IsRiemannianVolume X.metric.form μ)
    (O : ℕ → Set (Pt X)) (hO : SmoothExhaustion O) {b : ℝ} (hb : 0 < b)
    (C₀ : ℝ) (hC₀ : 0 ≤ C₀) {L : ℝ} (hL : 1 ≤ L) (hbL : b ≤ L^2) :
    ∃ E : Pt X → ℝ,Integrable E μ ∧ (∀ y,0 ≤ E y) ∧
      ∀ x,inducedDistance X.metric.form o x ≤ C₀*L → ∀ y,
      dirichletMinimalKernelCandidate X.metric X.kahler_metric μ hμ O hO b x y ≤ E y ∧
      Real.sqrt (gradNormSq X.metric.form (fun z =>
        dirichletMinimalKernelCandidate X.metric X.kahler_metric μ hμ O hO b z y) x) ≤ E y ∧
      dirichletMinimalKernelCandidate X.metric X.kahler_metric μ hμ O hO b x y*ρ y T ≤ E y ∧
      Real.sqrt (gradNormSq X.metric.form (fun z =>
        dirichletMinimalKernelCandidate X.metric X.kahler_metric μ hμ O hO b z y) x)*ρ y T ≤ E y := by
  obtain ⟨K,c₀,hK,hc₀,hKernel⟩ := dirichletMinimalKernelCandidate_coarse_gaussian X o h U P ρ hf C₀ hC₀
  obtain ⟨G,c₁,hG,hc₁,hGradient⟩ := dirichletMinimalKernelCandidate_left_gradient_coarse_gaussian X o h U P ρ hf C₀ hC₀
  let R := (C₀+1)*L
  have hR : 1 ≤ R := by dsimp [R];nlinarith
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  let V := (μ (distBall X.metric.form o R)).toReal
  have hV : 0 < V := ENNReal.toReal_pos
    (riemannianVolume_distBall_pos X.metric μ hμ o hR0).ne'
    (riemannianVolume_distBall_lt_top X.metric μ hμ o hR0).ne
  let Q := (L/Real.sqrt b)^(2*n)
  have hQ : 0 ≤ Q := by dsimp [Q];positivity
  let C := (K+G/Real.sqrt b)*Q/V
  have hC : 0 ≤ C := by dsimp [C];positivity
  let q : Pt X → ℝ := fun y => C*Real.exp (-(min c₀ c₁)*(inducedDistance X.metric.form o y/R)^2)
  let E : Pt X → ℝ := fun y => q y*(1+ρ y T)
  have hρ : ∀ y,0 ≤ ρ y T := fun y => (hf.2.2.2.2.2.2.2.2.2.1 y T hT).2
  have hq : ∀ y,0 ≤ q y := fun _ => mul_nonneg hC (Real.exp_pos _).le
  have hInt : Integrable E μ := by
    convert (localizedFlow_terminal_envelope_gaussian_integrable X o h U P ρ hf hT μ hμ
      (lt_min hc₀ hc₁) hR).const_mul C using 1
    funext y
    change (C*Real.exp (-(min c₀ c₁)*(inducedDistance X.metric.form o y/R)^2))*(1+ρ y T)=
      C*(Real.exp (-(min c₀ c₁)*(inducedDistance X.metric.form o y/R)^2)*(1+ρ y T))
    ring
  refine ⟨E,hInt,fun y => mul_nonneg (hq y) (by linarith [hρ y]),?_⟩
  intro x hx y
  have hExp (c : ℝ) (hc : min c₀ c₁ ≤ c) :
      Real.exp (-c*(inducedDistance X.metric.form o y/R)^2) ≤
        Real.exp (-(min c₀ c₁)*(inducedDistance X.metric.form o y/R)^2) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr hc) (sq_nonneg (inducedDistance X.metric.form o y/R))]
  have hCoefK : K*Q/V ≤ C := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (by positivity)) hQ) hV.le
  have hCoefG : (G/Real.sqrt b)*Q/V ≤ C := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hK.le) hQ) hV.le
  have hKernelQ : dirichletMinimalKernelCandidate X.metric X.kahler_metric μ hμ O hO b x y ≤ q y := by
    calc
      _ ≤ K*Q*Real.exp (-c₀*(inducedDistance X.metric.form o y/R)^2)/V :=
        hKernel μ hμ O hO L hL b hb hbL x hx y
      _ = (K*Q/V)*Real.exp (-c₀*(inducedDistance X.metric.form o y/R)^2) := by ring
      _ ≤ q y := mul_le_mul hCoefK (hExp c₀ (min_le_left _ _)) (by positivity) hC
  have hGradientQ : Real.sqrt (gradNormSq X.metric.form (fun z =>
      dirichletMinimalKernelCandidate X.metric X.kahler_metric μ hμ O hO b z y) x) ≤ q y := by
    calc
      _ ≤ (G/Real.sqrt b)*Q*Real.exp (-c₁*(inducedDistance X.metric.form o y/R)^2)/V :=
        hGradient μ hμ O hO L hL b hb hbL x hx y
      _ = ((G/Real.sqrt b)*Q/V)*Real.exp (-c₁*(inducedDistance X.metric.form o y/R)^2) := by ring
      _ ≤ q y := mul_le_mul hCoefG (hExp c₁ (min_le_right _ _)) (by positivity) hC
  have hqE : q y ≤ E y := by dsimp [E];nlinarith [mul_nonneg (hq y) (hρ y)]
  have hqρE : q y*ρ y T ≤ E y := by dsimp [E];nlinarith [hq y]
  exact ⟨hKernelQ.trans hqE,hGradientQ.trans hqE,
    (mul_le_mul_of_nonneg_right hKernelQ (hρ y)).trans hqρE,
    (mul_le_mul_of_nonneg_right hGradientQ (hρ y)).trans hqρE⟩

end Yau.Proofs.F03Aux
