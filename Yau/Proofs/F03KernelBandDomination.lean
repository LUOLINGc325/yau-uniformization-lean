import Yau.Proofs.F03KernelBandEnvelope

/-! The supplied flow density gives the actual common integrable positive-band majorant. -/
noncomputable section
open MeasureTheory Set
namespace Yau.Proofs.F03Aux
open Yau Blueprint HeatConcreteBindings HeatTargetCandidates
variable {n : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem dirichletMinimalKernel_positive_band_domination
    (X : KahlerManifold n) (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hf : LocalizedFlow X o h U P ρ) {T : ℝ} (hT : 0 ≤ T)
    (μ : Measure (Pt X)) (hμ : IsRiemannianVolume X.metric.form μ)
    (O : ℕ → Set (Pt X)) (hO : SmoothExhaustion O)
    {ε B : ℝ} (hε : 0 < ε) (hεB : ε ≤ B) (x : Pt X) :
    ∃ E : Pt X → ℝ,Integrable E μ ∧ (∀ y,0 ≤ E y) ∧
      ∀ b ∈ Icc ε B,∀ y,
      dirichletMinimalKernelCandidate X.metric X.kahler_metric μ hμ O hO b x y ≤ E y ∧
      Real.sqrt (gradNormSq X.metric.form (fun z =>
        dirichletMinimalKernelCandidate X.metric X.kahler_metric μ hμ O hO b x z) y) ≤ E y ∧
      dirichletMinimalKernelCandidate X.metric X.kahler_metric μ hμ O hO b x y*ρ y T ≤ E y ∧
      Real.sqrt (gradNormSq X.metric.form (fun z =>
        dirichletMinimalKernelCandidate X.metric X.kahler_metric μ hμ O hO b x z) y)*ρ y T ≤ E y := by
  obtain ⟨C,c,R,hC,hc,hR,hBound⟩ := dirichletMinimalKernel_positive_band_gaussian
    X o h U P ρ hf μ hμ O hO hε hεB x
  let q : Pt X → ℝ := fun y => C*Real.exp (-c*(inducedDistance X.metric.form o y/R)^2)
  let E : Pt X → ℝ := fun y => q y*(1+ρ y T)
  have hρ : ∀ y,0 ≤ ρ y T := fun y => (hf.2.2.2.2.2.2.2.2.2.1 y T hT).2
  have hq : ∀ y,0 ≤ q y := fun _ => by dsimp [q];positivity
  have hInt : Integrable E μ := by
    convert (localizedFlow_terminal_envelope_gaussian_integrable X o h U P ρ hf hT μ hμ hc hR).const_mul C using 1
    funext y
    change (C*Real.exp (-c*(inducedDistance X.metric.form o y/R)^2))*(1+ρ y T)=
      C*(Real.exp (-c*(inducedDistance X.metric.form o y/R)^2)*(1+ρ y T))
    ring
  refine ⟨E,hInt,fun y => mul_nonneg (hq y) (by linarith [hρ y]),?_⟩
  intro b hb y
  have hK := (hBound b hb y).1
  have hG := (hBound b hb y).2
  have hEq : q y ≤ E y := by dsimp [E];nlinarith [mul_nonneg (hq y) (hρ y)]
  have hρEq : q y*ρ y T ≤ E y := by dsimp [E];nlinarith [hq y]
  exact ⟨hK.trans hEq,hG.trans hEq,
    (mul_le_mul_of_nonneg_right hK (hρ y)).trans hρEq,
    (mul_le_mul_of_nonneg_right hG (hρ y)).trans hρEq⟩

end Yau.Proofs.F03Aux
